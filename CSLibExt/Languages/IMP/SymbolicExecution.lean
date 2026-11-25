/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bounded symbolic execution for IMP
-/
module

public import CSLibExt.Languages.IMP.ConstantFolding

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Bounded symbolic execution for IMP

Dynamically bounded path enumeration with checked pruning.
-/

@[expose] public section

namespace Cslib.IMP

namespace AExp

/-- Substitute a symbolic store into an arithmetic expr. -/
def subst (σ : Nat → AExp) : AExp → AExp
  | .const v => .const v
  | .var x => σ x
  | .add l r => .add (subst σ l) (subst σ r)
  | .sub l r => .sub (subst σ l) (subst σ r)
  | .mul l r => .mul (subst σ l) (subst σ r)

theorem eval_subst (σ : Nat → AExp) (a : AExp)
    (s : State) :
    (subst σ a).eval s = a.eval (fun x => (σ x).eval s) := by
  induction a with
  | const => rfl
  | var => rfl
  | add l r ihl ihr => simp [subst, eval, ihl, ihr]
  | sub l r ihl ihr => simp [subst, eval, ihl, ihr]
  | mul l r ihl ihr => simp [subst, eval, ihl, ihr]

end AExp

namespace BExp

/-- Substitute a symbolic store into a boolean expr. -/
def subst (σ : Nat → AExp) : BExp → BExp
  | .truth v => .truth v
  | .eq l r => .eq (AExp.subst σ l) (AExp.subst σ r)
  | .le l r => .le (AExp.subst σ l) (AExp.subst σ r)
  | .not b => .not (subst σ b)
  | .and l r => .and (subst σ l) (subst σ r)

theorem eval_subst (σ : Nat → AExp) (b : BExp)
    (s : State) :
    (subst σ b).eval s = b.eval (fun x => (σ x).eval s) := by
  induction b with
  | truth => rfl
  | eq l r => simp [subst, eval, AExp.eval_subst]
  | le l r => simp [subst, eval, AExp.eval_subst]
  | not b ih => simp [subst, eval, ih]
  | and l r ihl ihr => simp [subst, eval, ihl, ihr]

end BExp

/-- Counted big-step executions with while-body entries. -/
inductive BigStepCost : Cmd → State → State → Nat → Prop
  | skip (s : State) : BigStepCost .skip s s 0
  | assign (s : State) (x : Nat) (a : AExp) :
      BigStepCost (.assign x a) s
        (Function.update s x (a.eval s)) 0
  | seq {c1 c2 : Cmd} {s m f : State} {n1 n2 : Nat}
      (h1 : BigStepCost c1 s m n1)
      (h2 : BigStepCost c2 m f n2) :
      BigStepCost (.seq c1 c2) s f (n1 + n2)
  | iteTrue {g : BExp} {c1 c2 : Cmd} {s f : State}
      {n : Nat} (hg : g.eval s = true)
      (h : BigStepCost c1 s f n) :
      BigStepCost (.ite g c1 c2) s f n
  | iteFalse {g : BExp} {c1 c2 : Cmd} {s f : State}
      {n : Nat} (hg : g.eval s = false)
      (h : BigStepCost c2 s f n) :
      BigStepCost (.ite g c1 c2) s f n
  | whileFalse {g : BExp} {b : Cmd} {s : State}
      (hg : g.eval s = false) :
      BigStepCost (.while g b) s s 0
  | whileTrue {g : BExp} {b : Cmd} {s m f : State}
      {n1 n2 : Nat} (hg : g.eval s = true)
      (hb : BigStepCost b s m n1)
      (hr : BigStepCost (.while g b) m f n2) :
      BigStepCost (.while g b) s f (1 + n1 + n2)

theorem bigStepCost_erase (c : Cmd) (s f : State) :
    (∃ n, BigStepCost c s f n) ↔ BigStep c s f := by
  constructor
  · rintro ⟨n, h⟩
    induction h with
    | skip => exact .skip _
    | assign => exact .assign _ _ _
    | seq h1 h2 ih1 ih2 => exact .seq ih1 ih2
    | iteTrue hg h ih => exact .iteTrue hg ih
    | iteFalse hg h ih => exact .iteFalse hg ih
    | whileFalse hg => exact .whileFalse hg
    | whileTrue hg hb hr ihb ihr =>
        exact .whileTrue hg ihb ihr
  · intro h
    induction h with
    | skip => exact ⟨0, .skip _⟩
    | assign => exact ⟨0, .assign _ _ _⟩
    | seq h1 h2 ih1 ih2 =>
        obtain ⟨n1, h1⟩ := ih1
        obtain ⟨n2, h2⟩ := ih2
        exact ⟨n1 + n2, .seq h1 h2⟩
    | iteTrue hg h ih =>
        obtain ⟨n, h⟩ := ih
        exact ⟨n, .iteTrue hg h⟩
    | iteFalse hg h ih =>
        obtain ⟨n, h⟩ := ih
        exact ⟨n, .iteFalse hg h⟩
    | whileFalse hg => exact ⟨0, .whileFalse hg⟩
    | whileTrue hg hb hr ihb ihr =>
        obtain ⟨n1, hb⟩ := ihb
        obtain ⟨n2, hr⟩ := ihr
        exact ⟨1 + n1 + n2, .whileTrue hg hb hr⟩

namespace Symbolic

/-- Symbolic store mapping vars to terms over init state. -/
abbrev Store := Nat → AExp

namespace Store

/-- Initial store mapping each var to itself. -/
def init : Store := fun x => .var x

/-- Evaluate a store at an initial state to get a state. -/
def eval (σ : Store) (s : State) : State :=
  fun x => (σ x).eval s

theorem eval_init (s : State) : eval init s = s := rfl

theorem eval_update (σ : Store) (x : Nat) (e : AExp)
    (s : State) :
    eval (Function.update σ x e) s =
      Function.update (eval σ s) x (e.eval s) := by
  funext y
  by_cases hy : y = x
  · subst hy
    simp [eval, Function.update]
  · simp [eval, Function.update, hy]

end Store

/-- Embed a constant table as a symbolic store. -/
def tableStore (t : ConstTable) : Store :=
  fun x => match t x with
    | some n => .const n
    | none => .var x

theorem afold_eq_subst (t : ConstTable) (a : AExp) :
    afold t a =
      afold emptyTable (AExp.subst (tableStore t) a) := by
  induction a with
  | const => rfl
  | var x =>
      simp only [AExp.subst, tableStore]
      cases ht : t x
      · simp [ht, afold, emptyTable]
      · simp [ht, afold]
  | add l r ihl ihr =>
      simp [AExp.subst, afold, ihl, ihr]
  | sub l r ihl ihr =>
      simp [AExp.subst, afold, ihl, ihr]
  | mul l r ihl ihr =>
      simp [AExp.subst, afold, ihl, ihr]

theorem bfold_eq_subst (t : ConstTable) (b : BExp) :
    bfold t b =
      bfold emptyTable (BExp.subst (tableStore t) b) := by
  induction b with
  | truth => rfl
  | eq l r =>
      have h1 := afold_eq_subst t l
      have h2 := afold_eq_subst t r
      simp [BExp.subst, bfold, h1, h2]
  | le l r =>
      have h1 := afold_eq_subst t l
      have h2 := afold_eq_subst t r
      simp [BExp.subst, bfold, h1, h2]
  | not b ih =>
      simp [BExp.subst, bfold, ih]
  | and l r ihl ihr =>
      simp [BExp.subst, bfold, ihl, ihr]

theorem constApprox_iff (t : ConstTable) (s : State) :
    ConstApprox t s ↔
      Store.eval (tableStore t) s = s := by
  constructor
  · intro h
    funext x
    simp only [Store.eval, tableStore]
    cases ht : t x
    · simp
    · have hs := h x _ ht
      simp [hs]
  · intro h x n ht
    have hx := congrFun h x
    simp [Store.eval, tableStore, ht] at hx
    exact hx.symm

/-- Symbolic path with guard, store and cost. -/
structure Path where
  guard : BExp
  store : Store
  cost : Nat

namespace Path

/-- Initial path with true guard and zero cost. -/
def init : Path :=
  { guard := .truth true, store := Store.init, cost := 0 }

/-- Symbolic assignment updating the store with folding. -/
def assign (x : Nat) (a : AExp) (p : Path) : Path :=
  { p with store := (Function.update p.store x
      (afold emptyTable (AExp.subst p.store a))) }

/-- Assume a condition, pruning only on literal false. -/
def assume (b : BExp) (p : Path) : Option Path :=
  let b' := bfold emptyTable (BExp.subst p.store b)
  if b' = .truth false then none
  else some { p with guard := .and p.guard b' }

/-- Increment the path cost by one. -/
def tick (p : Path) : Path :=
  { p with cost := p.cost + 1 }

theorem assume_eq_none {b : BExp} {p : Path}
    (h : Path.assume b p = none) (s : State) :
    BExp.eval b (Store.eval p.store s) = false := by
  simp only [Path.assume] at h
  by_cases hb : bfold emptyTable (BExp.subst p.store b) =
      .truth false
  · have hfold := bfold_eval emptyTable
      (BExp.subst p.store b) s (emptyTable_approx s)
    have hsubst := BExp.eval_subst p.store b s
    have heval : (bfold emptyTable
        (BExp.subst p.store b)).eval s = false := by
      rw [hb]
      rfl
    rw [heval] at hfold
    rw [hsubst] at hfold
    exact hfold.symm
  · simp [hb] at h

end Path

/-- Execution leaf, terminal or budget-exhausted cutoff. -/
inductive Leaf where
  | done (path : Path)
  | cut (path : Path)

namespace Leaf

/-- Bind a continuation over terminal leaves only. -/
def bind (h : Path → List Leaf) : Leaf → List Leaf
  | .done q => h q
  | .cut q => [.cut q]

/-- Project terminal leaves to paths. -/
def done? : Leaf → Option Path
  | .done p => some p
  | .cut _ => none

/-- Project cutoff leaves to paths. -/
def cut? : Leaf → Option Path
  | .cut p => some p
  | .done _ => none

end Leaf

/-- Bounded loop unrolling with fuel as termination cert. -/
def loop (k : Nat) (g : BExp) (body : Path → List Leaf) :
    Nat → Path → List Leaf
  | 0, p =>
      (match Path.assume (.not g) p with
        | none => []
        | some q => [Leaf.done q]) ++
      (match Path.assume g p with
        | none => []
        | some q => [Leaf.cut q])
  | Nat.succ f, p =>
      (match Path.assume (.not g) p with
        | none => []
        | some q => [Leaf.done q]) ++
      (match Path.assume g p with
        | none => []
        | some q =>
            if p.cost < k then
              (body (Path.tick q)).flatMap
                (Leaf.bind (fun r => loop k g body f r))
            else [Leaf.cut q])

/-- Symbolically execute a command with bound k. -/
def run (k : Nat) : Cmd → Path → List Leaf
  | .skip, p => [Leaf.done p]
  | .assign x a, p => [Leaf.done (Path.assign x a p)]
  | .seq c1 c2, p =>
      (run k c1 p).flatMap
        (Leaf.bind (fun q => run k c2 q))
  | .ite g c1 c2, p =>
      (match Path.assume g p with
        | none => []
        | some q => run k c1 q) ++
      (match Path.assume (.not g) p with
        | none => []
        | some q => run k c2 q)
  | Cmd.«while» g b, p =>
      loop k g (fun q => run k b q) (k - p.cost) p

/-- All leaves from the initial path. -/
def leaves (k : Nat) (c : Cmd) : List Leaf :=
  run k c Path.init

/-- Terminal paths in order. -/
def paths (k : Nat) (c : Cmd) : List Path :=
  (leaves k c).filterMap Leaf.done?

/-- Cutoff paths in order. -/
def cutoffs (k : Nat) (c : Cmd) : List Path :=
  (leaves k c).filterMap Leaf.cut?

private theorem afold_empty_eval (a : AExp) (s : State) :
    (afold emptyTable a).eval s = a.eval s :=
  afold_eval emptyTable a s (emptyTable_approx s)

private theorem bfold_empty_eval (b : BExp) (s : State) :
    (bfold emptyTable b).eval s = b.eval s :=
  bfold_eval emptyTable b s (emptyTable_approx s)

private theorem assign_store (x : Nat) (a : AExp)
    (p : Path) (s0 : State) :
    Store.eval (Path.assign x a p).store s0 =
      Function.update (Store.eval p.store s0) x
        (a.eval (Store.eval p.store s0)) := by
  have hs : (Path.assign x a p).store =
      Function.update p.store x
        (afold emptyTable (AExp.subst p.store a)) := rfl
  rw [hs, Store.eval_update]
  have he : (afold emptyTable (AExp.subst p.store a)).eval s0 =
      a.eval (Store.eval p.store s0) := by
    rw [afold_empty_eval]
    exact AExp.eval_subst _ _ _
  rw [he]

private theorem assume_some (b : BExp) (p q : Path)
    (s0 : State) (h : Path.assume b p = some q) :
    q.store = p.store ∧ q.cost = p.cost ∧
      q.guard.eval s0 = (p.guard.eval s0 &&
        BExp.eval b (Store.eval p.store s0)) := by
  simp only [Path.assume] at h
  by_cases hb : bfold emptyTable (BExp.subst p.store b) =
      .truth false
  · simp only [ite_eq_left hb] at h
    cases h
  · simp only [ite_eq_right hb] at h
    have hq : ({ p with guard := (.and p.guard
      (bfold emptyTable (BExp.subst p.store b))) } : Path)
      = q := by cases h; rfl
    subst hq
    refine ⟨rfl, rfl, ?_⟩
    change (BExp.and p.guard _).eval s0 = _
    change (p.guard.eval s0 && _) = _
    rw [bfold_empty_eval, BExp.eval_subst]
    rfl

private theorem assume_some_of_true (b : BExp) (p : Path)
    (s0 : State) (hg : p.guard.eval s0 = true)
    (hc : BExp.eval b (Store.eval p.store s0) = true) :
    ∃ q, Path.assume b p = some q ∧
      q.guard.eval s0 = true := by
  have hbe : (bfold emptyTable
      (BExp.subst p.store b)).eval s0 = true := by
    rw [bfold_empty_eval, BExp.eval_subst]
    exact hc
  have hne : bfold emptyTable (BExp.subst p.store b) ≠
      .truth false := by
    intro hc2
    have hf : (bfold emptyTable
        (BExp.subst p.store b)).eval s0 = false := by
      rw [hc2]
      rfl
    rw [hbe] at hf
    cases hf
  refine ⟨{ p with guard := (.and p.guard
    (bfold emptyTable (BExp.subst p.store b))) }, ?_, ?_⟩
  · simp [Path.assume, hne]
  · change (BExp.and _ _).eval s0 = true
    change (_ && _) = true
    rw [hg, hbe]
    rfl

private theorem loop_mono (k : Nat) (g : BExp)
    (body : Path → List Leaf) (f1 f2 : Nat)
    (p q : Path) (hle : f1 ≤ f2)
    (hm : Leaf.done q ∈ loop k g body f1 p) :
    Leaf.done q ∈ loop k g body f2 p := by
  induction f1 generalizing f2 p q with
  | zero =>
      cases f2 with
      | zero => exact hm
      | succ f2 =>
          cases hx : Path.assume (.not g) p
          · cases he : Path.assume g p
            · simp [loop, hx, he] at hm
            · simp [loop, hx, he] at hm
          · cases he : Path.assume g p
            · simp only [loop, hx, he, List.append_nil, List.mem_singleton,
                Leaf.done.injEq] at hm ⊢
              exact hm
            · simp only [loop, hx, he, List.mem_append, List.mem_singleton,
                Leaf.done.injEq] at hm ⊢
              cases hm with
              | inl h => exact Or.inl h
              | inr h => exact Leaf.noConfusion h
  | succ f1 ih =>
      cases f2 with
      | zero =>
          have hfalse : False := by omega
          cases hfalse
      | succ f2 =>
          have hle2 : f1 ≤ f2 := by omega
          cases hx : Path.assume (.not g) p
          · cases he : Path.assume g p
            · simp [loop, hx, he] at hm ⊢
            · rename_i q0
              by_cases hc : p.cost < k
              · simp only [loop, hx, he, ite_eq_left hc, List.nil_append,
                  List.mem_flatMap] at hm ⊢
                have hm' : ∃ m, m ∈ body (Path.tick q0) ∧
                    Leaf.done q ∈
                      Leaf.bind (fun r => loop k g body f1 r) m := by
                  exact hm
                obtain ⟨m, hml, hqm⟩ := hm'
                cases m with
                | done r =>
                    simp only [Leaf.bind] at hqm
                    have hqm2 := ih _ _ _ hle2 hqm
                    have hbind : Leaf.done q ∈
                        Leaf.bind (fun r => loop k g body f2 r)
                          (Leaf.done r) := by
                      simp only [Leaf.bind]
                      exact hqm2
                    exact ⟨_, hml, hbind⟩
                | cut r =>
                    simp [Leaf.bind] at hqm
              · simp [loop, hx, he, hc] at hm ⊢
          · cases he : Path.assume g p
            · simp only [loop, hx, he, List.append_nil, List.mem_singleton,
                Leaf.done.injEq] at hm ⊢
              exact hm
            · rename_i q0
              by_cases hc : p.cost < k
              · simp only [loop, hx, he, ite_eq_left hc, List.mem_append,
                  List.mem_singleton, Leaf.done.injEq,
                  List.mem_flatMap] at hm ⊢
                cases hm with
                | inl h => exact Or.inl h
                | inr h =>
                    obtain ⟨m, hml, hqm⟩ := h
                    cases m with
                    | done r =>
                        simp only [Leaf.bind] at hqm
                        have hqm2 := ih _ _ _ hle2 hqm
                        have hbind : Leaf.done q ∈
                            Leaf.bind (fun r => loop k g body f2 r)
                              (Leaf.done r) := by
                          simp only [Leaf.bind]
                          exact hqm2
                        exact Or.inr ⟨_, hml, hbind⟩
                    | cut r =>
                        simp [Leaf.bind] at hqm
              · simp only [loop, hx, he, ite_eq_right hc, List.mem_append,
                  List.mem_singleton, Leaf.done.injEq] at hm ⊢
                cases hm with
                | inl h => exact Or.inl h
                | inr h => exact Leaf.noConfusion h

private theorem loop_exit_sound (g : BExp) (b : Cmd)
    (p q : Path) (s0 : State)
    (hx : Path.assume (.not g) p = some q)
    (hg : q.guard.eval s0 = true) :
    p.guard.eval s0 = true ∧ ∃ n,
      q.cost = p.cost + n ∧ BigStepCost (.while g b)
        (Store.eval p.store s0)
        (Store.eval q.store s0) n := by
  have hs := assume_some _ _ _ s0 hx
  obtain ⟨hstore, hcost, hguard⟩ := hs
  rw [hguard] at hg
  have hpg : p.guard.eval s0 = true :=
    (Eq.mp (Bool.and_eq_true _ _) hg).1
  have hnot : BExp.eval (.not g) (Store.eval p.store s0) = true :=
    (Eq.mp (Bool.and_eq_true _ _) hg).2
  simp only [BExp.eval] at hnot
  have hgfalse : g.eval (Store.eval p.store s0) = false := by
    simpa using hnot
  refine ⟨hpg, 0, by omega, ?_⟩
  rw [hstore]
  exact .whileFalse hgfalse

private theorem loop_sound_gen (k : Nat) (g : BExp)
    (b : Cmd) (body : Path → List Leaf)
    (hb : ∀ (p q : Path) (s0 : State),
      Leaf.done q ∈ body p → q.guard.eval s0 = true →
        p.guard.eval s0 = true ∧ ∃ n,
          q.cost = p.cost + n ∧ BigStepCost b
            (Store.eval p.store s0)
            (Store.eval q.store s0) n)
    (fuel : Nat) (p q : Path) (s0 : State)
    (hm : Leaf.done q ∈ loop k g body fuel p)
    (hg : q.guard.eval s0 = true) :
    p.guard.eval s0 = true ∧ ∃ n,
      q.cost = p.cost + n ∧ BigStepCost (.while g b)
        (Store.eval p.store s0)
        (Store.eval q.store s0) n := by
  induction fuel generalizing p q with
  | zero =>
      cases hx : Path.assume (.not g) p
      · cases he : Path.assume g p
        · simp [loop, hx, he] at hm
        · simp [loop, hx, he] at hm
      · cases he : Path.assume g p
        · simp only [loop, hx, he, List.append_nil, List.mem_singleton, Leaf.done.injEq] at hm
          obtain rfl := hm
          have hs := assume_some _ _ _ s0 hx
          simp only [hs.1, hs.2.1] at hg ⊢
          rw [hs.2.2] at hg
          have hpg : p.guard.eval s0 = true :=
            (Eq.mp (Bool.and_eq_true _ _) hg).1
          have hnot : BExp.eval (.not g) (Store.eval p.store s0) = true :=
            (Eq.mp (Bool.and_eq_true _ _) hg).2
          simp only [BExp.eval] at hnot
          have hgfalse : g.eval (Store.eval p.store s0) = false := by
            simpa using hnot
          exact ⟨hpg, 0, by omega, .whileFalse hgfalse⟩
        · simp only [loop, hx, he, List.mem_append, List.mem_singleton,
            Leaf.done.injEq] at hm
          cases hm with
          | inl h =>
              obtain rfl := h
              exact loop_exit_sound _ _ _ _ _ hx hg
          | inr h => exact Leaf.noConfusion h
  | succ f ih =>
      cases hx : Path.assume (.not g) p
      · cases he : Path.assume g p
        · simp [loop, hx, he] at hm
        · rename_i qe
          by_cases hc : p.cost < k
          · simp only [loop, hx, he, ite_eq_left hc, List.nil_append,
              List.mem_flatMap] at hm
            obtain ⟨m, hml, hqm⟩ := hm
            cases m with
            | done r =>
                simp only [Leaf.bind] at hqm
                obtain ⟨hrguard, n2, hcost2, hloop⟩ := ih _ _ hqm hg
                obtain ⟨htickg, n1, hcost1, hbody⟩ := hb _ _ _ hml hrguard
                have hqe := assume_some _ _ _ s0 he
                obtain ⟨hqestore, hqecost, hqeguard⟩ := hqe
                have hqeg : qe.guard.eval s0 = true := htickg
                rw [hqeguard] at hqeg
                have hpg : p.guard.eval s0 = true :=
                  (Eq.mp (Bool.and_eq_true _ _) hqeg).1
                have hgen : g.eval (Store.eval p.store s0) = true :=
                  (Eq.mp (Bool.and_eq_true _ _) hqeg).2
                have htickc : (Path.tick qe).cost = qe.cost + 1 := rfl
                have hstore_tick : Store.eval (Path.tick qe).store s0 =
                    Store.eval p.store s0 := by
                  rw [show (Path.tick qe).store = qe.store from rfl, hqestore]
                rw [hstore_tick] at hbody
                refine ⟨hpg, 1 + n1 + n2, by omega,
                  .whileTrue hgen hbody hloop⟩
            | cut r =>
                simp [Leaf.bind] at hqm
          · simp [loop, hx, he, hc] at hm
      · cases he : Path.assume g p
        · simp only [loop, hx, he, List.append_nil, List.mem_singleton,
            Leaf.done.injEq] at hm
          obtain rfl := hm
          exact loop_exit_sound _ _ _ _ _ hx hg
        · rename_i qe
          by_cases hc : p.cost < k
          · simp only [loop, hx, he, ite_eq_left hc, List.mem_append,
              List.mem_singleton, Leaf.done.injEq,
              List.mem_flatMap] at hm
            cases hm with
            | inl hexit =>
                obtain rfl := hexit
                exact loop_exit_sound _ _ _ _ _ hx hg
            | inr hentry =>
                obtain ⟨m, hml, hqm⟩ := hentry
                cases m with
                | done r =>
                    simp only [Leaf.bind] at hqm
                    obtain ⟨hrguard, n2, hcost2, hloop⟩ := ih _ _ hqm hg
                    obtain ⟨htickg, n1, hcost1, hbody⟩ := hb _ _ _ hml hrguard
                    have hqe := assume_some _ _ _ s0 he
                    obtain ⟨hqestore, hqecost, hqeguard⟩ := hqe
                    have hqeg : qe.guard.eval s0 = true := htickg
                    rw [hqeguard] at hqeg
                    have hpg : p.guard.eval s0 = true :=
                      (Eq.mp (Bool.and_eq_true _ _) hqeg).1
                    have hgen : g.eval (Store.eval p.store s0) = true :=
                      (Eq.mp (Bool.and_eq_true _ _) hqeg).2
                    have htickc : (Path.tick qe).cost = qe.cost + 1 := rfl
                    have hstore_tick : Store.eval (Path.tick qe).store s0 =
                        Store.eval p.store s0 := by
                      rw [show (Path.tick qe).store = qe.store from rfl, hqestore]
                    rw [hstore_tick] at hbody
                    refine ⟨hpg, 1 + n1 + n2, by omega,
                      .whileTrue hgen hbody hloop⟩
                | cut r =>
                    simp [Leaf.bind] at hqm
          · simp only [loop, hx, he, ite_eq_right hc, List.mem_append,
              List.mem_singleton, Leaf.done.injEq] at hm
            cases hm with
            | inl h =>
                obtain rfl := h
                exact loop_exit_sound _ _ _ _ _ hx hg
            | inr h => exact Leaf.noConfusion h

private theorem run_sound_gen (k : Nat) (c : Cmd)
    (p q : Path) (s0 : State)
    (hm : Leaf.done q ∈ run k c p)
    (hg : q.guard.eval s0 = true) :
    p.guard.eval s0 = true ∧ ∃ n,
      q.cost = p.cost + n ∧ BigStepCost c
        (Store.eval p.store s0)
        (Store.eval q.store s0) n := by
  induction c generalizing p q s0 with
  | skip =>
      simp only [run, List.mem_singleton, Leaf.done.injEq] at hm
      obtain rfl := hm
      exact ⟨hg, 0, by omega, .skip _⟩
  | assign x a =>
      simp only [run, List.mem_singleton] at hm
      have hqq : q = Path.assign x a p := by injection hm
      subst hqq
      have hs := assign_store x a p s0
      have hgg : (Path.assign x a p).guard.eval s0 =
          p.guard.eval s0 := by
        change (p.guard.eval s0) = _
        rfl
      rw [hgg] at hg
      refine ⟨hg, 0, rfl, ?_⟩
      have hcc : (Path.assign x a p).cost = p.cost := rfl
      rw [hs]
      exact .assign _ _ _
  | seq c1 c2 ih1 ih2 =>
      simp only [run, List.mem_flatMap] at hm
      obtain ⟨m, hml, hqm⟩ := hm
      cases m with
      | done r =>
          simp only [Leaf.bind] at hqm
          obtain ⟨hgr, n2, hcq, h2⟩ := ih2 _ _ _ hqm hg
          obtain ⟨hgp, n1, hcr, h1⟩ := ih1 _ _ _ hml hgr
          refine ⟨hgp, n1 + n2, ?_, .seq h1 ?_⟩
          · omega
          · exact h2
      | cut r =>
          simp [Leaf.bind] at hqm
  | ite g c1 c2 ih1 ih2 =>
      cases h1 : Path.assume g p
      · cases h2 : Path.assume (.not g) p
        · simp [run, h1, h2] at hm
        · simp only [run, h1, h2, List.nil_append] at hm
          obtain ⟨hguard2, n, hcost, hstep⟩ := ih2 _ _ _ hm hg
          have hs := assume_some _ _ _ s0 h2
          obtain ⟨hstore, hcoste, hguard⟩ := hs
          rw [hguard] at hguard2
          have hpg : p.guard.eval s0 = true :=
            (Eq.mp (Bool.and_eq_true _ _) hguard2).1
          have hnot : BExp.eval (.not g) (Store.eval p.store s0) = true :=
            (Eq.mp (Bool.and_eq_true _ _) hguard2).2
          simp only [BExp.eval] at hnot
          have hgfalse : g.eval (Store.eval p.store s0) = false := by
            simpa using hnot
          rw [hstore] at hstep
          refine ⟨hpg, n, by omega, .iteFalse hgfalse hstep⟩
      · cases h2 : Path.assume (.not g) p
        · simp only [run, h1, h2, List.append_nil] at hm
          obtain ⟨hguard1, n, hcost, hstep⟩ := ih1 _ _ _ hm hg
          have hs := assume_some _ _ _ s0 h1
          obtain ⟨hstore, hcoste, hguard⟩ := hs
          rw [hguard] at hguard1
          have hpg : p.guard.eval s0 = true :=
            (Eq.mp (Bool.and_eq_true _ _) hguard1).1
          have hgtrue : g.eval (Store.eval p.store s0) = true :=
            (Eq.mp (Bool.and_eq_true _ _) hguard1).2
          rw [hstore] at hstep
          refine ⟨hpg, n, by omega, .iteTrue hgtrue hstep⟩
        · simp only [run, h1, h2, List.mem_append] at hm
          cases hm with
          | inl hleft =>
              obtain ⟨hguard1, n, hcost, hstep⟩ := ih1 _ _ _ hleft hg
              have hs := assume_some _ _ _ s0 h1
              obtain ⟨hstore, hcoste, hguard⟩ := hs
              rw [hguard] at hguard1
              have hpg : p.guard.eval s0 = true :=
                (Eq.mp (Bool.and_eq_true _ _) hguard1).1
              have hgtrue : g.eval (Store.eval p.store s0) = true :=
                (Eq.mp (Bool.and_eq_true _ _) hguard1).2
              rw [hstore] at hstep
              refine ⟨hpg, n, by omega, .iteTrue hgtrue hstep⟩
          | inr hright =>
              obtain ⟨hguard2, n, hcost, hstep⟩ := ih2 _ _ _ hright hg
              have hs := assume_some _ _ _ s0 h2
              obtain ⟨hstore, hcoste, hguard⟩ := hs
              rw [hguard] at hguard2
              have hpg : p.guard.eval s0 = true :=
                (Eq.mp (Bool.and_eq_true _ _) hguard2).1
              have hnot : BExp.eval (.not g) (Store.eval p.store s0) = true :=
                (Eq.mp (Bool.and_eq_true _ _) hguard2).2
              simp only [BExp.eval] at hnot
              have hgfalse : g.eval (Store.eval p.store s0) = false := by
                simpa using hnot
              rw [hstore] at hstep
              refine ⟨hpg, n, by omega, .iteFalse hgfalse hstep⟩
  | «while» g b ih =>
      simp only [run] at hm
      exact loop_sound_gen _ _ _ _
        (fun p q s0 hm hg => ih p q s0 hm hg) _ _ _ _ hm hg

private theorem assume_some_cost {b : BExp} {p q : Path}
    (h : Path.assume b p = some q) : q.cost = p.cost := by
  simp only [Path.assume] at h
  by_cases hb : bfold emptyTable (BExp.subst p.store b) =
      .truth false
  · simp only [ite_eq_left hb] at h
    cases h
  · simp only [ite_eq_right hb] at h
    have hq : ({ p with guard := (.and p.guard
      (bfold emptyTable (BExp.subst p.store b))) } : Path)
      = q := by cases h; rfl
    subst hq
    rfl

private theorem loop_done_cost_le (k : Nat) (g : BExp)
    (body : Path → List Leaf)
    (hbody : ∀ p q, Leaf.done q ∈ body p → p.cost ≤ k →
      q.cost ≤ k)
    (fuel : Nat) (p q : Path)
    (hm : Leaf.done q ∈ loop k g body fuel p)
    (hle : p.cost ≤ k) :
    q.cost ≤ k := by
  induction fuel generalizing p q with
  | zero =>
      cases hx : Path.assume (.not g) p
      · cases he : Path.assume g p
        · simp [loop, hx, he] at hm
        · simp [loop, hx, he] at hm
      · cases he : Path.assume g p
        · simp only [loop, hx, he, List.append_nil, List.mem_singleton,
            Leaf.done.injEq] at hm
          obtain rfl := hm
          have hc := assume_some_cost hx
          omega
        · simp only [loop, hx, he, List.mem_append, List.mem_singleton,
            Leaf.done.injEq] at hm
          cases hm with
          | inl h =>
              obtain rfl := h
              have hc := assume_some_cost hx
              omega
          | inr h => exact Leaf.noConfusion h
  | succ f ih =>
      cases hx : Path.assume (.not g) p
      · cases he : Path.assume g p
        · simp [loop, hx, he] at hm
        · rename_i qe
          by_cases hc : p.cost < k
          · simp only [loop, hx, he, ite_eq_left hc, List.nil_append,
              List.mem_flatMap] at hm
            obtain ⟨m, hml, hqm⟩ := hm
            cases m with
            | done r =>
                simp only [Leaf.bind] at hqm
                have hqecost := assume_some_cost he
                have htickc : (Path.tick qe).cost = qe.cost + 1 := rfl
                have htickle : (Path.tick qe).cost ≤ k := by omega
                have hrle := hbody _ _ hml htickle
                exact ih _ _ hqm hrle
            | cut r =>
                simp [Leaf.bind] at hqm
          · simp [loop, hx, he, hc] at hm
      · cases he : Path.assume g p
        · simp only [loop, hx, he, List.append_nil, List.mem_singleton,
            Leaf.done.injEq] at hm
          obtain rfl := hm
          have hc := assume_some_cost hx
          omega
        · rename_i qe
          by_cases hc : p.cost < k
          · simp only [loop, hx, he, ite_eq_left hc, List.mem_append,
              List.mem_singleton, Leaf.done.injEq,
              List.mem_flatMap] at hm
            cases hm with
            | inl hexit =>
                obtain rfl := hexit
                have hcc := assume_some_cost hx
                omega
            | inr hentry =>
                obtain ⟨m, hml, hqm⟩ := hentry
                cases m with
                | done r =>
                    simp only [Leaf.bind] at hqm
                    have hqecost := assume_some_cost he
                    have htickc : (Path.tick qe).cost = qe.cost + 1 := rfl
                    have htickle : (Path.tick qe).cost ≤ k := by omega
                    have hrle := hbody _ _ hml htickle
                    exact ih _ _ hqm hrle
                | cut r =>
                    simp [Leaf.bind] at hqm
          · simp only [loop, hx, he, ite_eq_right hc, List.mem_append,
              List.mem_singleton, Leaf.done.injEq] at hm
            cases hm with
            | inl h =>
                obtain rfl := h
                have hcc := assume_some_cost hx
                omega
            | inr h => exact Leaf.noConfusion h

private theorem run_done_cost_le (k : Nat) (c : Cmd)
    (p q : Path)
    (hm : Leaf.done q ∈ run k c p)
    (hle : p.cost ≤ k) :
    q.cost ≤ k := by
  induction c generalizing p q with
  | skip =>
      simp only [run, List.mem_singleton, Leaf.done.injEq] at hm
      obtain rfl := hm
      exact hle
  | assign x a =>
      simp only [run, List.mem_singleton] at hm
      have hqq : q = Path.assign x a p := by injection hm
      subst hqq
      have hcc : (Path.assign x a p).cost = p.cost := rfl
      omega
  | seq c1 c2 ih1 ih2 =>
      simp only [run, List.mem_flatMap] at hm
      obtain ⟨m, hml, hqm⟩ := hm
      cases m with
      | done r =>
          simp only [Leaf.bind] at hqm
          have hrle := ih1 _ _ hml hle
          exact ih2 _ _ hqm hrle
      | cut r =>
          simp [Leaf.bind] at hqm
  | ite g c1 c2 ih1 ih2 =>
      cases h1 : Path.assume g p
      · cases h2 : Path.assume (.not g) p
        · simp [run, h1, h2] at hm
        · rename_i q2
          simp only [run, h1, h2, List.nil_append] at hm
          have hc2 := assume_some_cost h2
          have hle2 : q2.cost ≤ k := by omega
          exact ih2 _ _ hm hle2
      · rename_i q1
        cases h2 : Path.assume (.not g) p
        · simp only [run, h1, h2, List.append_nil] at hm
          have hc1 := assume_some_cost h1
          have hle1 : q1.cost ≤ k := by omega
          exact ih1 _ _ hm hle1
        · rename_i q2
          simp only [run, h1, h2, List.mem_append] at hm
          cases hm with
          | inl hleft =>
              have hc1 := assume_some_cost h1
              have hle1 : q1.cost ≤ k := by omega
              exact ih1 _ _ hleft hle1
          | inr hright =>
              have hc2 := assume_some_cost h2
              have hle2 : q2.cost ≤ k := by omega
              exact ih2 _ _ hright hle2
  | «while» g b ih =>
      simp only [run] at hm
      exact loop_done_cost_le _ _ _
        (fun p q hm hle => ih p q hm hle) _ _ _ hm hle

theorem paths_sound (k : Nat) (c : Cmd) (q : Path)
    (s : State) (hm : q ∈ paths k c)
    (hg : q.guard.eval s = true) :
    BigStepCost c s (Store.eval q.store s) q.cost ∧
      q.cost ≤ k := by
  simp only [paths, leaves, List.mem_filterMap] at hm
  obtain ⟨l, hml, hdone⟩ := hm
  cases l with
  | done p =>
      simp only [Leaf.done?] at hdone
      have hpq : p = q := by injection hdone
      rw [hpq] at hml
      obtain ⟨_, n, hcost, hstep⟩ := run_sound_gen k c Path.init q s hml hg
      have hinit_cost : Path.init.cost = 0 := rfl
      rw [hinit_cost, Nat.zero_add] at hcost
      subst hcost
      have hstore : Store.eval Path.init.store s = s :=
        Store.eval_init s
      rw [hstore] at hstep
      have hle : q.cost ≤ k :=
        run_done_cost_le k c Path.init q hml (Nat.zero_le k)
      exact ⟨hstep, hle⟩
  | cut p =>
      simp [Leaf.done?] at hdone

private theorem loop_exit_mem (k : Nat) (g : BExp)
    (body : Path → List Leaf) (fuel : Nat) (p : Path)
    (s0 : State) (hg : p.guard.eval s0 = true)
    (hgfalse : g.eval (Store.eval p.store s0) = false) :
    ∃ q, Leaf.done q ∈ loop k g body fuel p ∧ q.guard.eval s0 = true ∧
      q.store = p.store ∧ q.cost = p.cost := by
  have hc : BExp.eval (.not g) (Store.eval p.store s0) = true := by
    simp [BExp.eval, hgfalse]
  obtain ⟨q', hsome, hguard⟩ := assume_some_of_true _ _ _ hg hc
  obtain ⟨hstore, hcost, -⟩ := assume_some _ _ _ s0 hsome
  refine ⟨q', ?_, hguard, hstore, hcost⟩
  cases fuel with
  | zero =>
      simp only [loop, hsome, List.mem_append, List.mem_singleton]
      exact Or.inl trivial
  | succ f =>
      simp only [loop, hsome, List.mem_append, List.mem_singleton]
      exact Or.inl trivial

private theorem loop_complete_gen (k : Nat) (g : BExp)
    (b : Cmd) (body : Path → List Leaf)
    (hbody : ∀ (p : Path) (s0 f : State) (n : Nat),
      BigStepCost b (Store.eval p.store s0) f n →
      p.guard.eval s0 = true → p.cost + n ≤ k →
      ∃ q, Leaf.done q ∈ body p ∧ q.guard.eval s0 = true ∧
        Store.eval q.store s0 = f ∧ q.cost = p.cost + n)
    (fuel : Nat) (p : Path) (s0 f : State) (n : Nat)
    (h : BigStepCost (.while g b) (Store.eval p.store s0) f n)
    (hg : p.guard.eval s0 = true)
    (hle : p.cost + n ≤ k)
    (hfuel : n ≤ fuel) :
    ∃ q, Leaf.done q ∈ loop k g body fuel p ∧ q.guard.eval s0 = true ∧
      Store.eval q.store s0 = f ∧ q.cost = p.cost + n := by
  induction fuel generalizing p s0 f n with
  | zero =>
      cases h with
      | whileFalse hgfalse =>
          obtain ⟨q, hmem, hqguard, hstore_q, hcost_q⟩ :=
            loop_exit_mem k g body 0 p s0 hg hgfalse
          exact ⟨q, hmem, hqguard, by rw [hstore_q], by omega⟩
      | whileTrue hgtrue hb hr =>
          have hfalse : False := by omega
          exact False.elim hfalse
  | succ fuel0 ih =>
      cases h with
      | whileFalse hgfalse =>
          obtain ⟨q, hmem, hqguard, hstore_q, hcost_q⟩ :=
            loop_exit_mem k g body (Nat.succ fuel0) p s0 hg hgfalse
          exact ⟨q, hmem, hqguard, by rw [hstore_q], by omega⟩
      | whileTrue hgtrue hb hr =>
          obtain ⟨qe, hentry, hqeguard⟩ :=
            assume_some_of_true g p s0 hg hgtrue
          have hqe := assume_some g p qe s0 hentry
          obtain ⟨hqestore, hqecost, -⟩ := hqe
          have hlt : p.cost < k := by omega
          have hstore_tick : Store.eval (Path.tick qe).store s0 =
              Store.eval p.store s0 := by
            rw [show (Path.tick qe).store = qe.store from rfl, hqestore]
          have hcost_tick : (Path.tick qe).cost = p.cost + 1 := by
            rw [show (Path.tick qe).cost = qe.cost + 1 from rfl, hqecost]
          have hguard_tick : (Path.tick qe).guard.eval s0 = true := hqeguard
          have hb' := hb
          rw [← hstore_tick] at hb'
          obtain ⟨r, hmem_body, hrguard, hstore_r, hcost_r⟩ :=
            hbody (Path.tick qe) s0 _ _ hb' hguard_tick
              (by rw [hcost_tick]; omega)
          have hr' := hr
          rw [← hstore_r] at hr'
          obtain ⟨q, hmem_loop, hqguard, hstore_q, hcost_q⟩ :=
            ih r s0 _ _ hr' hrguard
              (by rw [hcost_r, hcost_tick]; omega) (by omega)
          have hmem : Leaf.done q ∈ loop k g body (Nat.succ fuel0) p := by
            simp only [loop, hentry, ite_eq_left hlt, List.mem_append,
              List.mem_flatMap]
            refine Or.inr ⟨Leaf.done r, hmem_body, ?_⟩
            have hbind : Leaf.done q ∈
                Leaf.bind (fun r => loop k g body fuel0 r)
                  (Leaf.done r) := by
              simp only [Leaf.bind]
              exact hmem_loop
            exact hbind
          exact ⟨q, hmem, hqguard, hstore_q, by omega⟩

private theorem run_complete_gen (k : Nat) (c : Cmd)
    (p : Path) (s0 f : State) (n : Nat)
    (h : BigStepCost c (Store.eval p.store s0) f n)
    (hg : p.guard.eval s0 = true)
    (hle : p.cost + n ≤ k) :
    ∃ q, Leaf.done q ∈ run k c p ∧ q.guard.eval s0 = true ∧
      Store.eval q.store s0 = f ∧ q.cost = p.cost + n := by
  induction c generalizing p s0 f n with
  | skip =>
      cases h
      exact ⟨p, by simp [run], hg, rfl, by omega⟩
  | assign x a =>
      cases h
      have hs := assign_store x a p s0
      have hgg : (Path.assign x a p).guard.eval s0 = true := hg
      have hcc : (Path.assign x a p).cost = p.cost := rfl
      exact ⟨Path.assign x a p, by simp [run], hgg, hs, by omega⟩
  | seq c1 c2 ih1 ih2 =>
      cases h with
      | seq h1 h2 =>
          obtain ⟨r, hmem1, hrguard, hstore_r, hcost_r⟩ :=
            ih1 _ _ _ _ h1 hg (by omega)
          have h2' := h2
          rw [← hstore_r] at h2'
          obtain ⟨q, hmem2, hqguard, hstore_q, hcost_q⟩ :=
            ih2 _ _ _ _ h2' hrguard (by rw [hcost_r]; omega)
          have hmem : Leaf.done q ∈ run k (.seq c1 c2) p := by
            simp only [run, List.mem_flatMap]
            refine ⟨Leaf.done r, hmem1, ?_⟩
            simp only [Leaf.bind]
            exact hmem2
          exact ⟨q, hmem, hqguard, hstore_q, by omega⟩
  | ite g c1 c2 ih1 ih2 =>
      cases h with
      | iteTrue hgtrue h1 =>
          obtain ⟨qe, hentry, hqeguard⟩ :=
            assume_some_of_true g p s0 hg hgtrue
          have hqe := assume_some g p qe s0 hentry
          obtain ⟨hqestore, hqecost, -⟩ := hqe
          have h1' := h1
          rw [← hqestore] at h1'
          obtain ⟨q, hmem1, hqguard, hstore_q, hcost_q⟩ :=
            ih1 _ _ _ _ h1' hqeguard (by rw [hqecost]; omega)
          have hmem : Leaf.done q ∈ run k (.ite g c1 c2) p := by
            simp only [run, hentry, List.mem_append]
            exact Or.inl hmem1
          exact ⟨q, hmem, hqguard, hstore_q, by omega⟩
      | iteFalse hgfalse h2 =>
          have hc : BExp.eval (.not g)
              (Store.eval p.store s0) = true := by
            simp [BExp.eval, hgfalse]
          obtain ⟨qe, hentry, hqeguard⟩ :=
            assume_some_of_true (.not g) p s0 hg hc
          have hqe := assume_some (.not g) p qe s0 hentry
          obtain ⟨hqestore, hqecost, -⟩ := hqe
          have h2' := h2
          rw [← hqestore] at h2'
          obtain ⟨q, hmem2, hqguard, hstore_q, hcost_q⟩ :=
            ih2 _ _ _ _ h2' hqeguard (by rw [hqecost]; omega)
          have hmem : Leaf.done q ∈ run k (.ite g c1 c2) p := by
            simp only [run, hentry, List.mem_append]
            exact Or.inr hmem2
          exact ⟨q, hmem, hqguard, hstore_q, by omega⟩
  | «while» g b ih =>
      have hfuel : n ≤ k - p.cost := by omega
      obtain ⟨q, hmem, hqguard, hstore_q, hcost_q⟩ :=
        loop_complete_gen k g b (fun q => run k b q)
          (fun p s0 f n hb hguard hle => ih p s0 f n hb hguard hle)
          (k - p.cost) p s0 f n h hg hle hfuel
      have hmem' : Leaf.done q ∈ run k (Cmd.«while» g b) p := by
        simpa only [run] using hmem
      exact ⟨q, hmem', hqguard, hstore_q, hcost_q⟩

theorem paths_complete (k : Nat) (c : Cmd) (s f : State)
    (n : Nat) (h : BigStepCost c s f n) (hle : n ≤ k) :
    ∃ q ∈ paths k c, q.guard.eval s = true ∧
      Store.eval q.store s = f ∧ q.cost = n := by
  have hinit : Store.eval Path.init.store s = s := Store.eval_init s
  have hguard : Path.init.guard.eval s = true := rfl
  have hcost0 : Path.init.cost = 0 := rfl
  have hcost : Path.init.cost + n ≤ k := by omega
  have h' : BigStepCost c (Store.eval Path.init.store s) f n := by
    rw [hinit]
    exact h
  obtain ⟨q, hmem, hqguard, hstore_q, hcost_q⟩ :=
    run_complete_gen k c Path.init s f n h' hguard hcost
  refine ⟨q, ?_, hqguard, hstore_q, by omega⟩
  simp only [paths, leaves, List.mem_filterMap]
  exact ⟨_, hmem, rfl⟩

private theorem assume_some_of_eval_true (b : BExp) (p : Path) (s0 : State)
    (h : BExp.eval b (Store.eval p.store s0) = true) :
    ∃ q, Path.assume b p = some q := by
  cases ha : Path.assume b p with
  | none =>
      have hfalse := Path.assume_eq_none ha s0
      rw [h] at hfalse
      cases hfalse
  | some q => exact ⟨q, rfl⟩

private theorem assume_guard_true (b : BExp) (p q : Path) (s0 : State)
    (ha : Path.assume b p = some q)
    (hguard : p.guard.eval s0 = true)
    (heval : BExp.eval b (Store.eval p.store s0) = true) :
    q.guard.eval s0 = true := by
  have hqeq := (assume_some b p q s0 ha).2.2
  calc q.guard.eval s0
      = (p.guard.eval s0 && BExp.eval b (Store.eval p.store s0)) := hqeq
    _ = (true && true) := by rw [hguard, heval]
    _ = true := rfl

private theorem loop_cover_gen (k : Nat) (g : BExp) (body : Path → List Leaf)
    (s0 : State)
    (hbody : ∀ p, p.guard.eval s0 = true →
      ∃ l ∈ body p, (match l with
        | .done q => q.guard
        | .cut q => q.guard).eval s0 = true)
    (fuel : Nat) (p : Path) (hguard : p.guard.eval s0 = true) :
    ∃ l ∈ loop k g body fuel p, (match l with
      | .done q => q.guard
      | .cut q => q.guard).eval s0 = true := by
  induction fuel generalizing p with
  | zero =>
      cases he : BExp.eval g (Store.eval p.store s0) with
      | true =>
          obtain ⟨q, ha⟩ := assume_some_of_eval_true g p s0 he
          have hqguard := assume_guard_true g p q s0 ha hguard he
          refine ⟨.cut q, ?_, hqguard⟩
          simp only [loop, ha, List.mem_append]
          exact Or.inr (List.mem_singleton_self _)
      | false =>
          have hnot : BExp.eval (.not g) (Store.eval p.store s0) = true := by
            have h1 : BExp.eval (.not g) (Store.eval p.store s0) =
              !(BExp.eval g (Store.eval p.store s0)) := rfl
            have h2 : (!(false) : Bool) = true := rfl
            rw [h1, he]
            exact h2
          obtain ⟨q, ha⟩ := assume_some_of_eval_true (.not g) p s0 hnot
          have hqguard := assume_guard_true (.not g) p q s0 ha hguard hnot
          refine ⟨.done q, ?_, hqguard⟩
          simp only [loop, ha, List.mem_append]
          exact Or.inl (List.mem_singleton_self _)
  | succ f ih =>
      cases he : BExp.eval g (Store.eval p.store s0) with
      | false =>
          have hnot : BExp.eval (.not g) (Store.eval p.store s0) = true := by
            have h1 : BExp.eval (.not g) (Store.eval p.store s0) =
              !(BExp.eval g (Store.eval p.store s0)) := rfl
            have h2 : (!(false) : Bool) = true := rfl
            rw [h1, he]
            exact h2
          obtain ⟨q, ha⟩ := assume_some_of_eval_true (.not g) p s0 hnot
          have hqguard := assume_guard_true (.not g) p q s0 ha hguard hnot
          refine ⟨.done q, ?_, hqguard⟩
          simp only [loop, ha, List.mem_append]
          exact Or.inl (List.mem_singleton_self _)
      | true =>
          obtain ⟨q, ha⟩ := assume_some_of_eval_true g p s0 he
          have hqguard := assume_guard_true g p q s0 ha hguard he
          by_cases hc : p.cost < k
          · have htick : (Path.tick q).guard.eval s0 = true := hqguard
            obtain ⟨l1, hmem1, hcov1⟩ := hbody (Path.tick q) htick
            cases l1 with
            | done r =>
                obtain ⟨l2, hmem2, hcov2⟩ := ih r hcov1
                refine ⟨l2, ?_, hcov2⟩
                simp only [loop, ha, ite_eq_left hc]
                exact List.mem_append.mpr (Or.inr
                  (List.mem_flatMap.mpr ⟨.done r, hmem1, hmem2⟩))
            | cut r =>
                refine ⟨.cut r, ?_, hcov1⟩
                simp only [loop, ha, ite_eq_left hc]
                exact List.mem_append.mpr (Or.inr
                  (List.mem_flatMap.mpr ⟨.cut r, hmem1,
                    List.mem_singleton_self _⟩))
          · refine ⟨.cut q, ?_, hqguard⟩
            simp only [loop, ha, ite_eq_right hc]
            exact List.mem_append.mpr (Or.inr
              (List.mem_singleton_self _))

private theorem run_cover_gen (k : Nat) (c : Cmd) (p : Path) (s0 : State)
    (hguard : p.guard.eval s0 = true) :
    ∃ l ∈ run k c p, (match l with
      | .done q => q.guard
      | .cut q => q.guard).eval s0 = true := by
  induction c generalizing p with
  | skip =>
      refine ⟨.done p, ?_, hguard⟩
      simp only [run]
      exact List.mem_singleton_self _
  | assign x a =>
      refine ⟨.done (Path.assign x a p), ?_, ?_⟩
      · simp only [run]
        exact List.mem_singleton_self _
      · change (Path.assign x a p).guard.eval s0 = true
        exact hguard
  | seq c1 c2 ih1 ih2 =>
      obtain ⟨l1, hmem1, hcov1⟩ := ih1 p hguard
      cases l1 with
      | done r =>
          obtain ⟨l2, hmem2, hcov2⟩ := ih2 r hcov1
          refine ⟨l2, ?_, hcov2⟩
          simp only [run]
          exact List.mem_flatMap.mpr ⟨.done r, hmem1, hmem2⟩
      | cut r =>
          refine ⟨.cut r, ?_, hcov1⟩
          simp only [run]
          exact List.mem_flatMap.mpr ⟨.cut r, hmem1,
            List.mem_singleton_self _⟩
  | ite g c1 c2 ih1 ih2 =>
      cases he : BExp.eval g (Store.eval p.store s0) with
      | true =>
          obtain ⟨q, ha⟩ := assume_some_of_eval_true g p s0 he
          have hqguard := assume_guard_true g p q s0 ha hguard he
          obtain ⟨l, hmem, hcov⟩ := ih1 q hqguard
          refine ⟨l, ?_, hcov⟩
          simp only [run, ha, List.mem_append]
          exact Or.inl hmem
      | false =>
          have hnot : BExp.eval (.not g) (Store.eval p.store s0) = true := by
            have h1 : BExp.eval (.not g) (Store.eval p.store s0) =
              !(BExp.eval g (Store.eval p.store s0)) := rfl
            have h2 : (!(false) : Bool) = true := rfl
            rw [h1, he]
            exact h2
          obtain ⟨q, ha⟩ := assume_some_of_eval_true (.not g) p s0 hnot
          have hqguard := assume_guard_true (.not g) p q s0 ha hguard hnot
          obtain ⟨l, hmem, hcov⟩ := ih2 q hqguard
          refine ⟨l, ?_, hcov⟩
          simp only [run, ha, List.mem_append]
          exact Or.inr hmem
  | «while» g b ih =>
      simp only [run]
      exact loop_cover_gen k g (fun q => run k b q) s0
        (fun p h => ih p h) (k - p.cost) p hguard

private theorem loop_ge_done (k : Nat) (g : BExp) (body : Path → List Leaf)
    (hbody : ∀ p q, Leaf.done q ∈ body p → p.cost ≤ q.cost)
    (fuel : Nat) (p q : Path)
    (hm : Leaf.done q ∈ loop k g body fuel p) :
    p.cost ≤ q.cost := by
  induction fuel generalizing p q with
  | zero =>
      simp only [loop] at hm
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · cases hx : Path.assume (.not g) p with
        | none =>
            simp only [hx] at hm
            cases hm
        | some r =>
            simp only [hx, List.mem_singleton, Leaf.done.injEq] at hm
            obtain rfl := hm
            have hr := assume_some_cost hx
            omega
      · cases hx : Path.assume g p with
        | none =>
            simp only [hx] at hm
            cases hm
        | some _r =>
            simp only [hx, List.mem_singleton] at hm
            cases hm
  | succ f ih =>
      simp only [loop] at hm
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · cases hx : Path.assume (.not g) p with
        | none =>
            simp only [hx] at hm
            cases hm
        | some r =>
            simp only [hx, List.mem_singleton, Leaf.done.injEq] at hm
            obtain rfl := hm
            have hr := assume_some_cost hx
            omega
      · cases hx : Path.assume g p with
        | none =>
            simp only [hx] at hm
            cases hm
        | some r =>
            simp only [hx] at hm
            by_cases hc : p.cost < k
            · rw [ite_eq_left hc] at hm
              rw [List.mem_flatMap] at hm
              obtain ⟨l1, hmem1, hmem2⟩ := hm
              cases l1 with
              | done r2 =>
                  have hcost : (Path.tick r).cost = r.cost + 1 := rfl
                  have hr := assume_some_cost hx
                  have hr2ge := hbody _ _ hmem1
                  have hm2 : Leaf.done q ∈ loop k g body f r2 := hmem2
                  have hle2 := ih _ _ hm2
                  omega
              | cut _r2 =>
                  simp only [Leaf.bind, List.mem_singleton] at hmem2
                  cases hmem2
            · rw [ite_eq_right hc] at hm
              rw [List.mem_singleton] at hm
              cases hm

private theorem run_ge_done (k : Nat) (c : Cmd)
    (p q : Path)
    (hm : Leaf.done q ∈ run k c p) :
    p.cost ≤ q.cost := by
  induction c generalizing p q with
  | skip =>
      simp only [run, List.mem_singleton, Leaf.done.injEq] at hm
      obtain rfl := hm
      omega
  | assign x a =>
      simp only [run, List.mem_singleton, Leaf.done.injEq] at hm
      obtain rfl := hm
      have hcost : (Path.assign x a p).cost = p.cost := rfl
      omega
  | seq c1 c2 ih1 ih2 =>
      simp only [run] at hm
      rw [List.mem_flatMap] at hm
      obtain ⟨l1, hmem1, hmem2⟩ := hm
      cases l1 with
      | done r =>
          have hr1 := ih1 _ _ hmem1
          have hm2 : Leaf.done q ∈ run k c2 r := hmem2
          have hr2 := ih2 _ _ hm2
          omega
      | cut _r =>
          simp only [Leaf.bind, List.mem_singleton] at hmem2
          cases hmem2
  | ite g c1 c2 ih1 ih2 =>
      simp only [run] at hm
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · cases hx : Path.assume g p with
        | none =>
            simp only [hx] at hm
            cases hm
        | some r =>
            simp only [hx] at hm
            have hr := assume_some_cost hx
            have hle2 := ih1 _ _ hm
            omega
      · cases hx : Path.assume (.not g) p with
        | none =>
            simp only [hx] at hm
            cases hm
        | some r =>
            simp only [hx] at hm
            have hr := assume_some_cost hx
            have hle2 := ih2 _ _ hm
            omega
  | «while» g b ih =>
      simp only [run] at hm
      exact loop_ge_done k g (fun q => run k b q)
        (fun p q h => ih p q h) (k - p.cost) p q hm

private theorem loop_cut_cost (k : Nat) (g : BExp) (body : Path → List Leaf)
    (hbody_done_le : ∀ p q, Leaf.done q ∈ body p → p.cost ≤ k → q.cost ≤ k)
    (hbody_done_ge : ∀ p q, Leaf.done q ∈ body p → p.cost ≤ q.cost)
    (hbody_cut_eq : ∀ p q, Leaf.cut q ∈ body p → p.cost ≤ k → q.cost = k)
    (fuel : Nat) (p q : Path)
    (hm : Leaf.cut q ∈ loop k g body fuel p)
    (hle : p.cost ≤ k) (hge : k ≤ p.cost + fuel) :
    q.cost = k := by
  induction fuel generalizing p q with
  | zero =>
      simp only [loop] at hm
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · cases hx : Path.assume (.not g) p with
        | none =>
            simp only [hx] at hm
            cases hm
        | some _r =>
            simp only [hx, List.mem_singleton] at hm
            cases hm
      · cases hx : Path.assume g p with
        | none =>
            simp only [hx] at hm
            cases hm
        | some r =>
            simp only [hx, List.mem_singleton, Leaf.cut.injEq] at hm
            obtain rfl := hm
            have hr := assume_some_cost hx
            omega
  | succ f ih =>
      simp only [loop] at hm
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · cases hx : Path.assume (.not g) p with
        | none =>
            simp only [hx] at hm
            cases hm
        | some _r =>
            simp only [hx, List.mem_singleton] at hm
            cases hm
      · cases hx : Path.assume g p with
        | none =>
            simp only [hx] at hm
            cases hm
        | some r =>
            simp only [hx] at hm
            by_cases hc : p.cost < k
            · rw [ite_eq_left hc] at hm
              rw [List.mem_flatMap] at hm
              obtain ⟨l1, hmem1, hmem2⟩ := hm
              cases l1 with
              | done r2 =>
                  have hcost : (Path.tick r).cost = r.cost + 1 := rfl
                  have hr := assume_some_cost hx
                  have hle2 : (Path.tick r).cost ≤ k := by omega
                  have hr2le := hbody_done_le _ _ hmem1 hle2
                  have hr2ge := hbody_done_ge _ _ hmem1
                  have hm2 : Leaf.cut q ∈ loop k g body f r2 := hmem2
                  have hge2 : k ≤ r2.cost + f := by omega
                  exact ih _ _ hm2 hr2le hge2
              | cut r2 =>
                  simp only [Leaf.bind, List.mem_singleton,
                    Leaf.cut.injEq] at hmem2
                  obtain rfl := hmem2
                  have hcost : (Path.tick r).cost = r.cost + 1 := rfl
                  have hr := assume_some_cost hx
                  have hle2 : (Path.tick r).cost ≤ k := by omega
                  exact hbody_cut_eq _ _ hmem1 hle2
            · rw [ite_eq_right hc] at hm
              rw [List.mem_singleton, Leaf.cut.injEq] at hm
              obtain rfl := hm
              have hr := assume_some_cost hx
              omega

private theorem run_cut_cost (k : Nat) (c : Cmd)
    (p q : Path)
    (hm : Leaf.cut q ∈ run k c p)
    (hle : p.cost ≤ k) :
    q.cost = k := by
  induction c generalizing p q with
  | skip =>
      simp only [run, List.mem_singleton] at hm
      cases hm
  | assign x a =>
      simp only [run, List.mem_singleton] at hm
      cases hm
  | seq c1 c2 ih1 ih2 =>
      simp only [run] at hm
      rw [List.mem_flatMap] at hm
      obtain ⟨l1, hmem1, hmem2⟩ := hm
      cases l1 with
      | done r =>
          have hr : r.cost ≤ k := run_done_cost_le k c1 p r hmem1 hle
          have hm2 : Leaf.cut q ∈ run k c2 r := hmem2
          exact ih2 _ _ hm2 hr
      | cut r =>
          simp only [Leaf.bind, List.mem_singleton, Leaf.cut.injEq] at hmem2
          obtain rfl := hmem2
          exact ih1 _ _ hmem1 hle
  | ite g c1 c2 ih1 ih2 =>
      simp only [run] at hm
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · cases hx : Path.assume g p with
        | none =>
            simp only [hx] at hm
            cases hm
        | some r =>
            simp only [hx] at hm
            have hr := assume_some_cost hx
            have hle2 : r.cost ≤ k := by omega
            exact ih1 _ _ hm hle2
      · cases hx : Path.assume (.not g) p with
        | none =>
            simp only [hx] at hm
            cases hm
        | some r =>
            simp only [hx] at hm
            have hr := assume_some_cost hx
            have hle2 : r.cost ≤ k := by omega
            exact ih2 _ _ hm hle2
  | «while» g b ih =>
      simp only [run] at hm
      have hge : k ≤ p.cost + (k - p.cost) := by omega
      exact loop_cut_cost k g (fun q => run k b q)
        (fun p q h hle => run_done_cost_le k b p q h hle)
        (fun p q h => run_ge_done k b p q h)
        (fun p q h hle => ih p q h hle) (k - p.cost) p q hm hle hge

theorem leaves_cover (k : Nat) (c : Cmd) (s : State) :
    ∃ l ∈ leaves k c,
      (match l with
        | .done p => p.guard
        | .cut p => p.guard).eval s = true := by
  have hinit : Path.init.guard.eval s = true := rfl
  obtain ⟨l, hmem, hcov⟩ := run_cover_gen k c Path.init s hinit
  exact ⟨l, hmem, hcov⟩

theorem cutoffs_cost (k : Nat) (c : Cmd) (q : Path)
    (hm : q ∈ cutoffs k c) : q.cost = k := by
  simp only [cutoffs, leaves, List.mem_filterMap] at hm
  obtain ⟨l, hmem, hsome⟩ := hm
  cases l with
  | done r =>
      simp only [Leaf.cut?] at hsome
      cases hsome
  | cut r =>
      simp only [Leaf.cut?, Option.some.injEq] at hsome
      obtain rfl := hsome
      have h0 : Path.init.cost = 0 := rfl
      have hle : Path.init.cost ≤ k := by omega
      exact run_cut_cost k c _ _ hmem hle

theorem exhausted_of_no_path (k : Nat) (c : Cmd)
    (s : State)
    (hno : ∀ q ∈ paths k c, q.guard.eval s ≠ true) :
    (∃ q ∈ cutoffs k c, q.guard.eval s = true) ∧
      (∀ f n, BigStepCost c s f n → k < n) := by
  obtain ⟨l, hmem, hcov⟩ := leaves_cover k c s
  refine ⟨?_, ?_⟩
  · cases l with
    | done p =>
        have hmem_paths : p ∈ paths k c :=
          List.mem_filterMap.mpr ⟨.done p, hmem, rfl⟩
        exact absurd hcov (hno p hmem_paths)
    | cut p =>
        have hmem_cut : p ∈ cutoffs k c :=
          List.mem_filterMap.mpr ⟨.cut p, hmem, rfl⟩
        exact ⟨p, hmem_cut, hcov⟩
  · intro f n hbig
    by_cases hle : n ≤ k
    · obtain ⟨q, hmemq, hguard, -, -⟩ :=
        paths_complete _ _ _ _ _ hbig hle
      exact absurd hguard (hno q hmemq)
    · omega

end Symbolic

end Cslib.IMP
