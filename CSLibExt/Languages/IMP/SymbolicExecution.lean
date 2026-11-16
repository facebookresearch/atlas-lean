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

Enumerate terminal paths up to a total loop-entry budget.
-/

@[expose] public section

namespace Cslib.IMP

/-- Substitute a store into an arithmetic expression. -/
def AExp.subst (sg : Nat → AExp) : AExp → AExp
  | .const n => .const n
  | .var x => sg x
  | .add l r => .add (subst sg l) (subst sg r)
  | .sub l r => .sub (subst sg l) (subst sg r)
  | .mul l r => .mul (subst sg l) (subst sg r)

/-- Substitute a store into a boolean expression. -/
def BExp.subst (sg : Nat → AExp) : BExp → BExp
  | .truth v => .truth v
  | .eq l r => .eq (AExp.subst sg l) (AExp.subst sg r)
  | .le l r => .le (AExp.subst sg l) (AExp.subst sg r)
  | .not b => .not (subst sg b)
  | .and l r => .and (subst sg l) (subst sg r)

/-- Evaluating substituted arithmetic preserves meaning. -/
theorem AExp.eval_subst (sg : Nat → AExp) (a : AExp)
    (s : State) :
    (subst sg a).eval s = a.eval (fun x => (sg x).eval s) := by
  induction a with
  | const _ => rfl
  | var _ => rfl
  | add l r ihl ihr => simp [subst, ihl, ihr]
  | sub l r ihl ihr => simp [subst, ihl, ihr]
  | mul l r ihl ihr => simp [subst, ihl, ihr]

/-- Evaluating substituted booleans preserves meaning. -/
theorem BExp.eval_subst (sg : Nat → AExp) (b : BExp)
    (s : State) :
    (subst sg b).eval s = b.eval (fun x => (sg x).eval s) := by
  induction b with
  | truth _ => rfl
  | eq l r => simp [subst, AExp.eval_subst]
  | le l r => simp [subst, AExp.eval_subst]
  | not b ih => simp [subst, ih]
  | and l r ihl ihr => simp [subst, ihl, ihr]

/-- Counted big-step semantics counting loop entries. -/
inductive BigStepCost : Cmd → State → State → Nat → Prop where
  | skip (s : State) : BigStepCost .skip s s 0
  | assign (x : Nat) (a : AExp) (s : State) :
      BigStepCost (.assign x a) s
        (Function.update s x (a.eval s)) 0
  | seq {c1 c2 : Cmd} {s t f : State} {n1 n2 : Nat} :
      BigStepCost c1 s t n1 →
      BigStepCost c2 t f n2 →
      BigStepCost (.seq c1 c2) s f (n1 + n2)
  | if_true {b : BExp} {c1 c2 : Cmd} {s f : State}
      {n : Nat} :
      b.eval s = true →
      BigStepCost c1 s f n →
      BigStepCost (.if_ b c1 c2) s f n
  | if_false {b : BExp} {c1 c2 : Cmd} {s f : State}
      {n : Nat} :
      b.eval s = false →
      BigStepCost c2 s f n →
      BigStepCost (.if_ b c1 c2) s f n
  | while_false {b : BExp} {c : Cmd} {s : State} :
      b.eval s = false →
      BigStepCost (.while b c) s s 0
  | while_true {b : BExp} {c : Cmd} {s t f : State}
      {n1 n2 : Nat} :
      b.eval s = true →
      BigStepCost c s t n1 →
      BigStepCost (.while b c) t f n2 →
      BigStepCost (.while b c) s f (1 + n1 + n2)

/-- Erasing counts yields canonical big-step semantics. -/
theorem bigStepCost_erase (c : Cmd) (s f : State) :
    (∃ n, BigStepCost c s f n) ↔ BigStep c s f := by
  constructor
  · rintro ⟨_, h⟩
    induction h with
    | skip _ => exact BigStep.skip _
    | assign _ _ _ => exact BigStep.assign _ _ _
    | seq _ _ ih1 ih2 => exact BigStep.seq ih1 ih2
    | if_true hb _ ih => exact BigStep.if_true hb ih
    | if_false hb _ ih => exact BigStep.if_false hb ih
    | while_false hb => exact BigStep.while_false hb
    | while_true hb _ _ ih1 ih2 =>
        exact BigStep.while_true hb ih1 ih2
  · intro h
    induction h with
    | skip _ => exact ⟨0, .skip _⟩
    | assign _ _ _ => exact ⟨0, .assign _ _ _⟩
    | seq _ _ ih1 ih2 =>
        obtain ⟨n1, h1⟩ := ih1
        obtain ⟨n2, h2⟩ := ih2
        exact ⟨n1 + n2, .seq h1 h2⟩
    | if_true hb _ ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n, .if_true hb hn⟩
    | if_false hb _ ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n, .if_false hb hn⟩
    | while_false hb => exact ⟨0, .while_false hb⟩
    | while_true hb _ _ ih1 ih2 =>
        obtain ⟨n1, h1⟩ := ih1
        obtain ⟨n2, h2⟩ := ih2
        exact ⟨1 + n1 + n2, .while_true hb h1 h2⟩

end Cslib.IMP

namespace Cslib.IMP.Symbolic

/-- A symbolic store mapping variables to terms. -/
abbrev Store := Nat → AExp

/-- The identity symbolic store. -/
def Store.init : Store := fun x => .var x

/-- Evaluate a symbolic store at an initial state. -/
def Store.eval (sg : Store) (s : State) : State :=
  fun x => (sg x).eval s

/-- Store from a constant table, unknown as variables. -/
def tableStore (t : ConstTable) : Store :=
  fun x =>
    match t x with
    | some n => .const n
    | none => .var x

/-- A symbolic path: guard, store and cost. -/
structure Path where
  guard : BExp
  store : Store
  cost : Nat

/-- The initial symbolic path. -/
def Path.init : Path :=
  { guard := .truth true, store := Store.init, cost := 0 }

/-- Symbolic assignment with folding. -/
def Path.assign (x : Nat) (a : AExp) (p : Path) : Path :=
  { guard := p.guard,
    store :=
      Function.update p.store x
        (afold emptyTable (AExp.subst p.store a)),
    cost := p.cost }

/-- Assume a conjunct, pruning only proved false. -/
def Path.assume (b : BExp) (p : Path) : Option Path :=
  let b' := bfold emptyTable (BExp.subst p.store b)
  if b' = .truth false then none
  else
    some
      { guard := .and p.guard b', store := p.store,
        cost := p.cost }

/-- Tick the loop-entry counter. -/
def Path.tick (p : Path) : Path :=
  { guard := p.guard, store := p.store,
    cost := p.cost + 1 }

/-- A symbolic leaf: terminal or cutoff. -/
inductive Leaf where
  | done (p : Path) : Leaf
  | cut (p : Path) : Leaf

/-- Bind terminal leaves through a continuation. -/
def Leaf.bind (h : Path → List Leaf) : Leaf → List Leaf
  | .done q => h q
  | .cut q => [.cut q]

/-- Terminal path of a leaf, if any. -/
def Leaf.done? : Leaf → Option Path
  | .done q => some q
  | .cut _ => none

/-- Cutoff path of a leaf, if any. -/
def Leaf.cut? : Leaf → Option Path
  | .done _ => none
  | .cut q => some q

/-- Bounded loop unrolling with shared budget. -/
def loop (k : Nat) (g : BExp) (body : Path → List Leaf) :
    Nat → Path → List Leaf
  | 0, p =>
      (match Path.assume (.not g) p with
        | none => []
        | some q => [Leaf.done q])
      ++ (match Path.assume g p with
        | none => []
        | some q => [Leaf.cut q])
  | f + 1, p =>
      (match Path.assume (.not g) p with
        | none => []
        | some q => [Leaf.done q])
      ++ (match Path.assume g p with
        | none => []
        | some q =>
            if p.cost < k then
              (body (Path.tick q)).flatMap
                (Leaf.bind (loop k g body f))
            else [Leaf.cut q])

/-- Symbolically execute a command with budget. -/
def run : Nat → Cmd → Path → List Leaf
  | _, .skip, p => [Leaf.done p]
  | _, .assign x a, p => [Leaf.done (Path.assign x a p)]
  | k, .seq c1 c2, p =>
      (run k c1 p).flatMap
        (Leaf.bind (fun q => run k c2 q))
  | k, .if_ g c1 c2, p =>
      (match Path.assume g p with
        | none => []
        | some q => run k c1 q)
      ++ (match Path.assume (.not g) p with
        | none => []
        | some q => run k c2 q)
  | k, .while g b, p =>
      loop k g (fun q => run k b q) (k - p.cost) p

/-- All leaves from symbolic execution. -/
def leaves (k : Nat) (c : Cmd) : List Leaf :=
  run k c Path.init

/-- Terminal paths from symbolic execution. -/
def paths (k : Nat) (c : Cmd) : List Path :=
  (leaves k c).filterMap Leaf.done?

/-- Cutoff paths from symbolic execution. -/
def cutoffs (k : Nat) (c : Cmd) : List Path :=
  (leaves k c).filterMap Leaf.cut?

private theorem afold_empty_eval (a : AExp) (s : State) :
    (afold emptyTable a).eval s = a.eval s :=
  afold_eval emptyTable a s (emptyTable_approx s)

private theorem bfold_empty_eval (b : BExp) (s : State) :
    (bfold emptyTable b).eval s = b.eval s :=
  bfold_eval emptyTable b s (emptyTable_approx s)

/-- The identity store evaluates to the state. -/
theorem Store.eval_init (s : State) :
    Store.eval Store.init s = s := by
  funext x
  rfl

/-- Store update commutes with evaluation. -/
theorem Store.eval_update (sg : Store) (x : Nat) (e : AExp)
    (s : State) :
    Store.eval (Function.update sg x e) s =
      Function.update (Store.eval sg s) x (e.eval s) := by
  funext y
  simp only [Store.eval]
  cases Decidable.em (y = x) with
  | inl h =>
      subst h
      simp
  | inr h =>
      simp [h]

/-- Folding equals substitution then empty folding. -/
theorem afold_eq_subst (t : ConstTable) (a : AExp) :
    afold t a =
      afold emptyTable (AExp.subst (tableStore t) a) := by
  induction a with
  | const _ => rfl
  | var x =>
      simp only [AExp.subst, tableStore]
      cases h : t x with
      | none =>
          simp [h, afold, emptyTable]
      | some n =>
          simp [h, afold]
  | add l r ihl ihr =>
      simp only [AExp.subst] at *
      simp only [afold, ihl, ihr]
  | sub l r ihl ihr =>
      simp only [AExp.subst] at *
      simp only [afold, ihl, ihr]
  | mul l r ihl ihr =>
      simp only [AExp.subst] at *
      simp only [afold, ihl, ihr]

/-- Boolean folding equals substitution then folding. -/
theorem bfold_eq_subst (t : ConstTable) (b : BExp) :
    bfold t b =
      bfold emptyTable (BExp.subst (tableStore t) b) := by
  induction b with
  | truth _ => rfl
  | eq l r =>
      simp only [BExp.subst, bfold, afold_eq_subst]
  | le l r =>
      simp only [BExp.subst, bfold, afold_eq_subst]
  | not b ih =>
      simp only [BExp.subst, bfold, ih]
  | and l r ihl ihr =>
      simp only [BExp.subst, bfold, ihl, ihr]

/-- Approximation iff table store evaluates to state. -/
theorem constApprox_iff (t : ConstTable) (s : State) :
    ConstApprox t s ↔ Store.eval (tableStore t) s = s := by
  constructor
  · intro h
    funext x
    simp only [Store.eval, tableStore]
    cases hx : t x with
    | none => simp [hx]
    | some n =>
        simp only [hx]
        have hsn : s x = n := h x n hx
        simp [hsn]
  · intro h x n hx
    have hx2 : (tableStore t x).eval s = s x := by
      have := congrFun h x
      simpa [Store.eval] using this
    simp [tableStore, hx] at hx2
    exact hx2.symm

/-- Pruned branches are false in every state. -/
theorem Path.assume_eq_none (b : BExp) (p : Path) :
    Path.assume b p = none →
      ∀ s, b.eval (Store.eval p.store s) = false := by
  intro h s
  simp only [Path.assume] at h
  cases Decidable.em
      (bfold emptyTable (BExp.subst p.store b) =
        .truth false) with
  | inl hb =>
      have he :
          (bfold emptyTable
            (BExp.subst p.store b)).eval s =
            (BExp.subst p.store b).eval s :=
        bfold_empty_eval _ s
      rw [hb] at he
      simp at he
      have hs := BExp.eval_subst p.store b s
      rw [hs] at he
      simpa [Store.eval] using he
  | inr hb =>
      simp [hb] at h

private theorem assign_guard (x : Nat) (a : AExp)
    (p : Path) :
    (Path.assign x a p).guard = p.guard :=
  rfl

private theorem assign_cost (x : Nat) (a : AExp)
    (p : Path) :
    (Path.assign x a p).cost = p.cost :=
  rfl

private theorem assign_eval (x : Nat) (a : AExp)
    (p : Path) (s : State) :
    Store.eval (Path.assign x a p).store s =
      Function.update (Store.eval p.store s) x
        (a.eval (Store.eval p.store s)) := by
  simp only [Path.assign]
  rw [Store.eval_update]
  congr 1
  have h1 :
      (afold emptyTable
        (AExp.subst p.store a)).eval s =
        (AExp.subst p.store a).eval s :=
    afold_empty_eval _ s
  have h2 :
      (AExp.subst p.store a).eval s =
        a.eval (fun x => (p.store x).eval s) :=
    AExp.eval_subst _ _ _
  rw [h1, h2]
  rfl

private theorem tick_guard (p : Path) :
    (Path.tick p).guard = p.guard :=
  rfl

private theorem tick_store (p : Path) :
    (Path.tick p).store = p.store :=
  rfl

private theorem tick_cost (p : Path) :
    (Path.tick p).cost = p.cost + 1 :=
  rfl

private theorem tick_eval (p : Path) (s : State) :
    Store.eval (Path.tick p).store s =
      Store.eval p.store s := by
  simp [Path.tick, Store.eval]

private theorem assume_some_store (b : BExp) (p q : Path) :
    Path.assume b p = some q → q.store = p.store := by
  intro h
  simp only [Path.assume] at h
  cases Decidable.em
      (bfold emptyTable (BExp.subst p.store b) =
        .truth false) with
  | inl hb => simp [hb] at h
  | inr hb =>
      simp [hb] at h
      cases h
      rfl

private theorem assume_some_cost (b : BExp) (p q : Path) :
    Path.assume b p = some q → q.cost = p.cost := by
  intro h
  simp only [Path.assume] at h
  cases Decidable.em
      (bfold emptyTable (BExp.subst p.store b) =
        .truth false) with
  | inl hb => simp [hb] at h
  | inr hb =>
      simp [hb] at h
      cases h
      rfl

private theorem assume_some_true (b : BExp) (p q : Path)
    (s0 : State) :
    Path.assume b p = some q →
      q.guard.eval s0 = true →
      p.guard.eval s0 = true ∧
        b.eval (Store.eval p.store s0) = true := by
  intro h hq
  simp only [Path.assume] at h
  cases Decidable.em
      (bfold emptyTable (BExp.subst p.store b) =
        .truth false) with
  | inl hb => simp [hb] at h
  | inr hb =>
      simp [hb] at h
      cases h
      simp at hq
      obtain ⟨hg, hb2⟩ := hq
      refine ⟨hg, ?_⟩
      have he :
          (bfold emptyTable
            (BExp.subst p.store b)).eval s0 =
            (BExp.subst p.store b).eval s0 :=
        bfold_empty_eval _ s0
      have hs := BExp.eval_subst p.store b s0
      simp [Store.eval] at hs ⊢
      rw [← hs, ← he]
      exact hb2

private theorem assume_some_of_true (b : BExp) (p : Path)
    (s0 : State) :
    p.guard.eval s0 = true →
      b.eval (Store.eval p.store s0) = true →
      ∃ q, Path.assume b p = some q ∧
        q.guard.eval s0 = true := by
  intro hg hb
  cases h :
      Path.assume b p with
  | none =>
      have hf := Path.assume_eq_none b p h s0
      simp [Store.eval] at hf ⊢
      rw [hb] at hf
      simp at hf
  | some q =>
      refine ⟨q, rfl, ?_⟩
      have hqq :
          p.guard.eval s0 = true ∧
            b.eval (Store.eval p.store s0) = true →
          q.guard.eval s0 = true := by
        intro _
        simp only [Path.assume] at h
        cases Decidable.em
            (bfold emptyTable
              (BExp.subst p.store b) =
              .truth false) with
        | inl hb2 => simp [hb2] at h
        | inr hb2 =>
            simp [hb2] at h
            cases h
            simp
            have he :
                (bfold emptyTable
                  (BExp.subst p.store b)).eval s0 =
                  (BExp.subst p.store b).eval s0 :=
              bfold_empty_eval _ s0
            have hs := BExp.eval_subst p.store b s0
            simp [Store.eval] at hs ⊢
            rw [← hs, ← he]
            simp [hg, hb]
      exact hqq ⟨hg, hb⟩

/-- Cost of a leaf's path. -/
private def leafCost : Leaf → Nat
  | .done q => q.cost
  | .cut q => q.cost

private theorem mem_flatMap {α : Type} {β : Type}
    (f : α → List β) (xs : List α) (y : β) :
    y ∈ xs.flatMap f ↔ ∃ x, x ∈ xs ∧ y ∈ f x := by
  induction xs with
  | nil => simp
  | cons hd tl ih =>
      simp only [List.flatMap, List.mem_append, ih]
      constructor
      · rintro (h | ⟨x, hx, hy⟩)
        · exact ⟨hd, by simp, h⟩
        · exact ⟨x, by simp [hx], hy⟩
      · rintro ⟨x, hx, hy⟩
        simp at hx
        cases hx with
        | inl h =>
            subst h
            exact Or.inl hy
        | inr h =>
            exact Or.inr ⟨x, h, hy⟩

private theorem mem_paths (k : Nat) (c : Cmd) (q : Path) :
    q ∈ paths k c ↔ Leaf.done q ∈ leaves k c := by
  simp only [paths, leaves]
  induction (run k c Path.init) with
  | nil => simp
  | cons hd tl ih =>
      cases hd with
      | done r =>
          simp [Leaf.done?, ih]
          constructor
          · rintro (h | h)
            · subst h
              exact Or.inl rfl
            · exact Or.inr h
          · rintro (h | h)
            · cases h
              exact Or.inl rfl
            · exact Or.inr (ih.mpr h)
      | cut r =>
          simp [Leaf.cut?, Leaf.done?, ih]
          constructor
          · intro h
            exact Or.inr (ih.mp h)
          · rintro (h | h)
            · cases h
            · exact ih.mpr h

private theorem mem_cutoffs (k : Nat) (c : Cmd)
    (q : Path) :
    q ∈ cutoffs k c ↔ Leaf.cut q ∈ leaves k c := by
  simp only [cutoffs, leaves]
  induction (run k c Path.init) with
  | nil => simp
  | cons hd tl ih =>
      cases hd with
      | done r =>
          simp [Leaf.done?, Leaf.cut?, ih]
          constructor
          · intro h
            exact Or.inr (ih.mp h)
          · rintro (h | h)
            · cases h
            · exact ih.mpr h
      | cut r =>
          simp [Leaf.cut?, ih]
          constructor
          · rintro (h | h)
            · subst h
              exact Or.inl rfl
            · exact Or.inr h
          · rintro (h | h)
            · cases h
              exact Or.inl rfl
            · exact Or.inr (ih.mpr h)

private theorem loop_cost_mono (k : Nat) (g : BExp)
    (body : Path → List Leaf)
    (hbody : ∀ p, ∀ l ∈ body p,
      p.cost ≤ leafCost l) :
    ∀ fuel p, ∀ l ∈ loop k g body fuel p,
      p.cost ≤ leafCost l := by
  intro fuel
  induction fuel with
  | zero =>
      intro p l hl
      simp only [loop, List.mem_append] at hl
      cases hl with
      | inl he =>
          cases heq : Path.assume (.not g) p with
          | none => simp [heq] at he
          | some q =>
              simp [heq] at he
              cases he
              simp [leafCost]
              have hc := assume_some_cost _ p q heq
              omega
      | inr he =>
          cases heq : Path.assume g p with
          | none => simp [heq] at he
          | some q =>
              simp [heq] at he
              cases he
              simp [leafCost]
              have hc := assume_some_cost _ p q heq
              omega
  | succ f ih =>
      intro p l hl
      simp only [loop, List.mem_append] at hl
      cases hl with
      | inl he =>
          cases heq : Path.assume (.not g) p with
          | none => simp [heq] at he
          | some q =>
              simp [heq] at he
              cases he
              simp [leafCost]
              have hc := assume_some_cost _ p q heq
              omega
      | inr he =>
          cases heq : Path.assume g p with
          | none => simp [heq] at he
          | some q =>
              simp [heq] at he
              cases Decidable.em (p.cost < k) with
              | inl hlt =>
                  simp [hlt] at he
                  rw [mem_flatMap] at he
                  obtain ⟨x, hx, hy⟩ := he
                  cases x with
                  | done r =>
                      simp [Leaf.bind] at hy
                      have hb := hbody _ _ hx
                      have hi := ih r l hy
                      simp [leafCost] at hb hi ⊢
                      have hc :=
                        assume_some_cost _ p q heq
                      have ht := tick_cost q
                      omega
                  | cut r =>
                      simp [Leaf.bind] at hy
                      cases hy
                      have hb := hbody _ _ hx
                      simp [leafCost] at hb ⊢
                      have hc :=
                        assume_some_cost _ p q heq
                      have ht := tick_cost q
                      omega
              | inr hge =>
                  simp [hge] at he
                  cases he
                  simp [leafCost]
                  have hc := assume_some_cost _ p q heq
                  omega

private theorem run_cost_mono (k : Nat) :
    ∀ c p, ∀ l ∈ run k c p, p.cost ≤ leafCost l := by
  intro c
  induction c with
  | skip =>
      intro p l hl
      simp [run, leafCost] at hl
      cases hl
      omega
  | assign x a =>
      intro p l hl
      simp [run, leafCost] at hl
      cases hl
      simp [leafCost]
      have hc := assign_cost x a p
      omega
  | seq c1 c2 ih1 ih2 =>
      intro p l hl
      simp only [run] at hl
      rw [mem_flatMap] at hl
      obtain ⟨x, hx, hy⟩ := hl
      cases x with
      | done r =>
          simp [Leaf.bind] at hy
          have h1 := ih1 p x hx
          have h2 := ih2 r l hy
          simp [leafCost] at h1 h2 ⊢
          omega
      | cut r =>
          simp [Leaf.bind] at hy
          cases hy
          have h1 := ih1 p (Leaf.cut r) hx
          simp [leafCost] at h1 ⊢
          exact h1
  | if_ g c1 c2 ih1 ih2 =>
      intro p l hl
      simp only [run, List.mem_append] at hl
      cases hl with
      | inl he =>
          cases heq : Path.assume g p with
          | none => simp [heq] at he
          | some q =>
              simp [heq] at he
              have h1 := ih1 q l he
              have hc := assume_some_cost _ p q heq
              simp [leafCost] at h1 ⊢
              omega
      | inr he =>
          cases heq : Path.assume (.not g) p with
          | none => simp [heq] at he
          | some q =>
              simp [heq] at he
              have h1 := ih2 q l he
              have hc := assume_some_cost _ p q heq
              simp [leafCost] at h1 ⊢
              omega
  | while g b ih =>
      intro p l hl
      simp only [run] at hl
      have hb : ∀ p, ∀ l ∈ (fun q => run k b q) p,
          p.cost ≤ leafCost l := by
        intro p l hl
        exact ih p l hl
      have hm := loop_cost_mono k g _ hb _ p l hl
      exact hm

private theorem loop_cost_le (k : Nat) (g : BExp)
    (body : Path → List Leaf)
    (hbody : ∀ p, p.cost ≤ k →
      ∀ l ∈ body p, leafCost l ≤ k) :
    ∀ fuel p, p.cost ≤ k →
      ∀ l ∈ loop k g body fuel p, leafCost l ≤ k := by
  intro fuel
  induction fuel with
  | zero =>
      intro p hp l hl
      simp only [loop, List.mem_append] at hl
      cases hl with
      | inl he =>
          cases heq : Path.assume (.not g) p with
          | none => simp [heq] at he
          | some q =>
              simp [heq] at he
              cases he
              simp [leafCost]
              have hc := assume_some_cost _ p q heq
              omega
      | inr he =>
          cases heq : Path.assume g p with
          | none => simp [heq] at he
          | some q =>
              simp [heq] at he
              cases he
              simp [leafCost]
              have hc := assume_some_cost _ p q heq
              omega
  | succ f ih =>
      intro p hp l hl
      simp only [loop, List.mem_append] at hl
      cases hl with
      | inl he =>
          cases heq : Path.assume (.not g) p with
          | none => simp [heq] at he
          | some q =>
              simp [heq] at he
              cases he
              simp [leafCost]
              have hc := assume_some_cost _ p q heq
              omega
      | inr he =>
          cases heq : Path.assume g p with
          | none => simp [heq] at he
          | some q =>
              simp [heq] at he
              cases Decidable.em (p.cost < k) with
              | inl hlt =>
                  simp [hlt] at he
                  rw [mem_flatMap] at he
                  obtain ⟨x, hx, hy⟩ := he
                  cases x with
                  | done r =>
                      simp [Leaf.bind] at hy
                      have ht : (Path.tick q).cost ≤ k := by
                        have hc :=
                          assume_some_cost _ p q heq
                        have htc := tick_cost q
                        omega
                      have hb0 := hbody _ ht _ hx
                      have hr : r.cost ≤ k := by
                        simpa [leafCost] using hb0
                      have hi := ih r hr l hy
                      exact hi
                  | cut r =>
                      simp [Leaf.bind] at hy
                      cases hy
                      have ht : (Path.tick q).cost ≤ k := by
                        have hc :=
                          assume_some_cost _ p q heq
                        have htc := tick_cost q
                        omega
                      have hb := hbody _ ht _ hx
                      simpa [leafCost] using hb
              | inr hge =>
                  simp [hge] at he
                  cases he
                  simp [leafCost]
                  have hc := assume_some_cost _ p q heq
                  omega

private theorem run_cost_le (k : Nat) :
    ∀ c p, p.cost ≤ k →
      ∀ l ∈ run k c p, leafCost l ≤ k := by
  intro c
  induction c with
  | skip =>
      intro p hp l hl
      simp [run, leafCost] at hl
      cases hl
      simpa [leafCost] using hp
  | assign x a =>
      intro p hp l hl
      simp [run, leafCost] at hl
      cases hl
      simp [leafCost]
      have hc := assign_cost x a p
      omega
  | seq c1 c2 ih1 ih2 =>
      intro p hp l hl
      simp only [run] at hl
      rw [mem_flatMap] at hl
      obtain ⟨x, hx, hy⟩ := hl
      cases x with
      | done r =>
          simp [Leaf.bind] at hy
          have h1 := ih1 p hp x hx
          have hr : r.cost ≤ k := by
            simpa [leafCost] using h1
          exact ih2 r hr l hy
      | cut r =>
          simp [Leaf.bind] at hy
          cases hy
          have h1 := ih1 p hp _ hx
          simpa [leafCost] using h1
  | if_ g c1 c2 ih1 ih2 =>
      intro p hp l hl
      simp only [run, List.mem_append] at hl
      cases hl with
      | inl he =>
          cases heq : Path.assume g p with
          | none => simp [heq] at he
          | some q =>
              simp [heq] at he
              have hc := assume_some_cost _ p q heq
              have hq : q.cost ≤ k := by omega
              exact ih1 q hq l he
      | inr he =>
          cases heq : Path.assume (.not g) p with
          | none => simp [heq] at he
          | some q =>
              simp [heq] at he
              have hc := assume_some_cost _ p q heq
              have hq : q.cost ≤ k := by omega
              exact ih2 q hq l he
  | while g b ih =>
      intro p hp l hl
      simp only [run] at hl
      have hb : ∀ p, p.cost ≤ k →
          ∀ l ∈ (fun q => run k b q) p,
            leafCost l ≤ k := by
        intro p hp l hl
        exact ih p hp l hl
      exact loop_cost_le k g _ hb _ p hp l hl

private theorem loop_cutoffs_cost (k : Nat) (g : BExp)
    (body : Path → List Leaf)
    (hle : ∀ p, p.cost ≤ k →
      ∀ l ∈ body p, leafCost l ≤ k)
    (hge : ∀ p, ∀ l ∈ body p,
      p.cost ≤ leafCost l)
    (hcut : ∀ p, p.cost ≤ k →
      ∀ q, Leaf.cut q ∈ body p → q.cost = k) :
    ∀ fuel p, p.cost ≤ k → k - p.cost ≤ fuel →
      ∀ q, Leaf.cut q ∈ loop k g body fuel p →
        q.cost = k := by
  intro fuel
  induction fuel with
  | zero =>
      intro p hp hf q hq
      simp only [loop, List.mem_append] at hq
      cases hq with
      | inl he =>
          cases heq : Path.assume (.not g) p with
          | none => simp [heq] at he
          | some r =>
              simp [heq] at he
              cases he
      | inr he =>
          cases heq : Path.assume g p with
          | none => simp [heq] at he
          | some r =>
              simp [heq] at he
              cases he
              have hc := assume_some_cost _ p r heq
              omega
  | succ f ih =>
      intro p hp hf q hq
      simp only [loop, List.mem_append] at hq
      cases hq with
      | inl he =>
          cases heq : Path.assume (.not g) p with
          | none => simp [heq] at he
          | some r =>
              simp [heq] at he
              cases he
      | inr he =>
          cases heq : Path.assume g p with
          | none => simp [heq] at he
          | some r =>
              simp [heq] at he
              cases Decidable.em (p.cost < k) with
              | inl hlt =>
                  simp [hlt] at he
                  rw [mem_flatMap] at he
                  obtain ⟨x, hx, hy⟩ := he
                  cases x with
                  | done s =>
                      simp [Leaf.bind] at hy
                      have ht : (Path.tick r).cost ≤ k := by
                        have hc :=
                          assume_some_cost _ p r heq
                        have htc := tick_cost r
                        omega
                      have hb0 := hle _ ht _ hx
                      have hr : s.cost ≤ k := by
                        simpa [leafCost] using hb0
                      have hge0 := hge _ _ hx
                      simp [leafCost] at hge0
                      have hc :=
                        assume_some_cost _ p r heq
                      have htc := tick_cost r
                      have hf2 : k - s.cost ≤ f := by
                        omega
                      exact ih s hr hf2 q hy
                  | cut s =>
                      simp [Leaf.bind] at hy
                      cases hy
                      have ht : (Path.tick r).cost ≤ k := by
                        have hc :=
                          assume_some_cost _ p r heq
                        have htc := tick_cost r
                        omega
                      exact hcut _ ht s hx
              | inr hge =>
                  simp [hge] at he
                  cases he
                  have hc := assume_some_cost _ p r heq
                  omega

private theorem run_cutoffs_cost (k : Nat) :
    ∀ c p, p.cost ≤ k →
      ∀ q, Leaf.cut q ∈ run k c p → q.cost = k := by
  intro c
  induction c with
  | skip =>
      intro p _ q hq
      simp [run] at hq
      cases hq
  | assign x a =>
      intro p _ q hq
      simp [run] at hq
      cases hq
  | seq c1 c2 ih1 ih2 =>
      intro p hp q hq
      simp only [run] at hq
      rw [mem_flatMap] at hq
      obtain ⟨x, hx, hy⟩ := hq
      cases x with
      | done r =>
          simp [Leaf.bind] at hy
          have h1 := run_cost_le k c1 p hp x hx
          have hr : r.cost ≤ k := by
            simpa [leafCost] using h1
          exact ih2 r hr q hy
      | cut r =>
          simp [Leaf.bind] at hy
          cases hy
          exact ih1 p hp r hx
  | if_ g c1 c2 ih1 ih2 =>
      intro p hp q hq
      simp only [run, List.mem_append] at hq
      cases hq with
      | inl he =>
          cases heq : Path.assume g p with
          | none => simp [heq] at he
          | some r =>
              simp [heq] at he
              have hc := assume_some_cost _ p r heq
              have hr : r.cost ≤ k := by omega
              exact ih1 r hr q he
      | inr he =>
          cases heq : Path.assume (.not g) p with
          | none => simp [heq] at he
          | some r =>
              simp [heq] at he
              have hc := assume_some_cost _ p r heq
              have hr : r.cost ≤ k := by omega
              exact ih2 r hr q he
  | while g b ih =>
      intro p hp q hq
      simp only [run] at hq
      have hle : ∀ p, p.cost ≤ k →
          ∀ l ∈ (fun q => run k b q) p,
            leafCost l ≤ k := by
        intro p hp l hl
        exact run_cost_le k b p hp l hl
      have hge : ∀ p, ∀ l ∈ (fun q => run k b q) p,
          p.cost ≤ leafCost l := by
        intro p l hl
        exact run_cost_mono k b p l hl
      have hcut : ∀ p, p.cost ≤ k →
          ∀ q, Leaf.cut q ∈ (fun q => run k b q) p →
            q.cost = k := by
        intro p hp q hq
        exact ih p hp q hq
      have hf : k - p.cost ≤ k - p.cost := by omega
      exact loop_cutoffs_cost k g _ hle hge hcut _ p hp hf q hq

/-- Every cutoff has cost exactly the bound. -/
theorem cutoffs_cost (k : Nat) (c : Cmd) (q : Path) :
    q ∈ cutoffs k c → q.cost = k := by
  intro hq
  rw [mem_cutoffs] at hq
  simp only [leaves] at hq
  have hp : Path.init.cost ≤ k := by simp [Path.init]
  exact run_cutoffs_cost k c Path.init hp q hq

private theorem loop_sound (k : Nat) (g : BExp)
    (body : Path → List Leaf) (b : Cmd)
    (hbody : ∀ p q s0,
      Leaf.done q ∈ body p →
      q.guard.eval s0 = true →
      p.guard.eval s0 = true ∧
      ∃ n, q.cost = p.cost + n ∧
        BigStepCost b (Store.eval p.store s0)
          (Store.eval q.store s0) n) :
    ∀ fuel p q s0,
      Leaf.done q ∈ loop k g body fuel p →
      q.guard.eval s0 = true →
      p.guard.eval s0 = true ∧
      ∃ n, q.cost = p.cost + n ∧
        BigStepCost (.while g b)
          (Store.eval p.store s0)
          (Store.eval q.store s0) n := by
  intro fuel
  induction fuel with
  | zero =>
      intro p q s0 hq hguard
      simp only [loop, List.mem_append] at hq
      cases hq with
      | inl he =>
          cases heq : Path.assume (.not g) p with
          | none => simp [heq] at he
          | some r =>
              simp [heq] at he
              cases he
              have ht := assume_some_true _ p r s0 heq hguard
              obtain ⟨hg, hnot⟩ := ht
              have hgfalse :
                  g.eval (Store.eval p.store s0) = false := by
                simp at hnot ⊢
                exact hnot
              refine ⟨hg, 0, ?_, ?_⟩
              · have hc := assume_some_cost _ p r heq
                omega
              · have hs := assume_some_store _ p r heq
                have heq2 : Store.eval r.store s0 =
                    Store.eval p.store s0 := by
                  rw [hs]
                rw [heq2]
                exact BigStepCost.while_false hgfalse
      | inr he =>
          cases heq : Path.assume g p with
          | none => simp [heq] at he
          | some r =>
              simp [heq] at he
              cases he
  | succ f ih =>
      intro p q s0 hq hguard
      simp only [loop, List.mem_append] at hq
      cases hq with
      | inl he =>
          cases heq : Path.assume (.not g) p with
          | none => simp [heq] at he
          | some r =>
              simp [heq] at he
              cases he
              have ht := assume_some_true _ p r s0 heq hguard
              obtain ⟨hg, hnot⟩ := ht
              have hgfalse :
                  g.eval (Store.eval p.store s0) = false := by
                simp at hnot ⊢
                exact hnot
              refine ⟨hg, 0, ?_, ?_⟩
              · have hc := assume_some_cost _ p r heq
                omega
              · have hs := assume_some_store _ p r heq
                have heq2 : Store.eval r.store s0 =
                    Store.eval p.store s0 := by
                  rw [hs]
                rw [heq2]
                exact BigStepCost.while_false hgfalse
      | inr he =>
          cases heq : Path.assume g p with
          | none => simp [heq] at he
          | some r =>
              simp [heq] at he
              cases Decidable.em (p.cost < k) with
              | inl hlt =>
                  simp [hlt] at he
                  rw [mem_flatMap] at he
                  obtain ⟨x, hx, hy⟩ := he
                  cases x with
                  | done s =>
                      simp [Leaf.bind] at hy
                      obtain ⟨hsg, n2, hcost2, hcost⟩ :=
                        ih s q s0 hy hguard
                      obtain ⟨htg, n1, hcost1, hbodyc⟩ :=
                        hbody _ s s0 hx hsg
                      have hrg : r.guard.eval s0 = true := by
                        have htg2 : (Path.tick r).guard.eval s0 =
                            r.guard.eval s0 := by
                          simp [Path.tick]
                        rw [← htg2]
                        exact htg
                      have ht2 :=
                        assume_some_true _ p r s0 heq hrg
                      obtain ⟨hpg, hgtrue⟩ := ht2
                      refine ⟨hpg, 1 + n1 + n2, ?_, ?_⟩
                      · have hc :=
                          assume_some_cost _ p r heq
                        have htc := tick_cost r
                        omega
                      · have hs1 : Store.eval
                            (Path.tick r).store s0 =
                            Store.eval p.store s0 := by
                          have hts := tick_store r
                          have hss :=
                            assume_some_store _ p r heq
                          simp [hts, hss]
                        have hs2 : Store.eval r.store s0 =
                            Store.eval p.store s0 := by
                          rw [assume_some_store _ p r heq]
                        rw [hs1] at hbodyc
                        exact BigStepCost.while_true hgtrue
                          hbodyc hcost
                  | cut s =>
                      simp [Leaf.bind] at hy
                      cases hy
              | inr hge =>
                  simp [hge] at he
                  cases he

private theorem run_sound (k : Nat) :
    ∀ c p q s0,
      Leaf.done q ∈ run k c p →
      q.guard.eval s0 = true →
      p.guard.eval s0 = true ∧
      ∃ n, q.cost = p.cost + n ∧
        BigStepCost c (Store.eval p.store s0)
          (Store.eval q.store s0) n := by
  intro c
  induction c with
  | skip =>
      intro p q s0 hq hguard
      simp [run] at hq
      cases hq
      refine ⟨hguard, 0, by omega, ?_⟩
      exact BigStepCost.skip _
  | assign x a =>
      intro p q s0 hq hguard
      simp [run] at hq
      cases hq
      have hg : p.guard.eval s0 = true := by
        have h1 := assign_guard x a p
        simp [h1] at hguard ⊢
        exact hguard
      refine ⟨hg, 0, ?_, ?_⟩
      · have hc := assign_cost x a p
        omega
      · have he := assign_eval x a p s0
        rw [he]
        exact BigStepCost.assign _ _ _
  | seq c1 c2 ih1 ih2 =>
      intro p q s0 hq hguard
      simp only [run] at hq
      rw [mem_flatMap] at hq
      obtain ⟨x, hx, hy⟩ := hq
      cases x with
      | done r =>
          simp [Leaf.bind] at hy
          obtain ⟨hrg, n2, hc2, h2⟩ :=
            ih2 r q s0 hy hguard
          obtain ⟨hpg, n1, hc1, h1⟩ :=
            ih1 p r s0 hx hrg
          refine ⟨hpg, n1 + n2, by omega, ?_⟩
          exact BigStepCost.seq h1 h2
      | cut r =>
          simp [Leaf.bind] at hy
          cases hy
  | if_ g c1 c2 ih1 ih2 =>
      intro p q s0 hq hguard
      simp only [run, List.mem_append] at hq
      cases hq with
      | inl he =>
          cases heq : Path.assume g p with
          | none => simp [heq] at he
          | some r =>
              simp [heq] at he
              obtain ⟨hrg, n, hcn, h1⟩ :=
                ih1 r q s0 he hguard
              have ht :=
                assume_some_true _ p r s0 heq hrg
              obtain ⟨hpg, hgtrue⟩ := ht
              have hc := assume_some_cost _ p r heq
              refine ⟨hpg, n, by omega, ?_⟩
              have hs : Store.eval r.store s0 =
                  Store.eval p.store s0 := by
                rw [assume_some_store _ p r heq]
              rw [hs] at h1
              exact BigStepCost.if_true hgtrue h1
      | inr he =>
          cases heq : Path.assume (.not g) p with
          | none => simp [heq] at he
          | some r =>
              simp [heq] at he
              obtain ⟨hrg, n, hcn, h2⟩ :=
                ih2 r q s0 he hguard
              have ht :=
                assume_some_true _ p r s0 heq hrg
              obtain ⟨hpg, hnot⟩ := ht
              have hgfalse :
                  g.eval (Store.eval p.store s0) =
                    false := by
                simp at hnot ⊢
                exact hnot
              have hc := assume_some_cost _ p r heq
              refine ⟨hpg, n, by omega, ?_⟩
              have hs : Store.eval r.store s0 =
                  Store.eval p.store s0 := by
                rw [assume_some_store _ p r heq]
              rw [hs] at h2
              exact BigStepCost.if_false hgfalse h2
  | while g b ih =>
      intro p q s0 hq hguard
      simp only [run] at hq
      have hb : ∀ p q s0,
          Leaf.done q ∈ (fun q => run k b q) p →
          q.guard.eval s0 = true →
          p.guard.eval s0 = true ∧
          ∃ n, q.cost = p.cost + n ∧
            BigStepCost b (Store.eval p.store s0)
              (Store.eval q.store s0) n := by
        intro p q s0 h1 h2
        exact ih p q s0 h1 h2
      exact loop_sound k g _ b hb _ p q s0 hq hguard

/-- Every terminal path yields a counted run. -/
theorem paths_sound (k : Nat) (c : Cmd) (q : Path)
    (s : State) :
    q ∈ paths k c → q.guard.eval s = true →
      BigStepCost c s (Store.eval q.store s) q.cost ∧
        q.cost ≤ k := by
  intro hmem hguard
  rw [mem_paths] at hmem
  simp only [leaves] at hmem
  obtain ⟨_, n, hcost, hbig⟩ :=
    run_sound k c Path.init q s hmem hguard
  have hcost0 : Path.init.cost = 0 := by rfl
  have hstore0 : Store.eval Path.init.store s = s := by
    have h1 := Store.eval_init s
    simp [Path.init] at h1 ⊢
    exact h1
  rw [hcost0] at hcost
  rw [hstore0] at hbig
  have hqeq : q.cost = n := by omega
  subst hqeq
  have hp : Path.init.cost ≤ k := by
    rw [hcost0]
    omega
  have hle2 :=
    run_cost_le k c Path.init hp (Leaf.done q) hmem
  have hle : q.cost ≤ k := by
    simpa [leafCost] using hle2
  exact ⟨hbig, hle⟩

private theorem loop_mono (k : Nat) (g : BExp)
    (body : Path → List Leaf) :
    ∀ f1 f2, f1 ≤ f2 →
      ∀ p q, Leaf.done q ∈ loop k g body f1 p →
        Leaf.done q ∈ loop k g body f2 p := by
  intro f1
  induction f1 with
  | zero =>
      intro f2 _ p q hq
      simp only [loop, List.mem_append] at hq ⊢
      cases hq with
      | inl he =>
          exact Or.inl he
      | inr he =>
          cases heq : Path.assume g p with
          | none => simp [heq] at he
          | some r =>
              simp [heq] at he
              cases he
  | succ f1 ih =>
      intro f2 hf p q hq
      cases f2 with
      | zero =>
          have : False := by omega
          cases this
      | succ f2 =>
          have hle : f1 ≤ f2 := by omega
          simp only [loop, List.mem_append] at hq ⊢
          cases hq with
          | inl he =>
              exact Or.inl he
          | inr he =>
              refine Or.inr ?_
              cases heq : Path.assume g p with
              | none => simp [heq] at he ⊢; exact he
              | some r =>
                  simp [heq] at he ⊢
                  cases Decidable.em (p.cost < k) with
                  | inl hlt =>
                      simp [hlt] at he ⊢
                      rw [mem_flatMap] at he ⊢
                      obtain ⟨x, hx, hy⟩ := he
                      refine ⟨x, hx, ?_⟩
                      cases x with
                      | done s =>
                          simp [Leaf.bind] at hy ⊢
                          exact ih f2 hle s q hy
                      | cut s =>
                          simp [Leaf.bind] at hy
                          cases hy
                  | inr hge =>
                      simp [hge] at he ⊢
                      exact he

private theorem run_complete (k : Nat) (c : Cmd)
    (s f : State) (n : Nat)
    (h : BigStepCost c s f n) :
    ∀ p s0,
      Store.eval p.store s0 = s →
      p.guard.eval s0 = true →
      p.cost + n ≤ k →
      ∃ q, Leaf.done q ∈ run k c p ∧
        q.guard.eval s0 = true ∧
        Store.eval q.store s0 = f ∧
        q.cost = p.cost + n := by
  induction h with
  | skip s =>
      intro p s0 hs hg _
      refine ⟨p, by simp [run], hg, hs, by omega⟩
  | assign x a s =>
      intro p s0 hs hg _
      refine ⟨Path.assign x a p, by simp [run], ?_, ?_, ?_⟩
      · have h1 := assign_guard x a p
        simp [h1, hg]
      · have he := assign_eval x a p s0
        simp [hs] at he ⊢
        exact he
      · have hc := assign_cost x a p
        omega
  | seq h1 h2 ih1 ih2 =>
      intro p s0 hs hg hbk
      obtain ⟨r, hr1, hrg, hrs, hrc⟩ :=
        ih1 p s0 hs hg (by omega)
      obtain ⟨q, hq2, hqg, hqf, hqc⟩ :=
        ih2 r s0 hrs hrg (by omega)
      refine ⟨q, ?_, hqg, hqf, by omega⟩
      simp only [run]
      rw [mem_flatMap]
      exact ⟨Leaf.done r, hr1, by simpa [Leaf.bind] using hq2⟩
  | if_true hb h1 ih =>
      intro p s0 hs hg hbk
      have hgb : b.eval (Store.eval p.store s0) = true := by
        simp [hs, hb]
      obtain ⟨r, hr, hrg⟩ :=
        assume_some_of_true _ p s0 hg hgb
      obtain ⟨q, hq, hqg, hqf, hqc⟩ :=
        ih r s0
          (by simp [assume_some_store _ p r hr, hs])
          hrg
          (by have hc := assume_some_cost _ p r hr; omega)
      refine ⟨q, ?_, hqg, hqf, ?_⟩
      · simp only [run, List.mem_append]
        refine Or.inl ?_
        simp [hr, hq]
      · have hc := assume_some_cost _ p r hr
        omega
  | if_false hb h1 ih =>
      intro p s0 hs hg hbk
      have hnb :
          (.not b).eval (Store.eval p.store s0) = true := by
        simp [hs, hb]
      obtain ⟨r, hr, hrg⟩ :=
        assume_some_of_true _ p s0 hg hnb
      obtain ⟨q, hq, hqg, hqf, hqc⟩ :=
        ih r s0
          (by simp [assume_some_store _ p r hr, hs])
          hrg
          (by have hc := assume_some_cost _ p r hr; omega)
      refine ⟨q, ?_, hqg, hqf, ?_⟩
      · simp only [run, List.mem_append]
        refine Or.inr ?_
        simp [hr, hq]
      · have hc := assume_some_cost _ p r hr
        omega
  | while_false hb =>
      intro p s0 hs hg _
      have hnb :
          (.not b).eval (Store.eval p.store s0) = true := by
        simp [hs, hb]
      obtain ⟨r, hr, hrg⟩ :=
        assume_some_of_true _ p s0 hg hnb
      refine ⟨r, ?_, hrg, ?_, ?_⟩
      · simp only [run]
        simp only [loop, List.mem_append]
        refine Or.inl ?_
        simp [hr]
      · have hss := assume_some_store _ p r hr
        simp [hss, hs]
      · have hc := assume_some_cost _ p r hr
        omega
  | while_true hb h1 h2 ih1 ih2 =>
      intro p s0 hs hg hbk
      have hgb : b.eval (Store.eval p.store s0) = true := by
        simp [hs, hb]
      obtain ⟨r, hr, hrg⟩ :=
        assume_some_of_true _ p s0 hg hgb
      have hlt : p.cost < k := by omega
      have hfuel : ∃ f, k - p.cost = f + 1 := by
        refine ⟨k - p.cost - 1, by omega⟩
      obtain ⟨fuel, hfuel⟩ := hfuel
      have htrg : (Path.tick r).guard.eval s0 = true := by
        simp [Path.tick, hrg]
      have htrs : Store.eval (Path.tick r).store s0 = s := by
        simp [tick_store, assume_some_store _ p r hr, hs]
      have htrc : (Path.tick r).cost + _ ≤ k := by
        have hc := assume_some_cost _ p r hr
        have htc := tick_cost r
        omega
      obtain ⟨st, hst, hstg, hstf, hstc⟩ :=
        ih1 (Path.tick r) s0 htrs htrg htrc
      have hst_ge : (Path.tick r).cost ≤ st.cost := by
        have h1 := run_cost_mono k _ _ _ hst
        simpa [leafCost] using h1
      have hf2 : k - st.cost ≤ fuel := by
        have hc := assume_some_cost _ p r hr
        have htc := tick_cost r
        omega
      obtain ⟨q, hqrun, hqg, hqf, hqc⟩ :=
        ih2 st s0 hstf hstg (by omega)
      have hqloop : Leaf.done q ∈ loop k _ _ fuel st := by
        simp only [run] at hqrun
        exact loop_mono k _ _ _ _ hf2 st q hqrun
      refine ⟨q, ?_, hqg, hqf, ?_⟩
      · simp only [run]
        rw [hfuel]
        simp only [loop, List.mem_append]
        refine Or.inr ?_
        simp [hr, hlt]
        rw [mem_flatMap]
        exact ⟨Leaf.done st, hst,
          by simpa [Leaf.bind] using hqloop⟩
      · have hc := assume_some_cost _ p r hr
        have htc := tick_cost r
        omega

/-- Every bounded run appears as a terminal path. -/
theorem paths_complete (k : Nat) (c : Cmd) (s f : State)
    (n : Nat) :
    BigStepCost c s f n → n ≤ k →
      ∃ q, q ∈ paths k c ∧ q.guard.eval s = true ∧
        Store.eval q.store s = f ∧ q.cost = n := by
  intro hbk hle
  have hcost0 : Path.init.cost = 0 := by rfl
  have hstore0 : Store.eval Path.init.store s = s :=
    Store.eval_init s
  have hguard0 : Path.init.guard.eval s = true := by
    simp [Path.init]
  obtain ⟨q, hq, hqg, hqf, hqc⟩ :=
    run_complete k c s f n hbk Path.init s hstore0
      hguard0 (by omega)
  refine ⟨q, ?_, hqg, hqf, by omega⟩
  rw [mem_paths]
  simp [leaves, hq]

private theorem loop_cover (k : Nat) (g : BExp)
    (body : Path → List Leaf)
    (hbody : ∀ p s0, p.guard.eval s0 = true →
      ∃ q, (Leaf.done q ∈ body p ∨
        Leaf.cut q ∈ body p) ∧
        q.guard.eval s0 = true) :
    ∀ fuel p s0, p.guard.eval s0 = true →
      ∃ q, (Leaf.done q ∈ loop k g body fuel p ∨
        Leaf.cut q ∈ loop k g body fuel p) ∧
        q.guard.eval s0 = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro p s0 hg
      cases he : g.eval (Store.eval p.store s0) with
      | true =>
          obtain ⟨r, hr, hrg⟩ :=
            assume_some_of_true g p s0 hg he
          refine ⟨r, Or.inr ?_, hrg⟩
          simp only [loop, List.mem_append]
          refine Or.inr ?_
          simp [hr]
      | false =>
          have hnb : (.not g).eval
              (Store.eval p.store s0) = true := by
            simp [he]
          obtain ⟨r, hr, hrg⟩ :=
            assume_some_of_true _ p s0 hg hnb
          refine ⟨r, Or.inl ?_, hrg⟩
          simp only [loop, List.mem_append]
          refine Or.inl ?_
          simp [hr]
  | succ f ih =>
      intro p s0 hg
      cases he : g.eval (Store.eval p.store s0) with
      | true =>
          obtain ⟨r, hr, hrg⟩ :=
            assume_some_of_true g p s0 hg he
          cases Decidable.em (p.cost < k) with
          | inl hlt =>
              have htrg : (Path.tick r).guard.eval s0 = true := by
                simp [Path.tick, hrg]
              obtain ⟨s, hs, hsg⟩ := hbody _ s0 htrg
              cases hs with
              | inl hs1 =>
                  obtain ⟨q, hq, hqg⟩ := ih s s0 hsg
                  refine ⟨q, ?_, hqg⟩
                  cases hq with
                  | inl hq1 =>
                      refine Or.inr ?_
                      simp only [loop, List.mem_append] at ⊢
                      refine Or.inr ?_
                      simp [hr, hlt]
                      rw [mem_flatMap]
                      exact ⟨Leaf.done s, hs1,
                        by simpa [Leaf.bind] using hq1⟩
                  | inr hq1 =>
                      refine Or.inr ?_
                      simp only [loop, List.mem_append] at ⊢
                      refine Or.inr ?_
                      simp [hr, hlt]
                      rw [mem_flatMap]
                      exact ⟨Leaf.done s, hs1,
                        by simpa [Leaf.bind] using hq1⟩
              | inr hs1 =>
                  refine ⟨s, Or.inr ?_, hsg⟩
                  simp only [loop, List.mem_append]
                  refine Or.inr ?_
                  simp [hr, hlt]
                  rw [mem_flatMap]
                  exact ⟨Leaf.cut s, hs1, by simp [Leaf.bind]⟩
          | inr hge =>
              refine ⟨r, Or.inr ?_, hrg⟩
              simp only [loop, List.mem_append]
              refine Or.inr ?_
              simp [hr, hge]
      | false =>
          have hnb : (.not g).eval
              (Store.eval p.store s0) = true := by
            simp [he]
          obtain ⟨r, hr, hrg⟩ :=
            assume_some_of_true _ p s0 hg hnb
          refine ⟨r, Or.inl ?_, hrg⟩
          simp only [loop, List.mem_append]
          refine Or.inl ?_
          simp [hr]

private theorem run_cover (k : Nat) :
    ∀ c p s0, p.guard.eval s0 = true →
      ∃ q, (Leaf.done q ∈ run k c p ∨
        Leaf.cut q ∈ run k c p) ∧
        q.guard.eval s0 = true := by
  intro c
  induction c with
  | skip =>
      intro p s0 hg
      exact ⟨p, Or.inl (by simp [run]), hg⟩
  | assign x a =>
      intro p s0 hg
      refine ⟨Path.assign x a p, Or.inl ?_, ?_⟩
      · simp [run]
      · have h1 := assign_guard x a p
        simp [h1, hg]
  | seq c1 c2 ih1 ih2 =>
      intro p s0 hg
      obtain ⟨r, hr, hrg⟩ := ih1 p s0 hg
      cases hr with
      | inl hr1 =>
          obtain ⟨q, hq, hqg⟩ := ih2 r s0 hrg
          refine ⟨q, ?_, hqg⟩
          cases hq with
          | inl hq1 =>
              refine Or.inl ?_
              simp only [run]
              rw [mem_flatMap]
              exact ⟨Leaf.done r, hr1,
                by simpa [Leaf.bind] using hq1⟩
          | inr hq1 =>
              refine Or.inr ?_
              simp only [run]
              rw [mem_flatMap]
              exact ⟨Leaf.done r, hr1,
                by simpa [Leaf.bind] using hq1⟩
      | inr hr1 =>
          refine ⟨r, Or.inr ?_, hrg⟩
          simp only [run]
          rw [mem_flatMap]
          exact ⟨Leaf.cut r, hr1, by simp [Leaf.bind]⟩
  | if_ g c1 c2 ih1 ih2 =>
      intro p s0 hg
      cases he : g.eval (Store.eval p.store s0) with
      | true =>
          obtain ⟨r, hr, hrg⟩ :=
            assume_some_of_true g p s0 hg he
          obtain ⟨q, hq, hqg⟩ := ih1 r s0 hrg
          refine ⟨q, ?_, hqg⟩
          cases hq with
          | inl hq1 =>
              refine Or.inl ?_
              simp only [run, List.mem_append]
              refine Or.inl ?_
              simp [hr, hq1]
          | inr hq1 =>
              refine Or.inr ?_
              simp only [run, List.mem_append]
              refine Or.inl ?_
              simp [hr, hq1]
      | false =>
          have hnb : (.not g).eval
              (Store.eval p.store s0) = true := by
            simp [he]
          obtain ⟨r, hr, hrg⟩ :=
            assume_some_of_true _ p s0 hg hnb
          obtain ⟨q, hq, hqg⟩ := ih2 r s0 hrg
          refine ⟨q, ?_, hqg⟩
          cases hq with
          | inl hq1 =>
              refine Or.inl ?_
              simp only [run, List.mem_append]
              refine Or.inr ?_
              simp [hr, hq1]
          | inr hq1 =>
              refine Or.inr ?_
              simp only [run, List.mem_append]
              refine Or.inr ?_
              simp [hr, hq1]
  | while g b ih =>
      intro p s0 hg
      have hb : ∀ p s0, p.guard.eval s0 = true →
          ∃ q, (Leaf.done q ∈ (fun q => run k b q) p ∨
            Leaf.cut q ∈ (fun q => run k b q) p) ∧
            q.guard.eval s0 = true := by
        intro p s0 hg
        exact ih p s0 hg
      have hc := loop_cover k g _ hb _ p s0 hg
      simpa [run] using hc

/-- Every state satisfies some leaf guard. -/
theorem leaves_cover (k : Nat) (c : Cmd) (s : State) :
    ∃ q, (Leaf.done q ∈ leaves k c ∨
      Leaf.cut q ∈ leaves k c) ∧
      q.guard.eval s = true := by
  have hg : Path.init.guard.eval s = true := by
    simp [Path.init]
  have hc := run_cover k c Path.init s hg
  simpa [leaves] using hc

/-- No terminal cover implies cutoff and high cost. -/
theorem exhausted_of_no_path (k : Nat) (c : Cmd)
    (s : State) :
    (∀ q ∈ paths k c, q.guard.eval s = false) →
      (∃ q ∈ cutoffs k c, q.guard.eval s = true) ∧
        ∀ f n, BigStepCost c s f n → k < n := by
  intro hno
  obtain ⟨q, hq, hqg⟩ := leaves_cover k c s
  cases hq with
  | inl hdone =>
      have hmem : q ∈ paths k c := by
        rw [mem_paths]
        exact hdone
      have hf : q.guard.eval s = false := hno q hmem
      simp [hqg] at hf
  | inr hcut =>
      have hmem : q ∈ cutoffs k c := by
        rw [mem_cutoffs]
        exact hcut
      refine ⟨⟨q, hmem, hqg⟩, ?_⟩
      intro f n hcost
      cases Decidable.em (n ≤ k) with
      | inl hle =>
          obtain ⟨r, hr, hrg, _, _⟩ :=
            paths_complete k c s f n hcost hle
          have hf : r.guard.eval s = false := hno r hr
          simp [hrg] at hf
      | inr hle =>
          omega

end Cslib.IMP.Symbolic
