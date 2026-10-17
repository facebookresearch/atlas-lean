/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Tactic.Linarith
public import MathlibExt.Computability.TuringMachine.Program
public import CSLibExt.Computability.Complexity.DenseSAT

/-!
# A polynomial-time verifier machine for dense CNF-SAT

An explicit `Turing.FinTM2`, `Cslib.Complexity.DenseSAT.Verifier.tm`, that reads a formula `w`
and a candidate assignment `y` in the `w # y` form `pairEncode (w, y)` and outputs
`check w y`, in at most `2 (n + 5)²` steps for an input of length `n`
(`Cslib.Complexity.DenseSAT.Verifier.verifier`). With `sat_iff_check` this is the verifier
half of SAT ∈ NP.

The machine stashes `w` and `y` on two work stacks, restores them in order, and makes one
left-to-right pass over the formula bits: per clause it walks the assignment from a second stack,
records whether some literal is satisfied, and restores the assignment at the clause terminator.

formal-math's `MetaMathlibExt.ComplexityTheory.NP` feeds a verifier the canonical
`BitstringEncoding` of the pair (a `delimit`-framed formula followed by the certificate, each bit
written as three bits), not `w # y`; connecting the two needs an encoding-converter machine
composed in front of this one.
-/

@[expose] public section

namespace Cslib.Complexity.DenseSAT

namespace Verifier

open Turing Function MetaMathlibExt

/-- Work stacks: the input stack, a stash for the formula, and two stacks for the assignment. -/
inductive W | inp | F | A | B
  deriving DecidableEq
instance W.instFintypeEnumFix : Fintype W where
  elems := ⟨↑[W.inp, W.F, W.A, W.B], by decide⟩
  complete := fun x => by cases x <;> decide

/-- Work alphabet = the pair alphabet `Bool ⊕ Option Bool` (`inr none` is the separator `#`).
Formula and assignment bits are stored as `inl b`. -/
abbrev G := Bool ⊕ Option Bool

/-- The `w # y` input of the verifier: left-tagged formula bits `inl b`, the separator
`inr none`, then right-tagged certificate bits `inr (some b)`. -/
def pairEncode (p : List Bool × List Bool) : List G :=
  p.1.map Sum.inl ++ Sum.inr none :: p.2.map fun b => Sum.inr (some b)

/-- Stack alphabets: `none` is the output stack (alphabet `Bool`), `some w` a work stack. -/
@[reducible] def Γ : Option W → Type
  | none => Bool
  | some _ => G

/-- Labels. `c0 fl`/`c1 fl b` read the two bits of a token (`fl`: current clause satisfied),
`adv fl o` moves one assignment bit `B → A` (`o = some s`: literal token `1s`), `restore fl`
moves the used assignment bits back `A → B`. -/
inductive Lab
  | read1 | read2 | back1 | back2
  | c0 (fl : Bool) | c1 (fl b : Bool) | adv (fl : Bool) (o : Option Bool) | restore (fl : Bool)
  | drainI (ans : Bool) | drainA (ans : Bool) | drainB (ans : Bool) | finish (ans : Bool)
  deriving DecidableEq, Fintype

/-- Machine state: the last popped symbol. -/
abbrev St := Option G

/-- Statements of the verifier. -/
abbrev Stmt := TM2.Stmt Γ Lab St
/-- Configurations of the verifier. -/
abbrev Cfg := TM2.Cfg Γ Lab St

/-- Generic loop: pop `s`; while the popped symbol `x` has `g x = some y`, push `y` onto `t`
(nothing if `t = none`) and repeat; otherwise go to `next`. -/
def loop (s : W) (g : G → Option G) (t : Option W) (self next : Lab) : Stmt :=
  .pop (some s) (fun _ o => o) <|
    .branch (fun v => (v.bind g).isSome)
      (match t with
        | some t => .push (some t) (fun v => (v.bind g).getD (.inl false)) (.goto fun _ => self)
        | none => .goto fun _ => self)
      (.goto fun _ => next)

/-- Left symbols pass (and stop at `#`). -/
def gRead1 : G → Option G
  | .inl b => some (.inl b)
  | .inr _ => none

/-- Right symbols `inr (some b)` pass as `inl b`. -/
def gRead2 : G → Option G
  | .inr (some b) => some (.inl b)
  | _ => none

/-- The program. -/
def prog : Lab → Stmt
  | .read1 => loop .inp gRead1 (some .F) .read1 .read2
  | .read2 => loop .inp gRead2 (some .A) .read2 .back1
  | .back1 => loop .F some (some .inp) .back1 .back2
  | .back2 => loop .A some (some .B) .back2 (.c0 false)
  | .c0 fl => .pop (some .inp) (fun _ o => o) <| .goto fun v => match v with
      | some (.inl b) => .c1 fl b
      | _ => .drainI true
  | .c1 fl false => .pop (some .inp) (fun _ o => o) <| .goto fun v => match v with
      | some (.inl false) => .restore fl
      | some (.inl true) => .adv fl none
      | _ => .drainI true
  | .c1 fl true => .pop (some .inp) (fun _ o => o) <| .goto fun v => match v with
      | some (.inl s) => .adv fl (some s)
      | _ => .drainI true
  | .adv fl o => .pop (some .B) (fun _ o => o) <|
      .branch (fun v => v.isSome)
        (.push (some .A) (fun v => v.getD (.inl false)) <|
          .goto fun v => .c0 (fl || decide (v = o.map fun s => .inl (!s))))
        (.goto fun _ => .c0 fl)
  | .restore fl => loop .A some (some .B) (.restore fl) (if fl then .c0 false else .drainI false)
  | .drainI ans => loop .inp some none (.drainI ans) (.drainA ans)
  | .drainA ans => loop .A some none (.drainA ans) (.drainB ans)
  | .drainB ans => loop .B some none (.drainB ans) (.finish ans)
  | .finish ans => .push none (fun _ => ans) <| .load (fun _ => none) .halt

/-- The verifier as a `FinTM2`. Input stack `some inp`, output stack `none`. -/
def tm : FinTM2 where
  K := Option W
  k₀ := some .inp
  k₁ := none
  Γ := Γ
  Λ := Lab
  main := .read1
  σ := St
  initialState := none
  Γk₀Fin := (inferInstance : Fintype G)
  m := prog

/-! ### Configurations -/

/-- Assemble all stacks from the (non-dependent) work stacks `V` and the output `o`. -/
def stk (V : W → List G) (o : List Bool) : ∀ k, List (Γ k)
  | none => o
  | some w => V w

theorem update_stk_some (V : W → List G) (o : List Bool) (w : W) (l : List G) :
    update (stk V o) (some w) l = stk (update V w l) o := by
  funext k
  rcases k with _ | k
  · rw [update_of_ne (by simp)]; rfl
  · by_cases h : k = w
    · subst h; simp [stk]
    · rw [update_of_ne (by simpa using h)]
      simp [stk, update_of_ne h]

theorem update_stk_none (V : W → List G) (o l : List Bool) :
    update (stk V o) none l = stk V l := by
  funext k
  rcases k with _ | k
  · simp [stk]
  · rw [update_of_ne (by simp)]; rfl

/-- Work stacks from four lists. -/
def mkV (i f a b : List G) : W → List G
  | .inp => i
  | .F => f
  | .A => a
  | .B => b

@[simp] theorem update_mkV_inp (i f a b x : List G) :
    update (mkV i f a b) .inp x = mkV x f a b := by
  funext k; cases k <;> rfl
@[simp] theorem update_mkV_F (i f a b x : List G) :
    update (mkV i f a b) .F x = mkV i x a b := by
  funext k; cases k <;> rfl
@[simp] theorem update_mkV_A (i f a b x : List G) :
    update (mkV i f a b) .A x = mkV i f x b := by
  funext k; cases k <;> rfl
@[simp] theorem update_mkV_B (i f a b x : List G) :
    update (mkV i f a b) .B x = mkV i f a x := by
  funext k; cases k <;> rfl

/-- Result of pushing `ys` one at a time onto `t` (nothing if `t = none`). -/
def pushAll : Option W → List G → (W → List G) → W → List G
  | none, _, V => V
  | some t, ys, V => update V t (ys.reverse ++ V t)

/-- The generic loop runs `|xs| + 1` steps, consuming `xs` and the stopping symbol. -/
theorem loop_run (s : W) (g : G → Option G) (t : Option W) (self next : Lab)
    (hp : prog self = loop s g t self next) (hst : t ≠ some s) (o : List Bool) :
    ∀ (xs ys rest : List G) (v : St) (V : W → List G),
      xs.map g = ys.map some → rest.head?.bind g = none → V s = xs ++ rest →
      TM2Program.Run prog (xs.length + 1) ⟨some self, v, stk V o⟩
        ⟨some next, rest.head?, stk (pushAll t ys (update V s rest.tail)) o⟩ := by
  intro xs
  induction xs with
  | nil =>
      intro ys rest v V hg hr hV
      obtain rfl : ys = [] := by simpa using hg.symm
      refine TM2Program.Run.head ?_ (TM2Program.Run.zero _)
      simp only [TM2.step, hp, loop, TM2.stepAux, show stk V o (some s) = V s from rfl, hV,
        List.nil_append, hr, Option.isSome_none, Bool.cond_false]
      rw [update_stk_some]
      rcases t with _ | t
      · rfl
      · simp [pushAll]
  | cons x xs ih =>
      intro ys rest v V hg hr hV
      rcases ys with _ | ⟨y, ys⟩
      · simp at hg
      simp only [List.map_cons, List.cons.injEq] at hg
      obtain ⟨hxy, hg⟩ := hg
      rcases t with _ | t
      · have key := ih ys rest (some x) (update V s (xs ++ rest)) hg hr (by simp)
        simp only [pushAll, update_idem] at key ⊢
        refine TM2Program.Run.head ?_ key
        simp only [TM2.step, hp, loop, TM2.stepAux, show stk V o (some s) = V s from rfl, hV,
          List.cons_append, List.head?_cons, List.tail_cons, Option.bind_some, hxy,
          Option.isSome_some, Bool.cond_true]
        rw [update_stk_some]
      · have hts : t ≠ s := fun h => hst (by rw [h])
        have key := ih ys rest (some x) (update (update V s (xs ++ rest)) t (y :: V t)) hg hr
          (by rw [update_of_ne (Ne.symm hts)]; simp)
        have hfin : pushAll (some t) ys
              (update (update (update V s (xs ++ rest)) t (y :: V t)) s rest.tail) =
            pushAll (some t) (y :: ys) (update V s rest.tail) := by
          funext k
          simp only [pushAll]
          by_cases hk : k = t
          · subst hk; simp [update_of_ne hts]
          · by_cases hk' : k = s
            · subst hk'; simp [update_of_ne hk]
            · simp [update_of_ne hk, update_of_ne hk']
        rw [hfin] at key
        refine TM2Program.Run.head ?_ key
        simp only [TM2.step, hp, loop, TM2.stepAux, show stk V o (some s) = V s from rfl, hV,
          List.cons_append, List.head?_cons, List.tail_cons, Option.bind_some, hxy,
          Option.isSome_some, Bool.cond_true, Option.getD_some]
        rw [update_stk_some, show stk (update V s (xs ++ rest)) o (some t) =
          update V s (xs ++ rest) t from rfl, update_stk_some, update_of_ne hts]

/-! ### Cleanup and output -/

/-- Draining `inp`, `A`, `B` and reaching `finish ans`. -/
theorem drain_run (ans : Bool) (i a b : List G) (v : St) :
    TM2Program.Run prog (i.length + a.length + b.length + 3)
      ⟨some (.drainI ans), v, stk (mkV i [] a b) []⟩
      ⟨some (.finish ans), none, stk (mkV [] [] [] []) []⟩ := by
  have h₁ := loop_run .inp some none (.drainI ans) (.drainA ans) rfl (by simp) [] i i [] v
    (mkV i [] a b) rfl rfl (by simp [mkV])
  have h₂ := loop_run .A some none (.drainA ans) (.drainB ans) rfl (by simp) [] a a [] none
    (mkV [] [] a b) rfl rfl (by simp [mkV])
  have h₃ := loop_run .B some none (.drainB ans) (.finish ans) rfl (by simp) [] b b [] none
    (mkV [] [] [] b) rfl rfl (by simp [mkV])
  simp only [pushAll, List.tail_nil, List.head?_nil, update_mkV_inp, update_mkV_A,
    update_mkV_B] at h₁ h₂ h₃
  exact (h₁.trans (h₂.trans h₃)).of_eq (by omega)

theorem finish_run (ans : Bool) :
    TM2Program.Run prog 1 ⟨some (.finish ans), none, stk (mkV [] [] [] []) []⟩
      ⟨none, none, stk (mkV [] [] [] []) [ans]⟩ := by
  refine TM2Program.Run.head ?_ (TM2Program.Run.zero _)
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_none]
  rfl

/-! ### The main scan -/

/-- Bits stored on a work stack. -/
def enc (l : List Bool) : List G := l.map Sum.inl

@[simp] theorem enc_nil : enc [] = [] := rfl
@[simp] theorem enc_cons (b : Bool) (l : List Bool) : enc (b :: l) = .inl b :: enc l := rfl
@[simp] theorem length_enc (l : List Bool) : (enc l).length = l.length := List.length_map _

theorem step_c0_nil (fl : Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c0 fl), v, stk (mkV [] [] a b) []⟩ =
      some ⟨some (.drainI true), none, stk (mkV [] [] a b) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_c0_cons (fl x : Bool) (r : List Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c0 fl), v, stk (mkV (enc (x :: r)) [] a b) []⟩ =
      some ⟨some (.c1 fl x), some (.inl x), stk (mkV (enc r) [] a b) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_c1_nil (fl x : Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c1 fl x), v, stk (mkV [] [] a b) []⟩ =
      some ⟨some (.drainI true), none, stk (mkV [] [] a b) []⟩ := by
  cases x <;>
  · simp only [TM2.step, prog, TM2.stepAux]
    rw [update_stk_some]
    simp [stk, mkV]

theorem step_c1_ff (fl : Bool) (r : List Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c1 fl false), v, stk (mkV (enc (false :: r)) [] a b) []⟩ =
      some ⟨some (.restore fl), some (.inl false), stk (mkV (enc r) [] a b) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_c1_ft (fl : Bool) (r : List Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c1 fl false), v, stk (mkV (enc (true :: r)) [] a b) []⟩ =
      some ⟨some (.adv fl none), some (.inl true), stk (mkV (enc r) [] a b) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_c1_t (fl s : Bool) (r : List Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c1 fl true), v, stk (mkV (enc (s :: r)) [] a b) []⟩ =
      some ⟨some (.adv fl (some s)), some (.inl s), stk (mkV (enc r) [] a b) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_adv_nil (fl : Bool) (o : Option Bool) (i a : List G) (v : St) :
    TM2.step prog ⟨some (.adv fl o), v, stk (mkV i [] a []) []⟩ =
      some ⟨some (.c0 fl), none, stk (mkV i [] a []) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_adv_cons (fl : Bool) (o : Option Bool) (x : Bool) (i a : List G) (bs : List Bool)
    (v : St) :
    TM2.step prog ⟨some (.adv fl o), v, stk (mkV i [] a (enc (x :: bs))) []⟩ =
      some ⟨some (.c0 (fl || decide (some (Sum.inl x : G) = o.map fun s => .inl (!s)))),
        some (.inl x), stk (mkV i [] (.inl x :: a) (enc bs)) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  simp [stk, mkV, update_stk_some]

theorem step_adv_none_cons (fl x : Bool) (i a : List G) (bs : List Bool) (v : St) :
    TM2.step prog ⟨some (.adv fl none), v, stk (mkV i [] a (enc (x :: bs))) []⟩ =
      some ⟨some (.c0 fl), some (.inl x), stk (mkV i [] (.inl x :: a) (enc bs)) []⟩ := by
  rw [step_adv_cons]; simp

theorem step_adv_some_cons (fl s x : Bool) (i a : List G) (bs : List Bool) (v : St) :
    TM2.step prog ⟨some (.adv fl (some s)), v, stk (mkV i [] a (enc (x :: bs))) []⟩ =
      some ⟨some (.c0 (fl || x == !s)), some (.inl x),
        stk (mkV i [] (.inl x :: a) (enc bs)) []⟩ := by
  rw [step_adv_cons]; cases x <;> cases s <;> simp

/-- Number of steps of the main scan (mirrors `evalCNF`). -/
def T : List Bool → List Bool → List Bool → Bool → ℕ
  | false :: false :: r, bs, as, fl =>
      as.length + 3 +
        if fl then T r (as.reverse ++ bs) [] false else r.length + (as.length + bs.length) + 3
  | false :: true :: r, [], as, fl => 3 + T r [] as fl
  | false :: true :: r, x :: bs, as, fl => 3 + T r bs (x :: as) fl
  | true :: _ :: r, [], as, fl => 3 + T r [] as fl
  | true :: s :: r, x :: bs, as, fl => 3 + T r bs (x :: as) (fl || x == !s)
  | r, bs, as, _ => r.length + as.length + bs.length + 4

theorem T_nil (bs as : List Bool) (fl : Bool) : T [] bs as fl = 0 + as.length + bs.length + 4 :=
  rfl

theorem T_single (b : Bool) (bs as : List Bool) (fl : Bool) :
    T [b] bs as fl = 1 + as.length + bs.length + 4 := by
  cases b <;> rfl

theorem enc_reverse_append (as bs : List Bool) :
    (enc as).reverse ++ enc bs = enc (as.reverse ++ bs) := by
  simp [enc]

/-- The main scan computes `evalCNF` and ends, all work stacks empty, at `finish`. -/
theorem scan (r bs as : List Bool) (fl : Bool) (v : St) :
    TM2Program.Run prog (T r bs as fl) ⟨some (.c0 fl), v, stk (mkV (enc r) [] (enc as) (enc bs)) []⟩
      ⟨some (.finish (evalCNF r bs as fl)), none, stk (mkV [] [] [] []) []⟩ := by
  induction r, bs, as, fl using evalCNF.induct generalizing v with
  | case1 r bs as fl ih =>
      have hR := loop_run .A some (some .B) (.restore fl)
        (if fl then .c0 false else .drainI false) rfl (by simp) [] (enc as) (enc as) []
        (some (.inl false)) (mkV (enc r) [] (enc as) (enc bs)) rfl rfl (by simp [mkV])
      simp only [pushAll, List.tail_nil, List.head?_nil, update_mkV_A, mkV, update_mkV_B,
        enc_reverse_append] at hR
      have h₀ := step_c0_cons fl false (false :: r) (enc as) (enc bs) v
      have h₁ := step_c1_ff fl r (enc as) (enc bs) (some (.inl false))
      cases fl
      · have hD := drain_run false (enc r) [] (enc (as.reverse ++ bs)) none
        exact (TM2Program.Run.head h₀ (TM2Program.Run.head h₁ (hR.trans hD))).of_eq
          (by simp [T]; omega)
      · have hI := ih none
        exact (TM2Program.Run.head h₀ (TM2Program.Run.head h₁ (hR.trans hI))).of_eq
          (by simp [T]; omega)
  | case2 r as fl ih =>
      exact (TM2Program.Run.head (step_c0_cons fl false (true :: r) (enc as) [] v)
        (TM2Program.Run.head (step_c1_ft fl r (enc as) [] _)
          (TM2Program.Run.head (step_adv_nil fl none (enc r) (enc as) _) (ih none)))).of_eq
        (by simp [T]; omega)
  | case3 r x bs as fl ih =>
      exact (TM2Program.Run.head (step_c0_cons fl false (true :: r) (enc as) (enc (x :: bs)) v)
        (TM2Program.Run.head (step_c1_ft fl r (enc as) (enc (x :: bs)) _)
          (TM2Program.Run.head (step_adv_none_cons fl x (enc r) (enc as) bs _) (ih _)))).of_eq
        (by simp [T]; omega)
  | case4 s r as fl ih =>
      exact (TM2Program.Run.head (step_c0_cons fl true (s :: r) (enc as) [] v)
        (TM2Program.Run.head (step_c1_t fl s r (enc as) [] _)
          (TM2Program.Run.head (step_adv_nil fl (some s) (enc r) (enc as) _) (ih none)))).of_eq
        (by simp [T]; omega)
  | case5 s r x bs as fl ih =>
      exact (TM2Program.Run.head (step_c0_cons fl true (s :: r) (enc as) (enc (x :: bs)) v)
        (TM2Program.Run.head (step_c1_t fl s r (enc as) (enc (x :: bs)) _)
          (TM2Program.Run.head (step_adv_some_cons fl s x (enc r) (enc as) bs _) (ih _)))).of_eq
        (by simp [T]; omega)
  | case6 r bs as fl h₁ h₂ h₃ h₄ h₅ =>
      rcases r with _ | ⟨b, _ | ⟨b', r⟩⟩
      · have hD := drain_run true [] (enc as) (enc bs) none
        have h := TM2Program.Run.head (step_c0_nil fl (enc as) (enc bs) v) hD
        rw [T_nil]
        exact h.of_eq (by simp)
      · have hD := drain_run true [] (enc as) (enc bs) none
        have h := TM2Program.Run.head (step_c0_cons fl b [] (enc as) (enc bs) v)
          (TM2Program.Run.head (step_c1_nil fl b (enc as) (enc bs) (some (.inl b))) hD)
        rw [T_single]
        have h' := h.of_eq (m := 1 + as.length + bs.length + 4) (by simp; omega)
        cases b <;> exact h'
      · exfalso
        rcases bs with _ | ⟨x, bs⟩ <;> cases b <;> cases b' <;>
          first
          | exact h₁ r rfl
          | exact h₂ r rfl rfl
          | exact h₃ r x bs rfl rfl
          | exact h₄ _ r rfl rfl
          | exact h₅ _ r x bs rfl rfl

theorem T_le (r bs as : List Bool) (fl : Bool) :
    T r bs as fl ≤ (r.length + 1) * (bs.length + as.length + 5) := by
  induction r, bs, as, fl using evalCNF.induct with
  | case1 r bs as fl ih =>
      cases fl
      · simp [T]; nlinarith
      · simp [T] at ih ⊢; nlinarith
  | case2 r as fl ih => simp [T] at ih ⊢; nlinarith
  | case3 r x bs as fl ih => simp [T] at ih ⊢; nlinarith
  | case4 s r as fl ih => simp [T] at ih ⊢; nlinarith
  | case5 s r x bs as fl ih => simp [T] at ih ⊢; nlinarith
  | case6 r bs as fl h₁ h₂ h₃ h₄ h₅ =>
      rcases r with _ | ⟨b, _ | ⟨b', r⟩⟩
      · rw [T_nil]; simp; nlinarith
      · rw [T_single]; simp; nlinarith
      · exfalso
        rcases bs with _ | ⟨x, bs⟩ <;> cases b <;> cases b' <;>
          first
          | exact h₁ r rfl
          | exact h₂ r rfl rfl
          | exact h₃ r x bs rfl rfl
          | exact h₄ _ r rfl rfl
          | exact h₅ _ r x bs rfl rfl

/-! ### Splitting the input `w # y` -/

/-- Right-tagged certificate bits, as they appear in the pair encoding. -/
def encR (y : List Bool) : List G := y.map fun b => .inr (some b)

/-- Phases 1–4: stash `w`, stash `y`, and restore both in order (`w` on `inp`, `y` on `B`). -/
theorem prefix_run (w y : List Bool) :
    TM2Program.Run prog (w.length + 1 + (y.length + 1) + (w.length + 1) + (y.length + 1))
      ⟨some .read1, none, stk (mkV (enc w ++ .inr none :: encR y) [] [] []) []⟩
      ⟨some (.c0 false), none, stk (mkV (enc w) [] [] (enc y)) []⟩ := by
  have h₁ := loop_run .inp gRead1 (some .F) .read1 .read2 rfl (by simp) [] (enc w) (enc w)
    (.inr none :: encR y) none (mkV (enc w ++ .inr none :: encR y) [] [] [])
    (by simp [enc, gRead1]) rfl rfl
  have h₂ := loop_run .inp gRead2 (some .A) .read2 .back1 rfl (by simp) [] (encR y) (enc y) []
    (some (.inr none)) (mkV (encR y) (enc w).reverse [] []) (by simp [encR, enc, gRead2]) rfl
    (by simp [mkV])
  have h₃ := loop_run .F some (some .inp) .back1 .back2 rfl (by simp) [] (enc w).reverse
    (enc w).reverse [] none (mkV [] (enc w).reverse (enc y).reverse []) rfl rfl (by simp [mkV])
  have h₄ := loop_run .A some (some .B) .back2 (.c0 false) rfl (by simp) [] (enc y).reverse
    (enc y).reverse [] none (mkV (enc w) [] (enc y).reverse []) rfl rfl (by simp [mkV])
  simp only [pushAll, List.tail_cons, List.tail_nil, List.head?_cons, List.head?_nil,
    update_mkV_inp, update_mkV_F, update_mkV_A, update_mkV_B, mkV, List.append_nil,
    List.reverse_reverse] at h₁ h₂ h₃ h₄
  exact (((h₁.trans h₂).trans h₃).trans h₄).of_eq (by simp [encR])

theorem initList_tm (l : List G) :
    initList tm l = ⟨some .read1, none, stk (mkV l [] [] []) []⟩ := by
  simp only [initList]
  congr 1
  funext k
  rcases k with _ | k
  · rfl
  · cases k <;> rfl

theorem haltList_tm (l : List Bool) :
    haltList tm l = ⟨none, none, stk (mkV [] [] [] []) l⟩ := by
  simp only [haltList]
  congr 1
  funext k
  rcases k with _ | k
  · rfl
  · cases k <;> rfl

/-- Exact number of steps on `w # y`. -/
def totalSteps (w y : List Bool) : ℕ :=
  w.length + 1 + (y.length + 1) + (w.length + 1) + (y.length + 1) + T w y [] false + 1

/-- Time bound `2 (n + 5)²` in the length `n = |w| + 1 + |y|` of `w # y`. -/
noncomputable def time : Polynomial ℕ :=
  Polynomial.C 2 * (Polynomial.X + Polynomial.C 5) ^ 2

/-- The verifier decides `check` on `w # y` in polynomial time. -/
noncomputable def verifier :
    TM2ComputableInPolyTime pairEncode (fun b : Bool => [b]) (fun p => check p.1 p.2) where
  tm := tm
  inputAlphabet := Equiv.refl G
  outputAlphabet := Equiv.refl Bool
  time := time
  outputsFun := fun p => by
    obtain ⟨w, y⟩ := p
    have hin : List.map (Equiv.refl G).invFun (pairEncode (w, y)) =
        enc w ++ .inr none :: encR y := by
      simp [pairEncode, enc, encR]
    have hlen : (pairEncode (w, y)).length = w.length + 1 + y.length := by
      simp only [pairEncode, List.length_append, List.length_map, List.length_cons]
      omega
    have hrun := ((prefix_run w y).trans (scan w y [] false none)).trans (finish_run (check w y))
    unfold TM2OutputsInTime
    refine { steps := totalSteps w y, evals_in_steps := ?_, steps_le_m := ?_ }
    · change (flip bind (TM2.step prog))^[_] (some (initList tm _)) =
        Option.map (haltList tm) (some _)
      erw [hin, initList_tm, Option.map_some, haltList_tm]
      exact hrun
    · rw [hlen, totalSteps]
      have hT := T_le w y [] false
      simp only [time, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_add, Polynomial.eval_X, List.length_nil] at hT ⊢
      nlinarith

end Verifier

end Cslib.Complexity.DenseSAT
