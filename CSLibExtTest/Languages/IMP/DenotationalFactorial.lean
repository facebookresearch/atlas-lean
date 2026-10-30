/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.IMP.Denotational
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section

namespace Cslib.IMP.DenotationalFactorialTests

/-- The IMP factorial program: variable `0` holds the input (counted down to
`0`) and variable `1` holds the accumulator, ending with `(s 0)!`. Copied
from `CSLibExtTest.Languages.IMP.EquivalenceTests`. -/
def factorial : Cmd :=
  .seq (.assign 1 (.const 1))
    (.while (.not (.eq (.var 0) (.const 0)))
      (.seq (.assign 1 (.mul (.var 1) (.var 0)))
        (.assign 0 (.sub (.var 0) (.const 1)))))

def factorialGuard : BExp :=
  .not (.eq (.var 0) (.const 0))

def factorialBody : Cmd :=
  .seq (.assign 1 (.mul (.var 1) (.var 0)))
    (.assign 0 (.sub (.var 0) (.const 1)))

def factorialLoop : Cmd :=
  .while factorialGuard factorialBody

/-- The state reached from `t` by the factorial loop: variable `0` is `0`,
variable `1` is `t 1 * (t 0)!`, and every other variable is unchanged. The
loop invariant behind this closed form is that `(var 1) * (var 0)!` is
constant across iterations. -/
def factFinal (t : State) : State :=
  Function.update (Function.update t 1 (t 1 * Nat.factorial (t 0))) 0 0

theorem factorialGuard_eval_true {t : State} :
    factorialGuard.eval t = true ↔ t 0 ≠ 0 := by
  by_cases h : t 0 = 0 <;> simp [factorialGuard, BExp.eval, AExp.eval, h]

theorem factorialGuard_eval_false {t : State} :
    factorialGuard.eval t = false ↔ t 0 = 0 := by
  by_cases h : t 0 = 0 <;> simp [factorialGuard, BExp.eval, AExp.eval, h]

theorem update_one_zero_eq {a b : State} {x : Nat}
    (h : ∀ k, k ≠ 0 → k ≠ 1 → a k = b k) :
    Function.update (Function.update a 1 x) 0 0 =
      Function.update (Function.update b 1 x) 0 0 := by
  funext k
  by_cases hk0 : k = 0
  · subst hk0
    simp [Function.update]
  · by_cases hk1 : k = 1
    · subst hk1
      simp [Function.update]
    · simp [Function.update, hk0, hk1, h k hk0 hk1]

theorem factFinal_self {t : State} (ht : t 0 = 0) : factFinal t = t := by
  have hval : t 1 * Nat.factorial (t 0) = t 1 := by
    rw [ht]
    simp
  funext k
  by_cases hk0 : k = 0
  · subst hk0
    simp [factFinal, Function.update, ht]
  · by_cases hk1 : k = 1
    · subst hk1
      simp [factFinal, Function.update, hval]
    · simp [factFinal, Function.update, hk0, hk1]

theorem factFinal_body {s : State} (hs : s 0 ≠ 0) :
    factFinal (Function.update (Function.update s 1 (s 1 * s 0)) 0 (s 0 - 1)) =
      factFinal s := by
  set m := Function.update (Function.update s 1 (s 1 * s 0)) 0 (s 0 - 1) with hm
  have hm0 : m 0 = s 0 - 1 := by
    simp [hm]
  have hm1 : m 1 = s 1 * s 0 := by
    simp [hm, Function.update]
  have hmk : ∀ k, k ≠ 0 → k ≠ 1 → m k = s k := by
    intro k hk0 hk1
    simp [hm, Function.update, hk0, hk1]
  have hfact : Nat.factorial (s 0) = s 0 * Nat.factorial (s 0 - 1) := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hs
    rw [hk]
    simp [Nat.factorial_succ]
  have hval : m 1 * Nat.factorial (m 0) = s 1 * Nat.factorial (s 0) := by
    rw [hm1, hm0, hfact]
    exact Nat.mul_assoc _ _ _
  simp only [factFinal]
  rw [hval]
  exact update_one_zero_eq hmk

theorem factFinal_init {s : State} :
    factFinal (Function.update s 1 1) =
      Function.update (Function.update s 1 (Nat.factorial (s 0))) 0 0 := by
  set m := Function.update s 1 1 with hm
  have hm0 : m 0 = s 0 := by
    simp [hm]
  have hm1 : m 1 = 1 := by
    simp [hm]
  have hmk : ∀ k, k ≠ 0 → k ≠ 1 → m k = s k := by
    intro k hk0 hk1
    simp [hm, hk1]
  have hval : m 1 * Nat.factorial (m 0) = Nat.factorial (s 0) := by
    rw [hm1, hm0]
    simp
  simp only [factFinal]
  rw [hval]
  exact update_one_zero_eq hmk

theorem factorialBody_denote {t m : State} :
    Denote factorialBody t m ↔
      m = Function.update (Function.update t 1 (t 1 * t 0)) 0 (t 0 - 1) := by
  simp only [factorialBody]
  constructor
  · intro h
    rw [Denote.seq_iff] at h
    obtain ⟨mid, h1, h2⟩ := h
    rw [Denote.assign_iff] at h1
    subst h1
    rw [Denote.assign_iff] at h2
    have e1 : (AExp.mul (.var 1) (.var 0)).eval t = t 1 * t 0 := by
      simp [AExp.eval]
    have e2 : (AExp.sub (.var 0) (.const 1)).eval
        (Function.update t 1 (t 1 * t 0)) = t 0 - 1 := by
      simp [AExp.eval, Function.update]
    rw [e1, e2] at h2
    exact h2
  · rintro rfl
    rw [Denote.seq_iff]
    refine ⟨Function.update t 1 (t 1 * t 0), ?_, ?_⟩
    · rw [Denote.assign_iff]
      simp [AExp.eval]
    · rw [Denote.assign_iff]
      simp [AExp.eval, Function.update]

/-- Soundness of the loop characterization, by Park induction
(`Denote.while_ind`) with the closed form `factFinal` as the invariant
relation. -/
theorem factorialLoop_denote_imp {t t' : State}
    (h : Denote factorialLoop t t') : t' = factFinal t := by
  refine Denote.while_ind (b := factorialGuard) (c := factorialBody)
    (P := fun s s' => s' = factFinal s) ?_ h
  intro s s' hstep
  rcases hstep with ⟨hfalse, rfl⟩ | ⟨htrue, m, hbody, hloop⟩
  · exact (factFinal_self (factorialGuard_eval_false.mp hfalse)).symm
  · have hs : s 0 ≠ 0 := factorialGuard_eval_true.mp htrue
    rw [factorialBody_denote] at hbody
    rw [hloop, hbody]
    exact factFinal_body hs

/-- Completeness of the loop characterization, by induction on `t 0` using
the loop unfolding equation `Denote.while_iff`. -/
theorem factorialLoop_denote_of :
    ∀ (n : Nat) (t : State), t 0 = n → Denote factorialLoop t (factFinal t) := by
  intro n
  induction n with
  | zero =>
      intro t ht
      show Denote (Cmd.while factorialGuard factorialBody) t (factFinal t)
      rw [Denote.while_iff]
      exact Or.inl ⟨factorialGuard_eval_false.mpr ht, factFinal_self ht⟩
  | succ n ih =>
      intro t ht
      show Denote (Cmd.while factorialGuard factorialBody) t (factFinal t)
      rw [Denote.while_iff]
      refine Or.inr ⟨?_, Function.update (Function.update t 1 (t 1 * t 0)) 0 (t 0 - 1),
        ?_, ?_⟩
      · apply factorialGuard_eval_true.mpr
        simp [ht]
      · exact factorialBody_denote.mpr rfl
      · have hm0 : (Function.update (Function.update t 1 (t 1 * t 0)) 0 (t 0 - 1)) 0
            = n := by
          simp [Function.update, ht]
        have hne : t 0 ≠ 0 := by
          simp [ht]
        rw [← factFinal_body hne]
        exact ih _ hm0

theorem factorialLoop_denote {t t' : State} :
    Denote factorialLoop t t' ↔ t' = factFinal t := by
  constructor
  · exact factorialLoop_denote_imp
  · intro h
    subst h
    exact factorialLoop_denote_of (t 0) t rfl

/-- The denotation of the factorial program is exactly the graph of the
factorial function: from `s`, the unique final state has variable `0` equal
to `0`, variable `1` equal to `(s 0)!`, and every other variable unchanged. -/
theorem factorial_denote {s s' : State} :
    Denote factorial s s' ↔
      s' = Function.update (Function.update s 1 (Nat.factorial (s 0))) 0 0 := by
  have hfact_eq : factorial = Cmd.seq (.assign 1 (.const 1)) factorialLoop := rfl
  rw [hfact_eq]
  constructor
  · intro h
    rw [Denote.seq_iff] at h
    obtain ⟨mid, h1, h2⟩ := h
    rw [Denote.assign_iff] at h1
    have h1' : mid = Function.update s 1 1 := h1
    subst h1'
    rw [factorialLoop_denote] at h2
    rw [h2]
    exact factFinal_init
  · rintro rfl
    rw [Denote.seq_iff]
    refine ⟨Function.update s 1 1, ?_, ?_⟩
    · rw [Denote.assign_iff]
      simp [AExp.eval]
    · rw [factorialLoop_denote]
      exact factFinal_init.symm

/-- The divergent loop `while true do skip` denotes the empty relation, by
Park induction with the everywhere-false relation. -/
theorem while_true_skip_not_denote {s s' : State} :
    ¬ Denote (.while (.truth true) .skip) s s' := by
  intro h
  refine Denote.while_ind (P := fun _ _ => False) ?_ h
  intro a a' hstep
  rcases hstep with ⟨hfalse, -⟩ | ⟨-, -, -, hfalse⟩
  · simp at hfalse
  · exact hfalse

/-- Concrete run through the denotation: input `4` in variable `0` yields
`24` in variable `1`. -/
theorem factorial_four (s : State) (h : s 0 = 4) :
    ∃ s', Denote factorial s s' ∧ s' 1 = 24 := by
  refine ⟨Function.update (Function.update s 1 (Nat.factorial (s 0))) 0 0,
    factorial_denote.mpr rfl, ?_⟩
  have hf : Nat.factorial (s 0) = 24 := by
    rw [h]
    rfl
  simp [Function.update, hf]

#print axioms Cslib.IMP.DenotationalFactorialTests.factorial_denote

end Cslib.IMP.DenotationalFactorialTests
