/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.PolynomialInequalities
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MvPolynomial

example {σ ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (g : ι → MvPolynomial σ ℝ) (h : κ → MvPolynomial σ ℝ)
    {p s₀ : MvPolynomial σ ℝ} {s : ι → MvPolynomial σ ℝ}
    {r : κ → MvPolynomial σ ℝ} (hs₀ : IsSumSq s₀)
    (hs : ∀ i ∈ I, IsSumSq (s i))
    (hid : p = s₀ + (∑ i ∈ I, s i * g i) + ∑ j ∈ J, r j * h j)
    {x : σ → ℝ} (hx : x ∈ basicClosedSet I J g h) : 0 ≤ eval x p := by
  exact eval_nonneg_of_sos_identity hs₀ hs hid hx

private abbrev P := MvPolynomial (Fin 2) ℝ

private theorem square_sos (p : P) : IsSumSq (p ^ 2) := by
  simpa only [pow_two] using IsSumSq.mul_self p

-- The disk identity has a nonzero SOS remainder and is sharp at (1,0).
example (x : Fin 2 → ℝ) (hx : 0 ≤ 1 - (x 0)^2 - (x 1)^2) :
    0 ≤ 1 - (x 0)^2 := by
  have hn := eval_nonneg_of_sos_identity
    (I := ({0} : Finset (Fin 1))) (J := (∅ : Finset (Fin 1)))
    (g := fun _ => (1 - X 0 ^ 2 - X 1 ^ 2 : P)) (h := fun _ => 0)
    (p := 1 - X 0 ^ 2) (s₀ := X 1 ^ 2) (s := fun _ => 1) (r := fun _ => 0)
    (square_sos _) (fun _ _ => IsSumSq.one)
    (by simp) (x := x) (by simpa [basicClosedSet] using hx)
  simpa using hn

example : (![1, 0] : Fin 2 → ℝ) ∈
    basicClosedSet ({0} : Finset (Fin 1)) (∅ : Finset (Fin 1))
      (fun _ => (1 - X 0 ^ 2 - X 1 ^ 2 : P)) (fun _ => 0) ∧
    eval (![1, 0] : Fin 2 → ℝ) (1 - X 0 ^ 2 : P) = 0 := by
  norm_num [basicClosedSet]

-- A nonconstant inequality multiplier exercises the SOS premise beyond 1.
example (x : Fin 2 → ℝ) (hx : 0 ≤ 1 - (x 0)^2) :
    0 ≤ (x 0)^2 * (1 - (x 0)^2) := by
  have hn := eval_nonneg_of_sos_identity
    (I := ({0} : Finset (Fin 1))) (J := (∅ : Finset (Fin 1)))
    (g := fun _ => (1 - X 0 ^ 2 : P)) (h := fun _ => 0)
    (p := X 0 ^ 2 * (1 - X 0 ^ 2)) (s₀ := 0)
    (s := fun _ => X 0 ^ 2) (r := fun _ => 0)
    IsSumSq.zero (fun _ _ => square_sos _)
    (by simp) (x := x) (by simpa [basicClosedSet] using hx)
  simpa using hn

-- Equality multipliers may change sign on the feasible set.
example (x : Fin 2 → ℝ) (hx : x 1 = 0) : 0 ≤ (x 0)^2 + x 0 * x 1 := by
  have hn := eval_nonneg_of_sos_identity
    (I := (∅ : Finset (Fin 1))) (J := ({0} : Finset (Fin 1)))
    (g := fun _ => (0 : P)) (h := fun _ => X 1)
    (p := X 0 ^ 2 + X 0 * X 1) (s₀ := X 0 ^ 2)
    (s := fun _ => 0) (r := fun _ => X 0)
    (square_sos _) (by simp) (by simp) (x := x)
    (by simpa [basicClosedSet] using hx)
  simpa using hn

example : eval (![1, 0] : Fin 2 → ℝ) (X 0 : P) = 1 ∧
    eval (![-1, 0] : Fin 2 → ℝ) (X 0 : P) = -1 ∧
    (![1, 0] : Fin 2 → ℝ) ∈ basicClosedSet (∅ : Finset (Fin 1)) {0}
      (fun _ => (0 : P)) (fun (_ : Fin 1) => X 1) ∧
    (![-1, 0] : Fin 2 → ℝ) ∈ basicClosedSet (∅ : Finset (Fin 1)) {0}
      (fun _ => (0 : P)) (fun (_ : Fin 1) => X 1) := by
  norm_num [basicClosedSet]

-- Inconsistent constraints x≥1 and x≤0; exercise the public emptiness theorem
-- with the exact minus-one identity, not an independent arithmetic proof.
example : basicClosedSet (Finset.univ : Finset (Fin 2)) (∅ : Finset (Fin 1))
    (![X 0 - 1, -X 0] : Fin 2 → P) (fun _ => 0) = ∅ := by
  apply basicClosedSet_eq_empty_of_sos_identity
    (s₀ := (0 : P)) (s := fun _ => 1) (r := fun _ => 0)
    IsSumSq.zero (fun _ _ => IsSumSq.one)
  simp only [Finset.sum_empty, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    one_mul, zero_add, add_zero]
  ring

-- Both empty families recover global SOS nonnegativity, with arbitrary variables.
example {σ : Type*} (p : MvPolynomial σ ℝ) (hp : IsSumSq p) (x : σ → ℝ) :
    0 ≤ eval x p := by
  exact eval_nonneg_of_sos_identity (I := (∅ : Finset (Fin 0)))
    (J := (∅ : Finset (Fin 0))) (g := fun i => Fin.elim0 i) (h := fun i => Fin.elim0 i)
    (s := fun i => Fin.elim0 i) (r := fun i => Fin.elim0 i)
    hp (by simp) (by simp) (by simp [basicClosedSet])

example : basicClosedSet (∅ : Finset (Fin 0)) (∅ : Finset (Fin 0))
    (fun i => Fin.elim0 i : Fin 0 → MvPolynomial (Fin 0) ℝ)
    (fun i => Fin.elim0 i) = Set.univ := by
  ext x
  simp [basicClosedSet]

-- Neither nonnegative inequality multipliers nor valid point constraints
-- can be dropped from the soundness theorem.
example : 0 ≤ eval (![0, 0] : Fin 2 → ℝ) (1 : P) ∧
    eval (![0, 0] : Fin 2 → ℝ) ((-1 : P) * 1) < 0 := by norm_num

example : IsSumSq (1 : P) ∧
    eval (![0, 0] : Fin 2 → ℝ) ((1 : P) * (-1)) < 0 := by
  exact ⟨IsSumSq.one, by norm_num⟩

example {σ ι κ : Type*} (I : Finset ι) (J : Finset κ)
    (g : ι → MvPolynomial σ ℝ) (h : κ → MvPolynomial σ ℝ) :
    TauCeti.IsSemialgebraic (basicClosedSet I J g h) :=
  isSemialgebraic_basicClosedSet I J g h

-- Values at indices outside the finite family impose no hidden constraints.
example (x : Fin 2 → ℝ) : 0 ≤ eval x (1 : P) := by
  exact eval_nonneg_of_sos_identity
    (I := ({0} : Finset (Fin 2))) (J := (∅ : Finset (Fin 1)))
    (g := ![(1 : P), -1]) (h := fun _ => 0)
    (s₀ := 0) (s := ![(1 : P), -1]) (r := fun _ => 0)
    IsSumSq.zero (by
      intro i hi
      simp only [Finset.mem_singleton] at hi
      subst i
      exact IsSumSq.one)
    (by simp) (by simp [basicClosedSet])

-- Mapping a constant SOS polynomial also works with no variables at all.
example (x : Fin 0 → ℝ) :
    IsSumSq (eval x (C 4 : MvPolynomial (Fin 0) ℝ)) := by
  exact ((IsSumSq.natCast (R := ℝ) 4).map C).map (eval x)

#print axioms MvPolynomial.eval_nonneg_of_sos_identity
#print axioms MvPolynomial.basicClosedSet_eq_empty_of_sos_identity
#print axioms MvPolynomial.isSemialgebraic_basicClosedSet
