/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Combinatorics.Perm.EulerianElements
public import MathlibExt.Combinatorics.Perm.EulerianLabelings
public import MathlibExt.Data.Fin.Tuple.StableSort
public import Mathlib.Logic.Equiv.Sum

/-!
# Actual stable-sort expansion and Eulerian composition

Every original finite labeling contributes its actual stable sorting
permutation with its actual sign. The exact stable-sort fiber count is the
original descent polynomial at the alphabet size. Successive stable sorting
and the original product-alphabet bijection prove multiplication
of the evaluated Eulerian elements multiplies their positive integer
parameters. Zero parameters and degree zero are retained explicitly.
No Eulerian composition or projector certificate is supplied.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace Equiv.Perm

/-- The actual signed group-ring sum of native stable sorting permutations of original labels. -/
def signedStableSortElement (n m : ℕ) : MonoidAlgebra ℚ (Perm (Fin n)) :=
  ∑ f : Fin n → Fin m, MonoidAlgebra.single (Tuple.sort f) (((Tuple.sort f).sign : ℤ) : ℚ)

/-- The exact signed native sorting sum is the original evaluated Eulerian element. -/
theorem signedStableSortElement_eq_eulerianLambda (n m : ℕ) :
    signedStableSortElement n m = eulerianLambda n (m : ℚ) := by
  classical
  cases n with
  | zero =>
    let _ : Unique (Perm (Fin 0)) :=
      { default := 1, uniq := fun σ => Subsingleton.elim _ _ }
    let _ : Unique (Fin 0 → Fin m) :=
      { default := Fin.elim0, uniq := fun f => funext (fun i => Fin.elim0 i) }
    rw [signedStableSortElement, eulerianLambda, Fintype.sum_unique, Fintype.sum_unique]
    have hdefault : (default : Fin 0 → Fin m) = Fin.elim0 := Subsingleton.elim _ _
    have hperm : (default : Perm (Fin 0)) = 1 := Subsingleton.elim _ _
    have hsort : Tuple.sort (Fin.elim0 : Fin 0 → Fin m) = 1 := Subsingleton.elim _ _
    rw [hdefault, hperm, hsort]
    simp [descentBinomialPolynomial]
  | succ n =>
    let e := Equiv.sigmaFiberEquiv (fun f : Fin (n + 1) → Fin m => Tuple.sort f)
    unfold signedStableSortElement
    rw [← e.sum_comp (fun f => MonoidAlgebra.single (Tuple.sort f) (((Tuple.sort f).sign : ℤ) : ℚ)),
      Fintype.sum_sigma]
    unfold eulerianLambda
    apply Finset.sum_congr rfl
    intro σ _
    have hconst (f : {f : Fin (n + 1) → Fin m // Tuple.sort f = σ}) :
        MonoidAlgebra.single (Tuple.sort (e ⟨σ, f⟩)) (((Tuple.sort (e ⟨σ, f⟩)).sign : ℤ) : ℚ) =
          MonoidAlgebra.single σ ((σ.sign : ℤ) : ℚ) := by
      change MonoidAlgebra.single (Tuple.sort f.val) (((Tuple.sort f.val).sign : ℤ) : ℚ) = _
      rw [f.property]
    simp_rw [hconst]
    rw [Finset.sum_const, Finset.card_univ, card_sortFiber,
      ← Nat.cast_smul_eq_nsmul ℚ, MonoidAlgebra.smul_single, smul_eq_mul]
    congr 1
    cases m with
    | zero =>
      simp only [Nat.cast_zero, Nat.add_zero]
      rw [← Polynomial.coeff_zero_eq_eval_zero,
        descentBinomialPolynomial_coeff_zero _ _ (by omega) (descentNumber_lt σ (by omega)), zero_mul,
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
    | succ m =>
      have he := descentBinomialPolynomial_eval_succ (n + 1) (descentNumber σ) m
        (by omega) (descentNumber_lt σ (by omega))
      have hdegree : n + (m + 1) = n + 1 + m := by omega
      have he₂ : (descentBinomialPolynomial (n + 1) (descentNumber σ)).eval (((m + 1 : ℕ) : ℚ)) =
          (((n + (m + 1) - descentNumber σ).choose (n + 1)) : ℚ) := by
        simpa only [Nat.cast_succ, hdegree] using he
      rw [he₂]

/-- Multiplying the actual native signed sorting sums multiplies the original alphabet sizes. -/
theorem signedStableSortElement_mul (n a b : ℕ) :
    signedStableSortElement n a * signedStableSortElement n b = signedStableSortElement n (b * a) := by
  classical
  let e := Tuple.successiveStableFinLabelsEquiv n a b
  unfold signedStableSortElement
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, MonoidAlgebra.single_mul_single]
  have hsign (f : Fin n → Fin a) (g : Fin n → Fin b) :
      (((Tuple.sort f).sign : ℤ) : ℚ) * (((Tuple.sort g).sign : ℤ) : ℚ) =
        (((Tuple.sort f * Tuple.sort g).sign : ℤ) : ℚ) := by
    rw [Equiv.Perm.sign_mul]
    simp only [Units.val_mul, Int.cast_mul]
  simp_rw [hsign]
  let F : ((Fin n → Fin a) × (Fin n → Fin b)) → MonoidAlgebra ℚ (Perm (Fin n)) :=
    fun z => MonoidAlgebra.single (Tuple.sort z.1 * Tuple.sort z.2)
      (((Tuple.sort z.1 * Tuple.sort z.2).sign : ℤ) : ℚ)
  change (∑ f : Fin n → Fin a, ∑ g : Fin n → Fin b, F (f, g)) = _
  rw [← Fintype.sum_prod_type F, ← e.symm.sum_comp F]
  apply Finset.sum_congr rfl
  intro h _
  change MonoidAlgebra.single (Tuple.sort (e.symm h).1 * Tuple.sort (e.symm h).2)
      (((Tuple.sort (e.symm h).1 * Tuple.sort (e.symm h).2).sign : ℤ) : ℚ) =
    MonoidAlgebra.single (Tuple.sort h) (((Tuple.sort h).sign : ℤ) : ℚ)
  have hp := Tuple.sort_successiveStableFinLabelsEquiv n a b (e.symm h)
  rw [show Tuple.successiveStableFinLabelsEquiv n a b (e.symm h) = h from e.apply_symm_apply h] at hp
  rw [← hp]

/-- The actual Eulerian polynomial elements satisfy the original natural-parameter composition law. -/
theorem eulerianLambda_mul_nat (n a b : ℕ) :
    eulerianLambda n (a : ℚ) * eulerianLambda n (b : ℚ) = eulerianLambda n ((a * b : ℕ) : ℚ) := by
  rw [← signedStableSortElement_eq_eulerianLambda,
    ← signedStableSortElement_eq_eulerianLambda, signedStableSortElement_mul,
    signedStableSortElement_eq_eulerianLambda, Nat.mul_comm]

end Equiv.Perm
