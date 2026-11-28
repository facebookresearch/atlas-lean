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
# Stable-sort sums and Eulerian composition

The element `C_n(m) = ∑ f : Fin n → Fin m, sign(sort f) [sort f]` in `ℚ[S_n]` equals the
rational Eulerian convolution value `Λ_n(m)`.

For all natural alphabet sizes `a,b`, successive stable sorting gives `C_n(a)C_n(b)=C_n(b*a)`.
Consequently `Λ_n(a)Λ_n(b)=Λ_n(a*b)`. Zero alphabet size and the empty word are included in
these identities.

References: Stanley, *Enumerative Combinatorics*, Volume 1, Chapters 1 and 3; Loday, *Cyclic
Homology*, Section 4.5.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace Equiv.Perm

/-- For `n,m : ℕ`, `signedStableSortElement n m = ∑ f : Fin n → Fin m, sign(Tuple.sort f)
[Tuple.sort f]` in `ℚ[S_n]`. -/
def signedStableSortElement (n m : ℕ) : MonoidAlgebra ℚ (Perm (Fin n)) :=
  ∑ f : Fin n → Fin m, MonoidAlgebra.single (Tuple.sort f) (((Tuple.sort f).sign : ℤ) : ℚ)

/-- For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)`, `P_(n,d)(X) = (1/n!)∏_(j=0)^(n-1)(X+j-d)`, and
`Λ_n(t) = ∑ σ ∈ S_n, P_(n,descentNumber σ)(t) sign(σ) [σ]` in `ℚ[S_n]`. For every `m : ℕ`,
`signedStableSortElement n m = Λ_n(m)`. -/
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
        descentBinomialPolynomial_coeff_zero _ _ (by omega) (descentNumber_lt σ (by omega)),
          zero_mul,
        Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
    | succ m =>
      have he := descentBinomialPolynomial_eval_succ (n + 1) (descentNumber σ) m
        (by omega) (descentNumber_lt σ (by omega))
      have hdegree : n + (m + 1) = n + 1 + m := by omega
      have he₂ : (descentBinomialPolynomial (n + 1) (descentNumber σ)).eval (((m + 1 : ℕ) : ℚ)) =
          (((n + (m + 1) - descentNumber σ).choose (n + 1)) : ℚ) := by
        simpa only [Nat.cast_succ, hdegree] using he
      rw [he₂]

/-- For `n,a,b : ℕ`, `signedStableSortElement n a * signedStableSortElement n b =
signedStableSortElement n (b*a)` in `ℚ[S_n]`. -/
theorem signedStableSortElement_mul (n a b : ℕ) :
    signedStableSortElement n a * signedStableSortElement n b = signedStableSortElement n (b * a) :=
      by
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
  rw [show Tuple.successiveStableFinLabelsEquiv n a b (e.symm h) = h from e.apply_symm_apply h] at
    hp
  rw [← hp]

/-- For `n : ℕ`, let `S_n = Equiv.Perm (Fin n)`, `P_(n,d)(X) = (1/n!)∏_(j=0)^(n-1)(X+j-d)`, and
`Λ_n(t) = ∑ σ ∈ S_n, P_(n,descentNumber σ)(t) sign(σ) [σ]` in `ℚ[S_n]`. For `a,b : ℕ`, `Λ_n(a)
* Λ_n(b) = Λ_n(a*b)`, with all natural parameters coerced to `ℚ`. -/
theorem eulerianLambda_mul_nat (n a b : ℕ) :
    eulerianLambda n (a : ℚ) * eulerianLambda n (b : ℚ) = eulerianLambda n ((a * b : ℕ) : ℚ) := by
  rw [← signedStableSortElement_eq_eulerianLambda,
    ← signedStableSortElement_eq_eulerianLambda, signedStableSortElement_mul,
    signedStableSortElement_eq_eulerianLambda, Nat.mul_comm]

end Equiv.Perm
