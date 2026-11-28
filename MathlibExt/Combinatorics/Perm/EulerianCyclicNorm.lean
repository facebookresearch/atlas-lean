/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Combinatorics.Perm.CyclicNormElement
public import MathlibExt.Combinatorics.Perm.EulerianCyclicAverage
public import MathlibExt.Combinatorics.Perm.EulerianRationalFamily

/-!
# The cyclic norm identity for the second convolution

Let `N=n+1`, `ρ=finRotate N`, and `N_n` be the signed cyclic norm. The coefficient of a
permutation `σ` in `Λ_N(a)N_n` is its sign times `∑ r : Fin N, P_(N,d(σ(ρ^r)⁻¹))(a)`.

The product `N_n H_n(Λ_n(a))` expands uniquely in rotation and fixed-head coordinates. At
parameter two these expansions give `Λ_N(2)N_n = 2 • (N_n H_n(Λ_n(2)))`, including the empty
tail `n=0`.

Reference: Loday, *Cyclic Homology*, Section 4.5.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace Equiv.Perm

private theorem sign_cancel_rotation (n : ℕ) (σ : Perm (Fin (n + 1))) (r : Fin (n + 1)) :
    ((((σ * (finRotate (n + 1) ^ r.val)⁻¹).sign : ℤ) : ℚ) *
      (((finRotate (n + 1) ^ r.val).sign : ℤ) : ℚ)) = ((σ.sign : ℤ) : ℚ) := by
  have h : (σ * (finRotate (n + 1) ^ r.val)⁻¹) * finRotate (n + 1) ^ r.val = σ := by
    rw [mul_assoc, inv_mul_cancel, mul_one]
  have hs := congrArg (fun π : Perm (Fin (n + 1)) => ((π.sign : ℤ) : ℚ)) h
  simpa only [Equiv.Perm.sign_mul, Units.val_mul, Int.cast_mul] using hs

/-- Let `n : ℕ`, `N=n+1`, `ρ=finRotate N`, and `a : ℚ`. Write
`P_(r,d)(X)=(1/r!)∏_(j=0)^(r-1)(X+j-d)`, `Λ_r(a)=∑ σ ∈ S_r, P_(r,descentNumber σ)(a) sign(σ)
[σ]`, and `N_n=∑ r : Fin N, sign(ρ^r.val) [ρ^r.val]` in the rational group rings. The
group-ring product is `Λ_N(a)N_n = ∑ σ ∈ S_N, (∑ r : Fin N, P_(N,d(σ*(ρ^r.val)⁻¹))(a)) sign(σ)
[σ]`. -/
theorem eulerianLambda_norm_coefficient_sum (n : ℕ) (a : ℚ) :
    eulerianLambda (n + 1) a * signedCyclicNormElement ℚ n =
      ∑ σ : Perm (Fin (n + 1)), MonoidAlgebra.single σ
        ((∑ r : Fin (n + 1),
          (descentBinomialPolynomial (n + 1)
            (descentNumber (σ * (finRotate (n + 1) ^ r.val)⁻¹))).eval a) *
          ((σ.sign : ℤ) : ℚ)) := by
  classical
  rw [eulerianLambda, signedCyclicNormElement, Finset.sum_mul]
  simp_rw [Finset.mul_sum, MonoidAlgebra.single_mul_single]
  rw [Finset.sum_comm]
  have hinner (r : Fin (n + 1)) :
      (∑ π : Perm (Fin (n + 1)),
        MonoidAlgebra.single (π * finRotate (n + 1) ^ r.val)
          (((descentBinomialPolynomial (n + 1) (descentNumber π)).eval a *
            ((π.sign : ℤ) : ℚ)) * (((finRotate (n + 1) ^ r.val).sign : ℤ) : ℚ))) =
        ∑ σ : Perm (Fin (n + 1)), MonoidAlgebra.single σ
          ((descentBinomialPolynomial (n + 1)
            (descentNumber (σ * (finRotate (n + 1) ^ r.val)⁻¹))).eval a *
              ((σ.sign : ℤ) : ℚ)) := by
    let e : Perm (Fin (n + 1)) ≃ Perm (Fin (n + 1)) :=
      Equiv.mulRight (finRotate (n + 1) ^ r.val)
    rw [← e.symm.sum_comp]
    apply Finset.sum_congr rfl
    intro σ _
    have he : e.symm σ = σ * (finRotate (n + 1) ^ r.val)⁻¹ := rfl
    rw [he]
    change MonoidAlgebra.single
      ((σ * (finRotate (n + 1) ^ r.val)⁻¹) * finRotate (n + 1) ^ r.val) _ = _
    rw [mul_assoc, inv_mul_cancel, mul_one, mul_assoc, sign_cancel_rotation]
  simp_rw [hinner]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  calc
    _ = MonoidAlgebra.single σ
        (∑ r : Fin (n + 1),
          (descentBinomialPolynomial (n + 1)
            (descentNumber (σ * (finRotate (n + 1) ^ r.val)⁻¹))).eval a *
              ((σ.sign : ℤ) : ℚ)) := by
      exact (map_sum (MonoidAlgebra.singleAddHom σ) _ Finset.univ).symm
    _ = _ := by rw [Finset.sum_mul]

/-- Let `n : ℕ`, `N=n+1`, `ρ=finRotate N`, and `a : ℚ`. Write
`P_(r,d)(X)=(1/r!)∏_(j=0)^(r-1)(X+j-d)`, `Λ_r(a)=∑ σ ∈ S_r, P_(r,descentNumber σ)(a) sign(σ)
[σ]`, and `N_n=∑ r : Fin N, sign(ρ^r.val) [ρ^r.val]` in the rational group rings. If `H_n` is
the fixed-head group-ring map, `N_n H_n(Λ_n(a)) = ∑ r : Fin N, ∑ π ∈ S_n, P_(n,d(π))(a)
sign(ρ^r.val * H_n(π)) [ρ^r.val * H_n(π)]`, with `H_n(π)` denoting its permutation embedding
in the summand. -/
theorem norm_headFixing_eulerianLambda_sum (n : ℕ) (a : ℚ) :
    signedCyclicNormElement ℚ n * headFixingGroupRingMap ℚ n (eulerianLambda n a) =
      ∑ r : Fin (n + 1), ∑ π : Perm (Fin n),
        MonoidAlgebra.single (finRotate (n + 1) ^ r.val * headFixingHom n π)
          ((descentBinomialPolynomial n (descentNumber π)).eval a *
            ((((finRotate (n + 1) ^ r.val * headFixingHom n π).sign : ℤ) : ℚ))) := by
  classical
  rw [signedCyclicNormElement, eulerianLambda, map_sum, Finset.sum_mul]
  simp_rw [headFixingGroupRingMap_single, Finset.mul_sum, MonoidAlgebra.single_mul_single]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro π _
  congr 1
  have hhead : (headFixingHom n π).sign = π.sign := headFixingPermutation_sign n π
  rw [Equiv.Perm.sign_mul, hhead]
  simp only [Units.val_mul, Int.cast_mul]
  ring

/-- For every `n : ℕ`, the rational convolution family and signed cyclic norm satisfy `Λ_(n+1)(2)
* N_n = 2 • (N_n * H_n(Λ_n(2)))`, where `H_n : ℚ[S_n] → ℚ[S_(n+1)]` is the fixed-head
group-ring map. The identity includes `n=0`. -/
theorem eulerianLambda_two_norm (n : ℕ) :
    eulerianLambda (n + 1) 2 * signedCyclicNormElement ℚ n =
      (2 : ℚ) • (signedCyclicNormElement ℚ n *
        headFixingGroupRingMap ℚ n (eulerianLambda n 2)) := by
  classical
  rw [eulerianLambda_norm_coefficient_sum]
  rw [sum_rotationHead n]
  rw [norm_headFixing_eulerianLambda_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r₀ _
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro π _
  rw [descentBinomial_rotation_average_two_inverse, MonoidAlgebra.smul_single]
  congr 1
  simp only [smul_eq_mul]
  ring

end Equiv.Perm
