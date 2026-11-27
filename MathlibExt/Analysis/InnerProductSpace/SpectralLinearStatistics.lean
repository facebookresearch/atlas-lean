/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.HoffmanWielandt
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Topology.EMetricSpace.Lipschitz

import Mathlib.Algebra.Order.Chebyshev

/-!
# Stability of spectral linear statistics

For Hermitian `n × n` matrices `A` and `B` and an `L`-Lipschitz function `f : ℝ → ℝ`,
`|∑ᵢ f(λᵢ(A)) - ∑ᵢ f(λᵢ(B))| ≤ L √n ‖A - B‖_F`, where `‖·‖_F` is the Frobenius norm. Dividing by
`n`, the linear statistic `∫ f dμ_A = (1/n) ∑ᵢ f(λᵢ(A))` of the empirical spectral distribution
moves by at most `L ‖A - B‖_F / √n`. This is how random matrix theory compares the spectra of a
matrix and a perturbation of it, for instance to reduce Wigner's semicircle law to bounded
entries by truncation, and it is the Lipschitz estimate behind the concentration of linear
statistics.

The proof sorts both spectra (the sums do not depend on the order), applies the Lipschitz bound
termwise, Cauchy–Schwarz, and the Hoffman–Wielandt inequality
`∑ᵢ (λᵢ(A) - λᵢ(B))² ≤ ‖A - B‖_F²` (`hoffman_wielandt_hermitian`).

## References

* T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, AMS, 2012,
  §1.3 (the Wielandt–Hoffman inequality (1.68)) and §2.4.1, Lemma 2.4.3 (its distribution-function
  form, used to reduce the semicircular law to bounded entries); the statement here is a
  linear-statistics variant of Lemma 2.4.3.
-/

@[expose] public section

open scoped NNReal

namespace Matrix.IsHermitian

/-- A sum over the eigenvalues of a symmetric operator does not depend on the proof of the
dimension used to index them. -/
private lemma sum_eigenvalues_congr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (g : ℝ → ℝ) {m₁ m₂ : ℕ}
    (h₁ : Module.finrank ℂ E = m₁) (h₂ : Module.finrank ℂ E = m₂) :
    ∑ i : Fin m₁, g (hT.eigenvalues h₁ i) = ∑ j : Fin m₂, g (hT.eigenvalues h₂ j) := by
  obtain rfl : m₁ = m₂ := h₁.symm.trans h₂
  rfl

/-- **Lipschitz linear statistics of Hermitian spectra are stable** (a linear-statistics variant of
Tao, *Topics in Random Matrix Theory*, Lemma 2.4.3, via the Wielandt–Hoffman inequality (1.68)).
For Hermitian `n × n` matrices `A`, `B` with eigenvalues `λᵢ(A)`, `λᵢ(B)` (listed in any order,
with multiplicity) and an `L`-Lipschitz `f : ℝ → ℝ`,
`|∑ᵢ f(λᵢ(A)) - ∑ᵢ f(λᵢ(B))| ≤ L √n (∑ᵢⱼ |Aᵢⱼ - Bᵢⱼ|²)^(1/2)`. -/
theorem abs_sum_sub_sum_le_of_lipschitzWith {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) :
    |∑ i, f (hA.eigenvalues i) - ∑ i, f (hB.eigenvalues i)| ≤
      L * Real.sqrt n * Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j - B i j)) := by
  set a := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues finrank_euclideanSpace_fin
  set b := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues finrank_euclideanSpace_fin
  -- Both sums may be taken over the sorted spectra used by Hoffman–Wielandt.
  have hsort : ∀ {C : Matrix (Fin n) (Fin n) ℂ} (hC : C.IsHermitian),
      ∑ i, f (hC.eigenvalues i) = ∑ k, f ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hC).eigenvalues
        finrank_euclideanSpace_fin k) := by
    intro C hC
    simp only [Matrix.IsHermitian.eigenvalues, Matrix.IsHermitian.eigenvalues₀]
    rw [Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
      (fun k => f ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hC).eigenvalues
        finrank_euclideanSpace k))]
    exact sum_eigenvalues_congr _ f _ _
  rw [hsort hA, hsort hB, ← Finset.sum_sub_distrib]
  have hHW := MathlibExt.Analysis.InnerProductSpace.HoffmanWielandtWanted.hoffman_wielandt_hermitian
    A B hA hB
  simp only at hHW
  -- Termwise Lipschitz bound, then Cauchy–Schwarz.
  have h1 : |∑ k, (f (a k) - f (b k))| ≤ L * ∑ k, |a k - b k| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have := hf.dist_le_mul (a k) (b k)
    simpa [Real.dist_eq] using this
  have h2 : ∑ k, |a k - b k| ≤ Real.sqrt n * Real.sqrt (∑ k, (a k - b k) ^ 2) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg n)]
    refine Real.le_sqrt_of_sq_le ?_
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => |a k - b k|)
    simpa [sq_abs] using this
  have h3 : Real.sqrt (∑ k, (a k - b k) ^ 2) ≤
      Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j - B i j)) := Real.sqrt_le_sqrt hHW
  calc |∑ k, (f (a k) - f (b k))| ≤ L * ∑ k, |a k - b k| := h1
    _ ≤ L * (Real.sqrt n * Real.sqrt (∑ k, (a k - b k) ^ 2)) := by gcongr
    _ ≤ L * (Real.sqrt n * Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j - B i j))) := by gcongr
    _ = L * Real.sqrt n * Real.sqrt (∑ i, ∑ j, Complex.normSq (A i j - B i j)) := by ring

end Matrix.IsHermitian
