/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.MetricSpace.HausdorffDistance

import Mathlib.Tactic.Abel

@[expose] public section

/-!
# Bauer–Fike eigenvalue perturbation for normal operators

For a normal operator `A` on a complex Hilbert space and any bounded
perturbation `E`, every point `μ` of the spectrum of `A + E` lies within
`‖E‖` of the spectrum of `A`. This is the Bauer–Fike theorem
(F. L. Bauer and C. T. Fike, *Norms and exclusion theorems*, Numer. Math. 2
(1960), 137–141). In particular, for self-adjoint `A` and `A + E` the two
spectra are Hausdorff-close by at most `‖E‖`, which is the
Weyl perturbation inequality for self-adjoint operators in its
Hausdorff form; base MathlibExt's `WeylPerturbation.lean` proves the
eigenvalue-by-eigenvalue form for Hermitian matrices, not the
Hausdorff form for operators.

The proof goes through a resolvent norm bound for normal operators:
if `z` is outside the spectrum of a normal `A`, then
`‖(z • 1 - A)⁻¹‖ ≤ 1 / dist z (spectrum ℂ A)`, because the resolvent is
normal, hence its norm equals its spectral radius, and a purely algebraic
factorisation writes every point of the resolvent's spectrum as
`(z - w)⁻¹` for `w` in the spectrum of `A`.

This is a companion to the spectral material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`
(self-adjoint spectrum, Rayleigh bounds, Fredholm alternative). It is not
one of the 72 v1 targets, and it is in neither the pinned Mathlib (which has
the spectral-radius formula for normal elements of a C⋆-algebra and the
continuous functional calculus, but no resolvent-norm or Bauer–Fike
statement) nor base MathlibExt.

## Main declarations

* `norm_ringInverse_sub_smul_one_le` : the resolvent norm bound for a
  normal operator.
* `infDist_le_norm_of_mem_spectrum_add` : the Bauer–Fike bound:
  `dist μ (spectrum ℂ A) ≤ ‖E‖` for `μ ∈ spectrum ℂ (A + E)`.
* `exists_mem_spectrum_norm_sub_le` : the attained form: some
  `λ ∈ spectrum ℂ A` has `‖μ - λ‖ ≤ ‖E‖`.
* `hausdorffDist_spectrum_le_of_isSelfAdjoint` : for self-adjoint `A`
  and `A + E`, the Hausdorff distance of the two spectra is at most `‖E‖`.
-/

section

namespace MathlibExt.Analysis.InnerProductSpace.BauerFike

open scoped Topology

open Metric

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H]

omit [Nontrivial H] [CompleteSpace H] in
/-- Spectral mapping for the resolvent, by pure algebra: if `λ` lies in the
spectrum of `(z • 1 - A)⁻¹`, then `λ = (z - w)⁻¹` for some `w` in the
spectrum of `A`. The key identity is the factorisation
`λ • 1 - (z • 1 - A)⁻¹ = (z • 1 - A)⁻¹ * (λ • ((z - λ⁻¹) • 1 - A))`. -/
private lemma exists_mem_spectrum_of_mem_spectrum_ringInverse {A : H →L[ℂ] H}
    {z t : ℂ} (hz : z ∉ spectrum ℂ A)
    (ht : t ∈ spectrum ℂ (Ring.inverse (z • (1 : H →L[ℂ] H) - A))) :
    ∃ w ∈ spectrum ℂ A, (z - w)⁻¹ = t := by
  have hunitB : IsUnit (z • (1 : H →L[ℂ] H) - A) := by
    by_contra hnu
    apply hz
    rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
    exact hnu
  have hRunit : IsUnit (Ring.inverse (z • (1 : H →L[ℂ] H) - A)) := by
    obtain ⟨u, hu⟩ := hunitB
    exact ⟨u⁻¹, by rw [← hu, Ring.inverse_unit]⟩
  have htne : t ≠ 0 := by
    intro ht0
    have hneg : IsUnit (algebraMap ℂ (H →L[ℂ] H) t
        - Ring.inverse (z • (1 : H →L[ℂ] H) - A)) := by
      rw [ht0, map_zero, zero_sub]
      exact hRunit.neg
    exact (spectrum.mem_iff.mp ht) hneg
  have e1 : t • ((z - t⁻¹) • (1 : H →L[ℂ] H) - A)
      = t • (z • (1 : H →L[ℂ] H) - A) - 1 := by
    rw [smul_sub, smul_sub, smul_smul, smul_smul, mul_sub, mul_inv_cancel₀ htne,
      sub_smul, one_smul]
    abel
  have e2 : algebraMap ℂ (H →L[ℂ] H) t - Ring.inverse (z • (1 : H →L[ℂ] H) - A)
      = Ring.inverse (z • (1 : H →L[ℂ] H) - A) * (t • (z • (1 : H →L[ℂ] H) - A) - 1) := by
    rw [mul_sub, mul_one, mul_smul_comm, Ring.inverse_mul_cancel _ hunitB,
      Algebra.algebraMap_eq_smul_one]
  have hfac : algebraMap ℂ (H →L[ℂ] H) t - Ring.inverse (z • (1 : H →L[ℂ] H) - A)
      = Ring.inverse (z • (1 : H →L[ℂ] H) - A)
          * (t • ((z - t⁻¹) • (1 : H →L[ℂ] H) - A)) :=
    e2.trans (congrArg _ e1.symm)
  refine ⟨z - t⁻¹, ?_, by rw [sub_sub_self, inv_inv]⟩
  by_contra hnot
  have hunitC : IsUnit ((z - t⁻¹) • (1 : H →L[ℂ] H) - A) := by
    by_contra hnu
    apply hnot
    rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
    exact hnu
  have hunitS : IsUnit (t • (1 : H →L[ℂ] H)) := by
    refine ⟨⟨t • (1 : H →L[ℂ] H), t⁻¹ • (1 : H →L[ℂ] H), ?_, ?_⟩, rfl⟩
    · rw [smul_mul_smul, mul_one, mul_inv_cancel₀ htne, one_smul]
    · rw [smul_mul_smul, mul_one, inv_mul_cancel₀ htne, one_smul]
  have hunitP : IsUnit (t • ((z - t⁻¹) • (1 : H →L[ℂ] H) - A)) := by
    have hsmul : t • ((z - t⁻¹) • (1 : H →L[ℂ] H) - A)
        = (t • (1 : H →L[ℂ] H)) * ((z - t⁻¹) • (1 : H →L[ℂ] H) - A) := by
      rw [smul_mul_assoc, one_mul]
    rw [hsmul]
    exact hunitS.mul hunitC
  have hunitL : IsUnit (algebraMap ℂ (H →L[ℂ] H) t
      - Ring.inverse (z • (1 : H →L[ℂ] H) - A)) := by
    rw [hfac]
    exact hRunit.mul hunitP
  exact (spectrum.mem_iff.mp ht) hunitL

omit [Nontrivial H] in
/-- A scalar operator is normal. -/
private lemma isStarNormal_algebraMap (z : ℂ) :
    IsStarNormal (algebraMap ℂ (H →L[ℂ] H) z) := by
  refine ⟨?_⟩
  rw [Algebra.algebraMap_eq_smul_one, star_smul, star_one]
  show (starRingEnd ℂ) z • (1 : H →L[ℂ] H) * (z • (1 : H →L[ℂ] H))
    = (z • (1 : H →L[ℂ] H)) * ((starRingEnd ℂ) z • (1 : H →L[ℂ] H))
  rw [smul_mul_smul, smul_mul_smul, mul_comm]

omit [Nontrivial H] in
/-- The resolvent of a normal operator is normal. -/
private lemma isStarNormal_ringInverse_sub {A : H →L[ℂ] H} [IsStarNormal A] {z : ℂ}
    (hz : z ∉ spectrum ℂ A) :
    IsStarNormal (Ring.inverse (algebraMap ℂ (H →L[ℂ] H) z - A)) := by
  have hunit : IsUnit (algebraMap ℂ (H →L[ℂ] H) z - A) := by
    by_contra hnu
    exact hz (spectrum.mem_iff.mpr hnu)
  have hcomm : Commute (algebraMap ℂ (H →L[ℂ] H) z) (star A) := by
    rw [Algebra.algebraMap_eq_smul_one]
    simp only [Commute, SemiconjBy, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  have hB : IsStarNormal (algebraMap ℂ (H →L[ℂ] H) z - A) :=
    hcomm.isStarNormal_sub (ha := isStarNormal_algebraMap z)
  have hunit' : IsStarNormal (↑hunit.unit : H →L[ℂ] H) := by
    rw [hunit.unit_spec]
    exact hB
  rw [← hunit.unit_spec, Ring.inverse_unit]
  exact inferInstance

set_option linter.style.haveILetI false in
/-- The resolvent norm bound for a normal operator: if `z` lies outside the
spectrum of a normal `A`, then `‖(z • 1 - A)⁻¹‖ ≤ 1 / dist z (spectrum ℂ A)`. -/
theorem norm_ringInverse_sub_smul_one_le {A : H →L[ℂ] H} [IsStarNormal A] {z : ℂ}
    (hz : z ∉ spectrum ℂ A) :
    ‖Ring.inverse (algebraMap ℂ (H →L[ℂ] H) z - A)‖
      ≤ (Metric.infDist z (spectrum ℂ A))⁻¹ := by
  set R := Ring.inverse (algebraMap ℂ (H →L[ℂ] H) z - A)
  set d := Metric.infDist z (spectrum ℂ A) with hd
  have hspec_nonempty : (spectrum ℂ A).Nonempty := spectrum.nonempty A
  have hdpos : 0 < d := by
    have hclosed : IsClosed (spectrum ℂ A) := spectrum.isClosed A
    exact (hclosed.notMem_iff_infDist_pos hspec_nonempty).mp hz
  have hRnormal : IsStarNormal R := isStarNormal_ringInverse_sub hz
  haveI : IsStarNormal R := hRnormal
  obtain ⟨t₀, ht₀, ht₀norm⟩ := spectrum.exists_nnnorm_eq_spectralRadius R
  have ht₀' : t₀ ∈ spectrum ℂ (Ring.inverse (z • (1 : H →L[ℂ] H) - A)) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact ht₀
  obtain ⟨w, hw, ht₀w⟩ :=
    exists_mem_spectrum_of_mem_spectrum_ringInverse hz ht₀'
  have hnorm : ‖R‖₊ = ‖t₀‖₊ := by
    have h := IsStarNormal.spectralRadius_eq_nnnorm R
    exact (ENNReal.coe_inj.mp (ht₀norm.trans h)).symm
  have hzw : z - w ≠ 0 := by
    intro h
    have hwz : w = z := (eq_of_sub_eq_zero h).symm
    subst hwz
    exact hz hw
  have hdw : d ≤ ‖z - w‖ := by
    have h := Metric.infDist_le_dist_of_mem (s := spectrum ℂ A) hw (x := z)
    rwa [dist_eq_norm] at h
  have hdnn : (Real.toNNReal d) ≤ ‖z - w‖₊ := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal d (le_of_lt hdpos), coe_nnnorm]
    exact hdw
  have hle : ‖R‖₊ ≤ Real.toNNReal (d⁻¹) := by
    rw [hnorm, ← ht₀w, nnnorm_inv, Real.toNNReal_inv]
    exact (inv_le_inv₀ (nnnorm_pos.mpr hzw) (Real.toNNReal_pos.mpr hdpos)).mpr hdnn
  have hle' : ‖R‖ ≤ d⁻¹ := by
    rw [← NNReal.coe_le_coe] at hle
    rw [coe_nnnorm, Real.coe_toNNReal (d⁻¹) (inv_nonneg.mpr (le_of_lt hdpos))] at hle
    exact hle
  exact hle'

/-- The Bauer–Fike theorem: every point of the spectrum of `A + E` lies
within `‖E‖` of the spectrum of a normal operator `A`. -/
theorem infDist_le_norm_of_mem_spectrum_add {A E : H →L[ℂ] H} [IsStarNormal A]
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (A + E)) :
    Metric.infDist μ (spectrum ℂ A) ≤ ‖E‖ := by
  by_contra hlt
  push Not at hlt
  set d := Metric.infDist μ (spectrum ℂ A) with hd
  have hμnot : μ ∉ spectrum ℂ A := by
    intro hmem
    rw [hd, Metric.infDist_zero_of_mem hmem] at hlt
    exact (not_lt_of_ge (norm_nonneg E)) hlt
  -- The resolvent at `μ` exists and has norm at most `1 / d`.
  have hres : ‖Ring.inverse (algebraMap ℂ (H →L[ℂ] H) μ - A)‖ ≤ d⁻¹ :=
    norm_ringInverse_sub_smul_one_le hμnot
  have hdpos : 0 < d := by
    have hspec_nonempty : (spectrum ℂ A).Nonempty := spectrum.nonempty A
    exact ((spectrum.isClosed A).notMem_iff_infDist_pos hspec_nonempty).mp hμnot
  have hRE : ‖Ring.inverse (algebraMap ℂ (H →L[ℂ] H) μ - A) * E‖ < 1 := by
    calc ‖Ring.inverse (algebraMap ℂ (H →L[ℂ] H) μ - A) * E‖
        ≤ ‖Ring.inverse (algebraMap ℂ (H →L[ℂ] H) μ - A)‖ * ‖E‖ :=
          norm_mul_le _ _
      _ ≤ d⁻¹ * ‖E‖ := by
          exact mul_le_mul_of_nonneg_right hres (norm_nonneg E)
      _ < d⁻¹ * d := by
          exact mul_lt_mul_of_pos_left hlt (inv_pos.mpr hdpos)
      _ = 1 := by
          exact inv_mul_cancel₀ (ne_of_gt hdpos)
  have hunit1 : IsUnit (1 - Ring.inverse (algebraMap ℂ (H →L[ℂ] H) μ - A) * E) :=
    isUnit_one_sub_of_norm_lt_one hRE
  have hunitB : IsUnit (algebraMap ℂ (H →L[ℂ] H) μ - A) := by
    by_contra hnu
    exact hμnot (spectrum.mem_iff.mpr hnu)
  -- Factor `μ • 1 - (A + E) = (μ • 1 - A) * (1 - R * E)`.
  have hfactor : algebraMap ℂ (H →L[ℂ] H) μ - (A + E)
      = (algebraMap ℂ (H →L[ℂ] H) μ - A)
          * (1 - Ring.inverse (algebraMap ℂ (H →L[ℂ] H) μ - A) * E) := by
    calc algebraMap ℂ (H →L[ℂ] H) μ - (A + E)
        = (algebraMap ℂ (H →L[ℂ] H) μ - A) - E := by rw [sub_add_eq_sub_sub]
      _ = (algebraMap ℂ (H →L[ℂ] H) μ - A)
            - (algebraMap ℂ (H →L[ℂ] H) μ - A)
                * (Ring.inverse (algebraMap ℂ (H →L[ℂ] H) μ - A) * E) := by
          rw [← mul_assoc, Ring.mul_inverse_cancel _ hunitB, one_mul]
      _ = (algebraMap ℂ (H →L[ℂ] H) μ - A)
            * (1 - Ring.inverse (algebraMap ℂ (H →L[ℂ] H) μ - A) * E) := by
          rw [mul_sub, mul_one]
  have hunit : IsUnit (algebraMap ℂ (H →L[ℂ] H) μ - (A + E)) := by
    rw [hfactor]
    exact hunitB.mul hunit1
  exact (spectrum.mem_iff.mp hμ) hunit

/-- The attained form of Bauer–Fike: some eigenvalue-like point of the
spectrum of `A` is within `‖E‖` of `μ`. -/
theorem exists_mem_spectrum_norm_sub_le {A E : H →L[ℂ] H} [IsStarNormal A]
    {μ : ℂ} (hμ : μ ∈ spectrum ℂ (A + E)) :
    ∃ v ∈ spectrum ℂ A, ‖μ - v‖ ≤ ‖E‖ := by
  have hbound := infDist_le_norm_of_mem_spectrum_add (A := A) (E := E) hμ
  obtain ⟨v, hv, hvd⟩ :=
    (spectrum.isClosed A).exists_infDist_eq_dist (spectrum.nonempty A) μ
  refine ⟨v, hv, ?_⟩
  rw [hvd, dist_eq_norm] at hbound
  exact hbound

set_option linter.style.haveILetI false in
/-- For self-adjoint `A` and `A + E`, the Hausdorff distance of the two
spectra is at most `‖E‖`. -/
theorem hausdorffDist_spectrum_le_of_isSelfAdjoint {A E : H →L[ℂ] H}
    (hA : IsSelfAdjoint A) (hAE : IsSelfAdjoint (A + E)) :
    Metric.hausdorffDist (spectrum ℂ A) (spectrum ℂ (A + E)) ≤ ‖E‖ := by
  haveI hAn : IsStarNormal A := hA.isStarNormal
  haveI hAEn : IsStarNormal (A + E) := hAE.isStarNormal
  apply Metric.hausdorffDist_le_of_infDist (norm_nonneg E)
  · intro x hx
    have h : Metric.infDist x (spectrum ℂ (A + E)) ≤ ‖-E‖ := by
      have hmem : x ∈ spectrum ℂ ((A + E) + (-E)) := by
        have heq : (A + E) + (-E) = A := by abel
        rw [heq]
        exact hx
      exact infDist_le_norm_of_mem_spectrum_add (A := A + E) (E := -E) hmem
    rwa [norm_neg] at h
  · intro μ hμ
    exact infDist_le_norm_of_mem_spectrum_add (A := A) (E := E) hμ

end MathlibExt.Analysis.InnerProductSpace.BauerFike

end
