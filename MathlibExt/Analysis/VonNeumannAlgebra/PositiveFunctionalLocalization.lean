/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Weight
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalFunctional
public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive

/-!
# Vector bounds from local positive-functional comparison

For a star projection `p ∈ M`, a vector `ξ∈H` and a bounded functional `ψ`, assume `Re ψ(b)≤Re
⟨ξ,bξ⟩` for all positive `b≤p`. Then `Re ψ((ap)*ap)≤‖apξ‖²` for every `a∈M`.

If `ψ` is also positive, Cauchy–Schwarz yields `|ψ(ap)|²≤|ψ(1)|‖apξ‖²`. This is a local norm
estimate; normality of `ψ` is not assumed.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CStarAlgebra.ScalarWeight
open scoped InnerProductSpace

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Local comparison bounds a positive Gram corner.** Let `H` be a complete complex Hilbert
space and `M ⊆ B(H)` a concrete von Neumann algebra. let `ψ∈M*`, `p∈M` a star projection
and `ξ∈H` satisfy `Re ψ(b)≤Re ⟨ξ,bξ⟩` for all `0≤b≤p`. Then for every `a∈M`, `Re
ψ((ap)*ap)≤‖apξ‖²`. Positivity of `ψ` is not required for this first estimate. -/
theorem positiveCompression_re_le_of_local_vector_comparison (M : VonNeumannAlgebra H)
    (ψ : StrongDual ℂ M) (p : M) (hp : IsStarProjection p) (ξ : H)
    (hlocal : ∀ b : PositiveElement M,
      @LE.le M (CStarAlgebra.spectralOrder M).toLE (b : M) p →
      (ψ (b : M)).re ≤ (vectorFunctional M ξ ξ (b : M)).re) (a : M) :
    (ψ (star (a * p) * (a * p))).re ≤ ‖((a * p : M) : H →L[ℂ] H) ξ‖ ^ 2 := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : LE M := (CStarAlgebra.spectralOrder M).toLE
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  let t : M := star (a * p) * (a * p)
  let c : ℝ := ‖star a * a‖ + 1
  have hc : 0 < c := by
    dsimp only [c]
    linarith [norm_nonneg (star a * a)]
  have hpstar : star p = p := hp.isSelfAdjoint.star_eq
  have hp0 : 0 ≤ p := by
    simpa only [hpstar, hp.isIdempotentElem.eq] using star_mul_self_nonneg p
  have ht0 : 0 ≤ t := star_mul_self_nonneg (a * p)
  have hbase : t ≤ ‖star a * a‖ • p := by
    have h := CStarAlgebra.star_left_conjugate_le_norm_smul p (star a * a)
      (IsSelfAdjoint.star_mul_self a)
    simpa only [t, star_mul, hpstar, mul_assoc, hp.isIdempotentElem.eq] using h
  have hbound : t ≤ c • p :=
    hbase.trans (smul_le_smul_of_nonneg_right (by dsimp only [c]; linarith) hp0)
  have hscaled : c⁻¹ • t ≤ p := by
    have h := smul_le_smul_of_nonneg_left hbound (inv_pos.mpr hc).le
    simpa only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] using h
  have hsmall0 : 0 ≤ c⁻¹ • t := smul_nonneg (inv_pos.mpr hc).le ht0
  have hcomparison := hlocal ⟨c⁻¹ • t, hsmall0⟩ hscaled
  have hψ : (ψ (c⁻¹ • t)).re = c⁻¹ * (ψ t).re := by
    change RCLike.re (ψ (c⁻¹ • t)) = c⁻¹ * RCLike.re (ψ t)
    rw [ψ.map_smul_of_tower, RCLike.smul_re]
  have hvector : (vectorFunctional M ξ ξ (c⁻¹ • t)).re =
      c⁻¹ * (vectorFunctional M ξ ξ t).re := by
    change RCLike.re (vectorFunctional M ξ ξ (c⁻¹ • t)) =
      c⁻¹ * RCLike.re (vectorFunctional M ξ ξ t)
    rw [(vectorFunctional M ξ ξ).map_smul_of_tower, RCLike.smul_re]
  change (ψ (c⁻¹ • t)).re ≤ (vectorFunctional M ξ ξ (c⁻¹ • t)).re at hcomparison
  rw [hψ, hvector] at hcomparison
  have hfull : (ψ t).re ≤ (vectorFunctional M ξ ξ t).re := by
    have hcinv : 0 < c⁻¹ := inv_pos.mpr hc
    nlinarith
  have hvalue : (vectorFunctional M ξ ξ t).re = ‖((a * p : M) : H →L[ℂ] H) ξ‖ ^ 2 := by
    rw [vectorFunctional_apply]
    let A : H →L[ℂ] H := ((a * p : M) : H →L[ℂ] H)
    change RCLike.re ⟪ξ, (ContinuousLinearMap.adjoint A ∘L A) ξ⟫_ℂ = ‖A ξ‖ ^ 2
    exact (ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right A ξ).symm
  rw [← hvalue]
  exact hfull

/-- **Vector bound for a positive localized functional.** Let `H` be a complete complex
Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Let `ψ : M → ℂ` be a positive
bounded complex-linear functional for the spectral orders. Let `p ∈ M` be a star
projection and `ξ ∈ H` satisfy `Re ψ(b)≤Re ⟨ξ,bξ⟩` for every positive `b≤p`. for every
`a∈M`, `|ψ(ap)|²≤|ψ(1)|*‖apξ‖²`. -/
theorem localizedPositiveFunctional_norm_sq_le_vector (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ) (p : M) (_hp : IsStarProjection p) (ξ : H),
      (∀ b : PositiveElement M,
        @LE.le M (CStarAlgebra.spectralOrder M).toLE (b : M) p →
        (ψ.toContinuousLinearMap (b : M)).re ≤ (vectorFunctional M ξ ξ (b : M)).re) →
      ∀ a : M, ‖ψ.toContinuousLinearMap (a * p)‖ ^ 2 ≤
        ‖ψ.toContinuousLinearMap 1‖ * ‖((a * p : M) : H →L[ℂ] H) ξ‖ ^ 2 := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : LE M := (CStarAlgebra.spectralOrder M).toLE
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  intro ψ p hp ξ hlocal a
  let φ : StrongDual ℂ M := ψ.toContinuousLinearMap
  have horders (z w : ℂ) : @LE.le ℂ (CStarAlgebra.spectralOrder ℂ).toLE z w ↔
      @LE.le ℂ Complex.partialOrder.toLE z w := by
    have hspectral : @LE.le ℂ (CStarAlgebra.spectralOrder ℂ).toLE z w ↔
        ∃ d, d ∈ AddSubmonoid.closure (Set.range fun s : ℂ => star s * s) ∧ w = z + d := by
      let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
      let : LE ℂ := (CStarAlgebra.spectralOrder ℂ).toLE
      let : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ
      exact StarOrderedRing.le_iff z w
    have hstandard : @LE.le ℂ Complex.partialOrder.toLE z w ↔
        ∃ d, d ∈ AddSubmonoid.closure (Set.range fun s : ℂ => star s * s) ∧ w = z + d := by
      let : PartialOrder ℂ := Complex.partialOrder
      let : LE ℂ := Complex.partialOrder.toLE
      let : StarOrderedRing ℂ := RCLike.toStarOrderedRing
      exact StarOrderedRing.le_iff z w
    exact hspectral.trans hstandard.symm
  have hmonotone (x y : M) (hxy : @LE.le M (CStarAlgebra.spectralOrder M).toLE x y) :
      @LE.le ℂ (CStarAlgebra.spectralOrder ℂ).toLE (φ x) (φ y) := ψ.monotone' hxy
  let t : M := star (a * p) * (a * p)
  have hpositive : @LE.le ℂ (CStarAlgebra.spectralOrder ℂ).toLE 0 (φ t) :=
    ψ.map_nonneg (star_mul_self_nonneg (a * p))
  have hnorm : ‖φ t‖ = (φ t).re := by
    have hstandard := (horders 0 (φ t)).mp hpositive
    have h := congrArg (fun z : ℂ => z.re) (Complex.eq_coe_norm_of_nonneg hstandard)
    simpa only [Complex.ofReal_re] using h.symm
  have hcomparison := positiveCompression_re_le_of_local_vector_comparison M φ p hp ξ hlocal a
  have hcs : ‖φ (a * p)‖ ^ 2 ≤ ‖φ 1‖ * ‖φ t‖ := by
    let : PartialOrder ℂ := Complex.partialOrder
    let : LE ℂ := Complex.partialOrder.toLE
    let f : PositiveLinearMap ℂ M ℂ :=
      { __ := φ.toLinearMap
        monotone' := by
          intro x y hxy
          exact (horders (φ x) (φ y)).mp (hmonotone x y hxy) }
    have hf (z : M) : f z = φ z := rfl
    have h := PositiveLinearMap.norm_map_star_mul_sq_le f (1 : M) (a * p)
    simpa only [hf, t, star_one, one_mul, mul_one] using h
  calc
    ‖ψ.toContinuousLinearMap (a * p)‖ ^ 2 ≤ ‖φ 1‖ * ‖φ t‖ := hcs
    _ = ‖φ 1‖ * (φ t).re := by rw [hnorm]
    _ ≤ ‖φ 1‖ * ‖((a * p : M) : H →L[ℂ] H) ξ‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hcomparison (norm_nonneg _)

end

end VonNeumannAlgebra
