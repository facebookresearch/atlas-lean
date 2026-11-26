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

public import MathlibExt.Analysis.VonNeumannAlgebra.MaximalLocalCutoffIdentity
public import MathlibExt.Analysis.VonNeumannAlgebra.FiniteNormalApproximation
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Positive order-normal functionals belong to the normal span

Let `M` be a concrete von Neumann algebra and `ψ : M → ℂ` a positive bounded complex-linear
functional. Suppose `Re ψ` preserves least upper bounds of nonempty directed increasing positive
families that are bounded in operator norm.

Then `ψ` belongs to the normal-functional Banach space `M_*`, the norm-closed span of vector
functionals. No normal-functional membership is assumed in this order-normality criterion.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set CStarAlgebra.ScalarWeight
open scoped Topology BigOperators

namespace VonNeumannAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Positive least-upper-bound preservation implies normal membership.** Let `H` be a
complete complex Hilbert space and `M ⊆ B(H)` a concrete von Neumann algebra. Write
`ω_(ξ,η)(x)=⟨ξ,xη⟩` for its vector functionals. Let `M_*` be their norm-closed complex
span in the continuous dual `M*`. let `ψ : PositiveContinuousLinearMap ℂ M ℂ`. Assume that
for every nonempty directed monotone norm-bounded positive family `a_i` with least upper
bound `s`, `Re ψ(s)` is the least upper bound of `{Re ψ(a_i)}`. Then the bounded
functional underlying `ψ` belongs to `M_*`. -/
theorem positiveFunctional_mem_normalFunctionalSpace_of_positiveLUBs (M : VonNeumannAlgebra H) :
    letI : PartialOrder M := CStarAlgebra.spectralOrder M
    letI : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
    ∀ (ψ : PositiveContinuousLinearMap ℂ M ℂ),
      (∀ (I : Type u) [Preorder I] [IsDirectedOrder I] [Nonempty I]
        (a : I → PositiveElement M) (s : PositiveElement M),
        @Monotone I M inferInstance (CStarAlgebra.spectralOrder M).toPreorder (fun i => (a i : M)) →
        (∃ C : ℝ, ∀ i, ‖(a i : M)‖ ≤ C) →
        @IsLUB M (CStarAlgebra.spectralOrder M).toLE (Set.range fun i => (a i : M)) (s : M) →
        IsLUB (Set.range fun i => (ψ.toContinuousLinearMap (a i : M)).re)
          (ψ.toContinuousLinearMap (s : M)).re) →
      ψ.toContinuousLinearMap ∈ normalFunctionalSpace M := by
  classical
  let sourceOrder : PartialOrder M := CStarAlgebra.spectralOrder M
  let : PartialOrder M := sourceOrder
  let : Preorder M := sourceOrder.toPreorder
  let : LE M := sourceOrder.toLE
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  let : IsOrderedAddMonoid M := StarOrderedRing.toIsOrderedAddMonoid
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  let : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ
  intro ψ hnormal
  let φ : StrongDual ℂ M := ψ.toContinuousLinearMap
  let S := maximalLocalProjectionFamily M ψ
  let P := maximalLocalPositiveFiniteCutoffs M ψ
  let a := fun t : Finset S.val => P.val t
  have hidentity : @IsLUB M (CStarAlgebra.spectralOrder M).toLE
      (Set.range fun t => (a t : M)) 1 := by
    have h := maximalLocalCutoffSupremum_isLUB M ψ
    rw [maximalLocalCutoffSupremum_eq_one M ψ] at h
    exact h
  let one : PositiveElement M := ⟨1, (IsStarProjection.one M).nonneg⟩
  have hvalueLUB : IsLUB (Set.range fun t => (φ (a t : M)).re) (φ 1).re :=
    hnormal (Finset S.val) a one (maximalLocalPositiveFiniteCutoffs_monotone M ψ)
      ⟨1, maximalLocalPositiveFiniteCutoffs_norm_le_one M ψ⟩ hidentity
  have hmono : Monotone (fun t : Finset S.val => (φ (a t : M)).re) := by
    intro t v htv
    have h := ψ.monotone' ((maximalLocalPositiveFiniteCutoffs_monotone M ψ) htv)
    have hstandard : @LE.le ℂ Complex.partialOrder.toLE (φ (a t : M)) (φ (a v : M)) := by
      have hsource : @LE.le ℂ (CStarAlgebra.spectralOrder ℂ).toLE
          (φ (a t : M)) (φ (a v : M)) := h
      have hspectral : @LE.le ℂ (CStarAlgebra.spectralOrder ℂ).toLE
          (φ (a t : M)) (φ (a v : M)) ↔
          ∃ d, d ∈ AddSubmonoid.closure (Set.range fun z : ℂ => star z * z) ∧
            φ (a v : M) = φ (a t : M) + d := StarOrderedRing.le_iff _ _
      have hstock : @LE.le ℂ Complex.partialOrder.toLE (φ (a t : M)) (φ (a v : M)) ↔
          ∃ d, d ∈ AddSubmonoid.closure (Set.range fun z : ℂ => star z * z) ∧
            φ (a v : M) = φ (a t : M) + d := by
        let : PartialOrder ℂ := Complex.partialOrder
        let : LE ℂ := Complex.partialOrder.toLE
        let : StarOrderedRing ℂ := RCLike.toStarOrderedRing
        exact StarOrderedRing.le_iff _ _
      exact hstock.mpr (hspectral.mp hsource)
    exact hstandard.1
  have hvalueLimit := tendsto_atTop_isLUB hmono hvalueLUB
  have hrealResidual : Tendsto (fun t : Finset S.val => (φ (1 - (a t : M))).re) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds : Tendsto (fun _t : Finset S.val => (φ 1).re) atTop _).sub hvalueLimit
    simpa only [sub_self, φ.map_sub, Complex.sub_re] using h
  have hreal (t : Finset S.val) : φ (1 - (a t : M)) = ((φ (1 - (a t : M))).re : ℂ) := by
    have hpositive : 0 ≤ φ (1 - (a t : M)) :=
      ψ.map_nonneg (maximalLocalPositiveFiniteCutoffs_isStarProjection M ψ t).one_sub_nonneg
    have him : (φ (1 - (a t : M))).im = 0 :=
      (RCLike.im_eq_zero_iff_isSelfAdjoint).mpr (IsSelfAdjoint.of_nonneg hpositive)
    apply Complex.ext
    · exact (Complex.ofReal_re _).symm
    · exact him.trans (Complex.ofReal_im _).symm
  have hnormResidual : Tendsto (fun t : Finset S.val => ‖φ (1 - (a t : M))‖) atTop (𝓝 0) := by
    have hnorm (t : Finset S.val) : ‖φ (1 - (a t : M))‖ = ‖(φ (1 - (a t : M))).re‖ := by
      rw [hreal t]
      exact Complex.norm_real _
    have hfunction : (fun t : Finset S.val => ‖φ (1 - (a t : M))‖) =
        (fun t : Finset S.val => ‖(φ (1 - (a t : M))).re‖) := funext hnorm
    rw [hfunction]
    have h := hrealResidual.norm
    rw [norm_zero] at h
    exact h
  have herrorLimit : Tendsto (fun t : Finset S.val =>
      Real.sqrt (‖φ‖ * ‖φ (1 - (a t : M))‖)) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.continuousAt.tendsto).comp
      ((tendsto_const_nhds : Tendsto (fun _t : Finset S.val => ‖φ‖) atTop _).mul hnormResidual)
    simpa only [mul_zero, Real.sqrt_zero, Function.comp_def] using h
  let p : S.val → M := fun i => i.val
  have hp (i : S.val) : IsStarProjection (p i) := (S.property.1 i.val i.property).1
  let ξ (i : S.val) : H := Classical.choose (S.property.1 i.val i.property).2.2
  have hlocal (i : S.val) : ∀ b : PositiveElement M,
      @LE.le M (CStarAlgebra.spectralOrder M).toLE (b : M) (p i) →
      (φ (b : M)).re ≤ (vectorFunctional M (ξ i) (ξ i) (b : M)).re :=
    Classical.choose_spec (S.property.1 i.val i.property).2.2
  have horthogonal (i j : S.val) (hij : i ≠ j) : p i * p j = 0 :=
    S.property.2.1 i.property j.property (fun h => hij (Subtype.ext h))
  let ρ (t : Finset S.val) := finiteOrthogonalNormalApproximation M ψ p hp horthogonal ξ hlocal t
  have hbound (t : Finset S.val) : ‖φ - (ρ t).val.val‖ ≤
      Real.sqrt (‖φ‖ * ‖φ (1 - (a t : M))‖) := by
    have h := (ρ t).property.2
    rw [(maximalLocalPositiveFiniteCutoffs_value M ψ) t]
    exact h
  have hclosure : φ ∈ closure (normalFunctionalSpace M : Set (StrongDual ℂ M)) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    have heventually := herrorLimit.eventually_lt_const hε
    obtain ⟨t, ht⟩ := heventually.exists
    refine ⟨(ρ t).val.val, (ρ t).val.property, ?_⟩
    rw [dist_eq_norm]
    exact (hbound t).trans_lt ht
  rw [(normalFunctionalSpace_isClosed M).closure_eq] at hclosure
  exact hclosure

end

end VonNeumannAlgebra
