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

public import MathlibExt.Analysis.CStarAlgebra.Weight.PositiveCompression
public import MathlibExt.Analysis.CStarAlgebra.Weight.GNSPositiveFunctional
public import MathlibExt.Analysis.VonNeumannAlgebra.Weight
public import MathlibExt.Analysis.VonNeumannAlgebra.PositiveLUBLimit
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Original normal-weight values make the same GNS diagonal coefficient order normal

Original finite-square elements have finite positive compressed weight
values, by the original conjugation norm bound and scalar-weight monotonicity.
Normality of the same global weight applies to the literal compressed
positive family and its proved original LUB. Finite values and the actual
positive coefficient identity give preservation of the real diagonal LUB.

The bounded coefficient is the existing positive continuous linear map.
No normal-predual membership or selected representation model is an input.
That membership criterion and the computed GNS normal homomorphism remain
separate, as do full scalar extension and Tomita/modular/polar constructors.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set CStarAlgebra.ScalarWeight
open scoped Topology

noncomputable section

namespace VonNeumannAlgebra

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I : Type v} [Preorder I] [IsDirectedOrder I] [Nonempty I]

/-- A normal scalar weight makes its actual positive diagonal coefficient preserve positive LUBs. -/
theorem gnsDiagonalPositiveFunctional_preserves_boundedPositiveIsLUB
    (M : VonNeumannAlgebra H) (φ : Weight M) (hφ : IsNormalWeight M φ)
    (x : φ.finiteSquareSubmodule) (a : I → PositiveElement M) (s : PositiveElement M)
    (hmono : @Monotone I M inferInstance (CStarAlgebra.spectralOrder M).toPreorder (fun i => (a i : M)))
    (hbound : ∃ C : ℝ, ∀ i, ‖(a i : M)‖ ≤ C)
    (hLUB : @IsLUB M (CStarAlgebra.spectralOrder M).toLE (Set.range fun i => (a i : M)) (s : M)) :
    IsLUB (Set.range fun i => (φ.gnsDiagonalPositiveFunctional x (a i : M)).re)
      (φ.gnsDiagonalPositiveFunctional x (s : M)).re := by
  let : PartialOrder M := CStarAlgebra.spectralOrder M
  let : LE M := (CStarAlgebra.spectralOrder M).toLE
  let : StarOrderedRing M := CStarAlgebra.spectralOrderedRing M
  let : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
  let : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder (H →L[ℂ] H)
  let : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing (H →L[ℂ] H)
  let ι : M →⋆ₐ[ℂ] (H →L[ℂ] H) := M.toStarSubalgebra.subtype
  let operatorLE : LE M :=
    ⟨fun p q : M => @LE.le (H →L[ℂ] H) (CStarAlgebra.spectralOrder (H →L[ℂ] H)).toLE
      (p : H →L[ℂ] H) (q : H →L[ℂ] H)⟩
  have horders (p q : M) : @LE.le M (CStarAlgebra.spectralOrder M).toLE p q ↔
      @LE.le M operatorLE p q := by
    exact (NonUnitalStarAlgHom.map_le_map_iff (A := M) (B := H →L[ℂ] H)
      ι Subtype.val_injective).symm
  let b : I → PositiveElement M := fun i =>
    ⟨star (x : M) * (a i : M) * (x : M), star_left_conjugate_nonneg (a i).property (x : M)⟩
  let t : PositiveElement M :=
    ⟨star (x : M) * (s : M) * (x : M), star_left_conjugate_nonneg s.property (x : M)⟩
  have hmonoB : @Monotone I M inferInstance (CStarAlgebra.spectralOrder M).toPreorder
      (fun i => (b i : M)) := by
    intro i j hij
    exact star_left_conjugate_le_conjugate (hmono hij) (x : M)
  have hdir : DirectedOn (fun p q : PositiveElement M =>
      @LE.le M (CStarAlgebra.spectralOrder M).toLE (p : M) (q : M)) (Set.range b) := by
    rintro p ⟨i, rfl⟩ q ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    exact ⟨b k, Set.mem_range_self k, hmonoB hik, hmonoB hjk⟩
  obtain ⟨C, hC⟩ := hbound
  have hboundB : ∃ D : ℝ, ∀ p ∈ Set.range b, ‖(p : M)‖ ≤ D := by
    refine ⟨‖(x : M)‖ * C * ‖(x : M)‖, ?_⟩
    rintro p ⟨i, rfl⟩
    change ‖star (x : M) * (a i : M) * (x : M)‖ ≤ ‖(x : M)‖ * C * ‖(x : M)‖
    calc
      _ ≤ (‖star (x : M)‖ * ‖(a i : M)‖) * ‖(x : M)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ ‖(x : M)‖ * C * ‖(x : M)‖ := by
        rw [norm_star]
        gcongr
        exact hC i
  have hconjugate := starConjugation_preserves_boundedPositiveIsLUB M (x : M)
    (fun i => (a i : M)) (s : M) hmono (fun i => (a i).property) ⟨C, hC⟩ hLUB
  have himage : ((fun p : PositiveElement M => (p : M)) '' Set.range b) =
      Set.range (fun i => (b i : M)) := by
    ext y
    constructor
    · rintro ⟨p, ⟨i, rfl⟩, rfl⟩
      exact Set.mem_range_self i
    · rintro ⟨i, rfl⟩
      exact ⟨b i, Set.mem_range_self i, rfl⟩
  have hLUBB : @IsLUB M (CStarAlgebra.spectralOrder M).toLE
      ((fun p : PositiveElement M => (p : M)) '' Set.range b) (t : M) := by
    rw [himage]
    exact hconjugate
  have hdirOperator : DirectedOn (fun p q : PositiveElement M =>
      @LE.le M operatorLE (p : M) (q : M)) (Set.range b) := by
    intro p hp q hq
    obtain ⟨r, hr, hpr, hqr⟩ := hdir p hp q hq
    exact ⟨r, hr, (horders (p : M) (r : M)).mp hpr, (horders (q : M) (r : M)).mp hqr⟩
  have hLUBOperator : @IsLUB M operatorLE
      ((fun p : PositiveElement M => (p : M)) '' Set.range b) (t : M) := by
    constructor
    · intro p hp
      exact (horders p (t : M)).mp (hLUBB.1 hp)
    · intro q hq
      apply (horders (t : M) q).mp
      apply hLUBB.2
      intro p hp
      exact (horders p q).mpr (hq hp)
  have hnormal := hφ (Set.range b) (Set.range_nonempty b)
    hdirOperator hboundB t hLUBOperator
  have hvalueImage : (φ.value '' Set.range b) = Set.range (fun i => φ.value (b i)) := by
    ext y
    constructor
    · rintro ⟨p, ⟨i, rfl⟩, rfl⟩
      exact Set.mem_range_self i
    · rintro ⟨i, rfl⟩
      exact ⟨b i, Set.mem_range_self i, rfl⟩
  have hvalueLUB : IsLUB (Set.range fun i => φ.value (b i)) (φ.value t) := by
    rw [← hvalueImage]
    exact hnormal
  have hmonoValue : Monotone (fun i => φ.value (b i)) := by
    intro i j hij
    exact φ.value_mono (b i) (b j) (hmonoB hij)
  have htFinite : φ.value t ≠ ⊤ := (φ.value_positiveConjugate_lt_top x s).ne
  have hvalueLimit := tendsto_atTop_isLUB hmonoValue hvalueLUB
  have hrealLimit : Tendsto (fun i => (φ.value (b i)).toReal) atTop
      (𝓝 (φ.value t).toReal) := by
    simpa only [Function.comp_def] using (ENNReal.tendsto_toReal htFinite).comp hvalueLimit
  have hrealUpper : ∀ i, (φ.value (b i)).toReal ≤ (φ.value t).toReal := fun i =>
    ENNReal.toReal_mono htFinite (hvalueLUB.1 (Set.mem_range_self i))
  have hrealLUB : IsLUB (Set.range fun i => (φ.value (b i)).toReal) (φ.value t).toReal :=
    IsLUB.range_of_tendsto hrealUpper hrealLimit
  have hcoefficient (p : PositiveElement M) :
      (φ.gnsDiagonalPositiveFunctional x (p : M)).re =
        (φ.value ⟨star (x : M) * (p : M) * (x : M),
          star_left_conjugate_nonneg p.property (x : M)⟩).toReal := by
    change ((φ.gnsDiagonalPositiveFunctional x).toContinuousLinearMap (p : M)).re = _
    rw [φ.gnsDiagonalPositiveFunctional_toContinuousLinearMap,
      φ.gnsCoefficient_positive_value (p : M) p.property x]
    simp only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re]
  have hfunction : (fun i => (φ.gnsDiagonalPositiveFunctional x (a i : M)).re) =
      (fun i => (φ.value (b i)).toReal) := by
    funext i
    exact hcoefficient (a i)
  have hpoint : (φ.gnsDiagonalPositiveFunctional x (s : M)).re = (φ.value t).toReal :=
    hcoefficient s
  rw [hfunction, hpoint]
  exact hrealLUB

end VonNeumannAlgebra

end
