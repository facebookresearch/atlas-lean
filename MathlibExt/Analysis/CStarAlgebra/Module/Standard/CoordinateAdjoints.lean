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

public import MathlibExt.Analysis.CStarAlgebra.Module.Standard
public import MathlibExt.Analysis.CStarAlgebra.Module.Adjointable.OfPair

/-!
# Coordinate adjoints on the actual standard right C-star module

For complete possibly nonunital coefficients, the existing coefficient single
and coordinate evaluation form an actual bounded adjoint pair. Their maps,
norms and module carriers are unchanged. The pairing uses the coefficient-valued
inner product and the source-order product `star a * coord i y`.

Canonical opposite-coefficient order and the actual self-module dictionary are
activated locally before the operator types. No unit-valued basis, adjoint of an
arbitrary bounded map, nonzero coefficient algebra or new norm is required.
-/

@[expose] public section

noncomputable section

namespace CStarModule.Right.Standard

universe uB uι

variable {B : Type uB} [NonUnitalCStarAlgebra B] {ι : Type uι}

/-- The existing coefficient single as an adjointable map, with the existing
coordinate evaluation as its stored adjoint. -/
noncomputable def singleAdjointable (i : ι) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    CStarModule.AdjointableOperator B B (Standard B ι) := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  change CStarModule.AdjointableOperator B B (Standard B ι)
  refine CStarModule.AdjointableOperator.ofAdjointPair
    (single (B := B) i) (coord (B := B) i) ?_
  intro a y
  calc
    CStarModule.rightInner (B := B) (single i a) y =
        ∑' j, star (coord j (single i a)) * coord j y :=
      rightInner_eq_tsum_coord _ _
    _ = star (coord i (single i a)) * coord i y :=
      tsum_eq_single i fun j hji => by
        rw [coord_single_ne hji, star_zero, zero_mul]
    _ = CStarModule.rightInner (B := B) a (coord i y) := by
      rw [coord_single_self, CStarModule.Right.rightInner_self]

/-- The forward bounded map is literally the original single. -/
theorem singleAdjointable_toContinuousLinearMap (i : ι) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    (singleAdjointable (B := B) i).toContinuousLinearMap = single i := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  rfl

/-- The reverse bounded map is literally the original coordinate evaluation. -/
theorem singleAdjointable_adjoint_toContinuousLinearMap (i : ι) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    (singleAdjointable (B := B) i).adjointOperator.toContinuousLinearMap =
      coord i := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  rfl

/-- The adjointable insertion has the original pointwise value. -/
@[simp]
theorem singleAdjointable_apply (i : ι) (a : B) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    singleAdjointable i a = single i a := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  rfl

/-- The stored adjoint is literally the original coordinate evaluation. -/
@[simp]
theorem singleAdjointable_adjoint (i : ι) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    (singleAdjointable (B := B) i).adjoint = coord i := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  rfl

/-- The constructed adjoint operator has the original coordinate value. -/
theorem singleAdjointable_adjoint_apply (i : ι) (y : Standard B ι) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    (singleAdjointable i).adjointOperator y = coord i y := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  rfl

/-- A coefficient single pairs with any vector by the literal coordinate
product, with the coefficient starred on the left. -/
theorem rightInner_single_coord (i : ι) (a : B) (y : Standard B ι) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    CStarModule.rightInner (B := B) (single i a) y =
      star a * coord i y := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  have h := (singleAdjointable (B := B) i).adjoint_inner a y
  change CStarModule.rightInner (B := B) (single i a) y =
    CStarModule.rightInner (B := B) a (coord i y) at h
  simpa only [CStarModule.Right.rightInner_self] using h

/-- Evaluation after insertion at the same index is the identity operator on
the actual coefficient self-module, without assuming a coefficient unit. -/
@[simp]
theorem singleAdjointable_adjoint_comp_self :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    ∀ i : ι, (singleAdjointable i).adjointOperator.comp (singleAdjointable i) =
      (1 : CStarModule.AdjointableOperator.End B B) := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  intro i
  apply CStarModule.AdjointableOperator.ext
  intro a
  change coord i (single i a) = a
  exact coord_single_self i a

/-- Evaluation at one index after insertion at a different index vanishes. -/
@[simp]
theorem singleAdjointable_adjoint_comp_of_ne :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    ∀ {i j : ι}, i ≠ j →
      (singleAdjointable i).adjointOperator.comp (singleAdjointable j) =
      (0 : CStarModule.AdjointableOperator.End B B) := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  intro i j hij
  apply CStarModule.AdjointableOperator.ext
  intro a
  change coord i (single j a) = 0
  exact coord_single_ne hij a

/-- Coefficient insertion is an isometry for the unchanged coefficient and
standard-module norms, including the zero coefficient algebra. -/
theorem singleAdjointable_isometry (i : ι) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    Isometry (singleAdjointable (B := B) i) := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  change Isometry (single (B := B) i)
  refine isometry_iff_dist_eq.mpr ?_
  intro a b
  rw [dist_eq_norm, dist_eq_norm, ← map_sub (single (B := B) i) a b]
  exact norm_single i (a - b)

/-- The actual insertion operator has norm at most one. Equality with one is
not asserted for the zero coefficient algebra. -/
theorem norm_singleAdjointable_le (i : ι) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    ‖singleAdjointable (B := B) i‖ ≤ 1 := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  rw [CStarModule.AdjointableOperator.norm_eq,
    singleAdjointable_toContinuousLinearMap]
  refine (single (B := B) i).opNorm_le_bound zero_le_one ?_
  intro a
  simp only [norm_single, one_mul, le_refl]

end CStarModule.Right.Standard

end

end
