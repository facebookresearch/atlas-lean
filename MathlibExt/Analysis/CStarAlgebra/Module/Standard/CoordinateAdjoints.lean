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
# Adjointable coordinates of standard modules

For nonunital C-star `B` and arbitrary index type `I`, insertion `j_i : B → Standard B I` and
evaluation `π_i : Standard B I → B` form an adjoint pair. Their coefficient pairing is `⟨j_i
a,y⟩_B = star a * coord i y`.

They satisfy `π_i j_i = id_B` and `π_i j_j = 0` for `i ≠ j`. Each insertion is isometric and has
operator norm at most one, including the zero coefficient algebra. No unit in `B` is needed.
-/

@[expose] public section

noncomputable section

namespace CStarModule.Right.Standard

universe uB uι

variable {B : Type uB} [NonUnitalCStarAlgebra B] {ι : Type uι}

/-- **Adjointable coefficient insertion.** For a nonunital complex C-star algebra `B` and
arbitrary index type `I`, `singleAdjointable i : B → Standard B I` is the single-coordinate
inclusion with adjoint `coord i`. -/
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

/-- **Forward map of coefficient insertion.** For a nonunital complex C-star algebra `B` and
arbitrary index type `I`, `(singleAdjointable i).toContinuousLinearMap = single i`. -/
theorem singleAdjointable_toContinuousLinearMap (i : ι) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    (singleAdjointable (B := B) i).toContinuousLinearMap = single i := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  rfl

/-- **Coordinate map of the adjoint operator.** For a nonunital complex C-star algebra `B` and
arbitrary index type `I`, the continuous linear map underlying `(singleAdjointable
i).adjointOperator` is `coord i`. -/
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

/-- **Value of adjointable coefficient insertion.** For a nonunital complex C-star algebra `B` and
arbitrary index type `I`, `singleAdjointable i a = single i a` for every coefficient `a : B`. -/
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

/-- **Adjoint of coefficient insertion.** For a nonunital complex C-star algebra `B` and arbitrary
index type `I`, `(singleAdjointable i).adjoint = coord i`. -/
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

/-- **Evaluation of the coordinate adjoint.** For a nonunital complex C-star algebra `B` and
arbitrary index type `I`, `(singleAdjointable i).adjointOperator y = coord i y`. -/
theorem singleAdjointable_adjoint_apply (i : ι) (y : Standard B ι) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    (singleAdjointable i).adjointOperator y = coord i y := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  rfl

/-- **Pairing with a coefficient single.** For a nonunital complex C-star algebra `B` and
arbitrary index type `I`, `⟨single i a,y⟩_B = star a * coord i y`, with the starred
coefficient on the left. -/
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

/-- **Evaluation after insertion.** For a nonunital complex C-star algebra `B` and arbitrary index
type `I`, `(singleAdjointable i)* ∘ singleAdjointable i = id_B` on the coefficient
self-module. -/
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

/-- **Evaluation at a different coordinate.** For a nonunital complex C-star algebra `B` and
arbitrary index type `I`, if `i ≠ j`, `(singleAdjointable i)* ∘ singleAdjointable j = 0`. -/
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

/-- **Isometric coefficient insertion.** For a nonunital complex C-star algebra `B` and arbitrary
index type `I`, `singleAdjointable i` is an isometry between the coefficient norm and
standard-module norm. -/
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

/-- **Operator norm of coefficient insertion.** For a nonunital complex C-star algebra `B` and
arbitrary index type `I`, `‖singleAdjointable i‖ ≤ 1`, including the zero algebra. -/
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
