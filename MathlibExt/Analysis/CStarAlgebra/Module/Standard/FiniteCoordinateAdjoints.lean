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
# Adjointable finite standard-module coordinates

For nonunital C-star `B` and finite `I`, finite insertion `j_i : B → B^I` and evaluation `π_i :
B^I → B` satisfy `⟨j_i a,x⟩_B = star a * x_i` for the finite coefficient inner product. They
therefore form an adjointable pair on `FiniteStandard B I`, with insertion as the forward map
and evaluation as its adjoint.
-/

@[expose] public section

namespace CStarModule.Right

universe uB uI

variable {B : Type uB} [NonUnitalCStarAlgebra B] {I : Type uI} [Fintype I]

/-- **Adjointable finite coefficient insertion.** For a nonunital complex C-star algebra `B` and
finite index type `I`, the map `B → FiniteStandard B I` inserts its argument in coordinate `i`
and has adjoint `finiteCoord i`. -/
noncomputable def finiteSingleAdjointable (i : I) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    CStarModule.AdjointableOperator B B (FiniteStandard B I) := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  classical
  change CStarModule.AdjointableOperator B B (FiniteStandard B I)
  refine CStarModule.AdjointableOperator.ofAdjointPair
    (finiteSingle (B := B) (ι := I) i)
    (finiteCoord (B := B) (ι := I) i) ?_
  intro a y
  have hSingle : finiteSingle (B := B) (ι := I) i a =
      (WithCStarModule.equiv Bᵐᵒᵖ (I → B)).symm (Pi.single i a) := rfl
  have hPi :
      inner Bᵐᵒᵖ
        ((WithCStarModule.equiv Bᵐᵒᵖ (I → B)).symm (Pi.single i a)) y =
      inner Bᵐᵒᵖ a (y i) :=
    WithCStarModule.inner_single_left
      (A := Bᵐᵒᵖ) (E := fun _ : I => B) (i := i) y a
  have hUnop :
      CStarModule.rightInner (B := B)
        ((WithCStarModule.equiv Bᵐᵒᵖ (I → B)).symm (Pi.single i a)) y =
      CStarModule.rightInner (B := B) a (y i) :=
    congrArg (MulOpposite.unop : Bᵐᵒᵖ → B) hPi
  calc
    CStarModule.rightInner (B := B) (finiteSingle (B := B) (ι := I) i a) y =
        CStarModule.rightInner (B := B)
          ((WithCStarModule.equiv Bᵐᵒᵖ (I → B)).symm (Pi.single i a)) y :=
      congrArg (fun z : FiniteStandard B I =>
        CStarModule.rightInner (B := B) z y) hSingle
    _ = CStarModule.rightInner (B := B) a (y i) := hUnop
    _ = CStarModule.rightInner (B := B) a
        (finiteCoord (B := B) (ι := I) i y) :=
      congrArg (fun b : B => CStarModule.rightInner (B := B) a b)
        (finiteCoord_apply (B := B) (ι := I) i y).symm

/-- **Forward map of finite insertion.** For a nonunital complex C-star algebra `B` and finite
index type `I`, `(finiteSingleAdjointable i).toContinuousLinearMap = finiteSingle i`. -/
theorem finiteSingleAdjointable_toContinuousLinearMap (i : I) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    (finiteSingleAdjointable (B := B) (I := I) i).toContinuousLinearMap =
      finiteSingle (B := B) (ι := I) i := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  rfl

/-- **Adjoint of finite coefficient insertion.** For a nonunital complex C-star algebra `B` and
finite index type `I`, `(finiteSingleAdjointable i).adjoint = finiteCoord i`. -/
theorem finiteSingleAdjointable_adjoint (i : I) :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    (finiteSingleAdjointable (B := B) (I := I) i).adjoint =
      finiteCoord (B := B) (ι := I) i := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  rfl

end CStarModule.Right

end
