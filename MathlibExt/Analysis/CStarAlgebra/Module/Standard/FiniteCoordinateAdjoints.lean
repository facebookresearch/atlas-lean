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
# Adjointable finite coefficient coordinates

The existing finite coefficient insertion and evaluation are an actual
adjoint pair on the original finite right standard module. The pairing is
the stock finite Pi inner-product identity, specialized to the opposite
coefficient algebra and the constant coefficient family.

The original maps, coefficient-inner norm and module carrier are retained.
No coefficient unit, nonzero algebra, supplied adjoint or new norm is needed.
-/

@[expose] public section

namespace CStarModule.Right

universe uB uI

variable {B : Type uB} [NonUnitalCStarAlgebra B] {I : Type uI} [Fintype I]

/-- The existing finite coefficient insertion, with the existing coordinate
evaluation as its actual stored adjoint. -/
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

/-- The forward bounded map is literally the original finite insertion. -/
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

/-- The stored adjoint is literally the original finite evaluation. -/
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
