/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Realization weakness of the original raw identity-core diagonal.
import MathlibExt.AlgebraicTopology.SimplicialSpace.SAMEOriginalRawIdentityCoreNativeLift
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalRawZeroConstantPowerWeak
import MathlibExt.AlgebraicTopology.SimplicialSpace.WholePowerZeroOriginalMappingIso
import MathlibExt.AlgebraicTopology.SimplicialSpace.FullEEquivalenceTrivialFibration
import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialDiagonalWeakEquivalence
import MathlibExt.CategoryTheory.ClosedPowerInterchangeOriginalConstant
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalRawFullEForwardEvaluation

/-!
# Weakness of the SAME original raw identity-core diagonal

The original full-E forward evaluation is weak in every original coefficient
row. The whole native closed interchange and scalar mapping comparison identify
its diagonal source with raw(W raised to E)_0. The actual original raw constant
E-power section is weak by the independently constructed raw(E)_0 interval.
Their literal composite is the previously defined SAME rawIdentityCore.
No raw-unit WE, core WE, completeness, Raw-zero Kan or comparison fibration is
supplied as a premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory MonoidalClosed
open HomotopicalAlgebra CartesianMonoidalCategory
open scoped Simplicial MonoidalCategory SimplicialSpace.Inner
  SimplicialSpace.Cartesian SSet.modelCategoryQuillen

namespace SimplicialSpace.RezkCompletionCoreDiagonal
open RezkCompletionRaw SegalHomotopy WalkingEUnit
open WholePowerZeroOriginalMappingIso

/-- The original whole E-powers of EVERY original coefficient power, at zero. -/
def originalWholeEZeroDiagram (W : SimplicialSpace.{u}) : SimplicialObject SSet.{u} :=
  powerDiagram W ⋙ (ihom coherentSpace ⋙ outerZero)

/-- Whole closed interchange, retaining the actual inverse braid and EVERY
contravariant original coefficient operator before row evaluation. -/
def rawWholeEInterchangeIso (W : SimplicialSpace.{u}) :
    rowPowerDiagram (powerSpace W) (op ⦋0⦌) ≅ originalWholeEZeroDiagram W :=
  NatIso.ofComponents (fun n => outerZero.mapIso
    (ClosedPowerInterchange.interchange coherentSpace
      (coefficient.obj n.unop) W).symm) (by
    intro n m δ
    change outerZero.map ((pre (coefficient.map δ.unop)).app (powerSpace W)) ≫
        outerZero.map ((ClosedPowerInterchange.interchange coherentSpace
          (coefficient.obj m.unop) W).inv) =
      outerZero.map ((ClosedPowerInterchange.interchange coherentSpace
        (coefficient.obj n.unop) W).inv) ≫
          outerZero.map ((ihom coherentSpace).map
            ((pre (coefficient.map δ.unop)).app W))
    have h := congrArg outerZero.map
      (ClosedPowerInterchange.interchange_inv_coefficient_naturality
        coherentSpace (coefficient.map δ.unop) W)
    exact ((outerZero.map_comp _ _).symm.trans h).trans (outerZero.map_comp _ _))

/-- The scalar-end representation is target natural for EVERY coefficient map. -/
def wholeEZeroScalarEndIso (W : SimplicialSpace.{u}) :
    originalWholeEZeroDiagram W ≅ originalFullEEndDiagram W :=
  Functor.isoWhiskerLeft (powerDiagram W) (powerZeroScalarNatIso coherentSpace)

/-- The complete whole-row comparison is internally constructed, not an input. -/
def rawWholeEEndIso (W : SimplicialSpace.{u}) :
    rowPowerDiagram (powerSpace W) (op ⦋0⦌) ≅ originalFullEEndDiagram W :=
  rawWholeEInterchangeIso W ≪≫ wholeEZeroScalarEndIso W

set_option linter.unusedVariables false in
/-- The actual full-E constant maps are natural under all original operators. -/
def originalFullEConstant (W : SimplicialSpace.{u}) :
    rowPowerDiagram W (op ⦋0⦌) ⟶ originalFullEEndDiagram W where
  app n := FullEEquivalence.constantMap ((powerDiagram W).obj n)
  naturality n m δ :=
    FullEEquivalence.constantMap_naturality_target ((powerDiagram W).map δ)

/-- Interchange and the complete scalar-end comparison take the SAME original
raw constant-power target map to those SAME full-E constant maps. -/
theorem rawWholeEEndIso_constantPower (W : SimplicialSpace.{u}) :
    Functor.whiskerRight (powerDiagramMap (constantPower W))
        (forget ⋙ (evaluation SimplexCategoryᵒᵖ SSet.{u}).obj (op ⦋0⦌)) ≫
      (rawWholeEEndIso W).hom = originalFullEConstant W := by
  apply NatTrans.ext
  funext n
  change outerZero.map ((ihom (coefficient.obj n.unop)).map
      (curry (CartesianMonoidalCategory.snd coherentSpace W))) ≫
        (outerZero.map ((ClosedPowerInterchange.interchange coherentSpace
          (coefficient.obj n.unop) W).inv) ≫
          (powerZeroScalarIso coherentSpace ((powerDiagram W).obj n)).hom) =
    FullEEquivalence.constantMap ((powerDiagram W).obj n)
  have h := congrArg outerZero.map
    (ClosedPowerInterchangeOriginalConstant.interchange_inv_constantPower
      coherentSpace (coefficient.obj n.unop) W)
  have hc : outerZero.map ((ihom (coefficient.obj n.unop)).map
      (curry (CartesianMonoidalCategory.snd coherentSpace W))) ≫
        outerZero.map ((ClosedPowerInterchange.interchange coherentSpace
          (coefficient.obj n.unop) W).inv) =
      (WalkingEUnit.constantPower ((powerDiagram W).obj n)).hom.app (op ⦋0⦌) :=
    (outerZero.map_comp _ _).symm.trans h
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫
      (powerZeroScalarIso coherentSpace ((powerDiagram W).obj n)).hom) hc).trans
        (powerZeroScalarIso_constantPower ((powerDiagram W).obj n)))

/-- The literal constant/forward-evaluation composite is the original identity
core in each full power, without changing either endpoint or operator. -/
theorem originalFullEConstant_forwardEvaluation (W : SimplicialSpace.{u})
    (hW : segalSpaces W) :
    originalFullEConstant W ≫ originalFullEForwardEvaluation W hW =
      powerIdentityCore W hW := by
  apply NatTrans.ext
  funext n
  exact FullEEquivalence.constant_evaluation ((powerDiagram W).obj n)
    (powerDiagram_segal W hW n) SSet.coherentIso.forwardMap

/-- The actual full diagonal comparison out of raw(W raised to E)_0. -/
def rawFullEForwardEvaluation (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (rawCompletion (powerSpace W)).diagram _⦋0⦌ ⟶ coreDiagonal W hW :=
  (SSet.simplicialDiagonalFunctor.mapIso (rawWholeEEndIso W)).hom ≫
    SSet.simplicialDiagonalFunctor.map (originalFullEForwardEvaluation W hW)

/-- Weakness is derived from the actual whole-row Iso and genuine rowwise
forward evaluations, not from a prescribed core-weakness premise. -/
theorem rawFullEForwardEvaluation_weak (W : SimplicialSpace.{u})
    (hW : segalSpaces W) :
    SSet.realizationWeakEquivalences (rawFullEForwardEvaluation W hW) :=
  SSet.realizationWeakEquivalences.comp_mem _ _
    (SSet.realizationWeakEquivalences.of_isIso
      (SSet.simplicialDiagonalFunctor.mapIso (rawWholeEEndIso W)).hom)
    (originalFullEForwardEvaluation_diagonal_weak W hW)

/-- This whole composite IS the previously defined SAME rawIdentityCore. -/
theorem rawConstantPower_fullEForward_identity (W : SimplicialSpace.{u})
    (hW : segalSpaces W) :
    (rawCompletionMap (constantPower W)).hom.app (op ⦋0⦌) ≫
        rawFullEForwardEvaluation W hW = rawIdentityCore W hW := by
  change SSet.simplicialDiagonalFunctor.map
      (Functor.whiskerRight (powerDiagramMap (constantPower W))
        (forget ⋙ (evaluation SimplexCategoryᵒᵖ SSet.{u}).obj (op ⦋0⦌))) ≫
      (SSet.simplicialDiagonalFunctor.map (rawWholeEEndIso W).hom ≫
        SSet.simplicialDiagonalFunctor.map (originalFullEForwardEvaluation W hW)) =
    SSet.simplicialDiagonalFunctor.map (powerIdentityCore W hW)
  let r := Functor.whiskerRight (powerDiagramMap (constantPower W))
    (forget ⋙ (evaluation SimplexCategoryᵒᵖ SSet.{u}).obj (op ⦋0⦌))
  let s := (rawWholeEEndIso W).hom
  let t := originalFullEForwardEvaluation W hW
  have h : r ≫ s ≫ t = powerIdentityCore W hW :=
    (Category.assoc r s t).symm.trans
      ((congrArg (fun f => f ≫ t) (rawWholeEEndIso_constantPower W)).trans
        (originalFullEConstant_forwardEvaluation W hW))
  have hm : SSet.simplicialDiagonalFunctor.map (r ≫ s ≫ t) =
      SSet.simplicialDiagonalFunctor.map r ≫
        (SSet.simplicialDiagonalFunctor.map s ≫ SSet.simplicialDiagonalFunctor.map t) :=
    (SSet.simplicialDiagonalFunctor.map_comp r (s ≫ t)).trans
      (congrArg (fun f => SSet.simplicialDiagonalFunctor.map r ≫ f)
        (SSet.simplicialDiagonalFunctor.map_comp s t))
  exact hm.symm.trans (congrArg SSet.simplicialDiagonalFunctor.map h)

/-- The SAME actual original raw identity-core map is genuinely weak. Only
original RF Segalness is a premise; every intermediate weakness was derived. -/
theorem originalRawIdentityCore_weak (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    SSet.realizationWeakEquivalences (rawIdentityCore W hW) := by
  have hs := OriginalRawZeroConstantPowerWeak.originalRaw_constantPower_weak W
  have he := rawFullEForwardEvaluation_weak W hW
  have h := SSet.realizationWeakEquivalences.comp_mem _ _ hs he
  rw [rawConstantPower_fullEForward_identity] at h
  exact h

end SimplicialSpace.RezkCompletionCoreDiagonal
