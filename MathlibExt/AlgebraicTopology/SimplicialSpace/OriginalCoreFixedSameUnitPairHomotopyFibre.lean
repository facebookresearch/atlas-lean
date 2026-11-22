/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalCoreZeroPairHomotopyFibre
import MathlibExt.AlgebraicTopology.SimplicialSpace.SAMEOriginalRawIdentityCoreNativeLift
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BetaPairTrivialCofibration

/-!
# The actual original core comparison over the fixed SAME pair base

The weak base change is the baseline beta on BOTH raw object factors.
The entire SAME unit remains rawUnit followed by beta; its pair map is
not assumed weak. The source is the unchanged original equivalence core.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.RezkCompletionCoreDiagonal
open RezkCompletionRaw

/-- The fixed baseline beta on the original source-first/target-second pair. -/
def sameBaselineBetaPair (W : SimplicialSpace.{u}) :
    (rawCompletion W).diagram _⦋0⦌ ⨯ (rawCompletion W).diagram _⦋0⦌ ⟶
      (RezkCompletionData.completion.obj W).diagram _⦋0⦌ ⨯
        (RezkCompletionData.completion.obj W).diagram _⦋0⦌ :=
  prod.map (sameBetaZero W) (sameBetaZero W)

/-- The genuine scalar TCof beta gives pair weakness without RawW₀ Kan. -/
theorem sameBaselineBetaPair_weak (W : SimplicialSpace.{u}) :
    WeakEquivalence (sameBaselineBetaPair W) :=
  (weakEquivalence_iff _).mpr
    (SSet.betaPair_realizationWeak (sameBetaZero W) (sameBetaZero_trivialCofibration W))

/-- The original SAME coaugmentation on both prescribed object factors. -/
def sameOriginalUnitPair (W : SimplicialSpace.{u}) :
    (W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌) ⟶
      (RezkCompletionData.completion.obj W).diagram _⦋0⦌ ⨯
        (RezkCompletionData.completion.obj W).diagram _⦋0⦌ :=
  prod.map ((RezkCompletionData.unit.app W).hom.app (op ⦋0⦌))
    ((RezkCompletionData.unit.app W).hom.app (op ⦋0⦌))

/-- The actual raw pair followed by beta² is literally the SAME unit pair. -/
theorem originalRawUnitPair_betaPair (W : SimplicialSpace.{u}) :
    originalRawUnitPair W ≫ sameBaselineBetaPair W = sameOriginalUnitPair W := by
  change prod.map ((rawCompletionUnit W).hom.app (op ⦋0⦌))
        ((rawCompletionUnit W).hom.app (op ⦋0⦌)) ≫
      prod.map (sameBetaZero W) (sameBetaZero W) =
    prod.map (((rawCompletionUnit W).hom.app (op ⦋0⦌)) ≫ sameBetaZero W)
      (((rawCompletionUnit W).hom.app (op ⦋0⦌)) ≫ sameBetaZero W)
  exact prod.map_map _ _ _ _

/-- The whole original raw core endpoint followed by beta² is the SAME base. -/
theorem originalRawCoreEndpoint_betaPair (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    originalRawCoreEndpoint W hW ≫ sameBaselineBetaPair W = sameCoreBase W hW := by
  change (coreDiagonalInclusion W hW ≫ mappingEndpoint (rawCompletion W)) ≫
      sameBaselineBetaPair W = coreDiagonalInclusion W hW ≫
        (mappingEndpoint (rawCompletion W) ≫ sameBaselineBetaPair W)
  exact Category.assoc _ _ _

/-- Base transport retains the whole core diagonal and the original W₀ pair. -/
def originalCoreRawToSameUnitPairCospanMap (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    cospan (originalRawCoreEndpoint W hW) (originalRawUnitPair W) ⟶
      cospan (sameCoreBase W hW) (sameOriginalUnitPair W) :=
  cospanHomMk (sameBaselineBetaPair W) (𝟙 (coreDiagonal W hW))
    (𝟙 ((W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌)))
    (by
      change originalRawCoreEndpoint W hW ≫ sameBaselineBetaPair W =
        𝟙 (coreDiagonal W hW) ≫ sameCoreBase W hW
      simpa only [Category.id_comp] using originalRawCoreEndpoint_betaPair W hW)
    (by
      change originalRawUnitPair W ≫ sameBaselineBetaPair W =
        𝟙 ((W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌)) ≫ sameOriginalUnitPair W
      simpa only [Category.id_comp] using originalRawUnitPair_betaPair W)

/-- Every native cospan component is captured in its actual ordered position. -/
theorem originalCoreRawToSameUnitPairCospanMap_components
    (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (originalCoreRawToSameUnitPairCospanMap W hW).app WalkingCospan.one = sameBaselineBetaPair W ∧
      (originalCoreRawToSameUnitPairCospanMap W hW).app WalkingCospan.left = 𝟙 (coreDiagonal W hW) ∧
      (originalCoreRawToSameUnitPairCospanMap W hW).app WalkingCospan.right =
        𝟙 ((W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌)) :=
  ⟨rfl, rfl, rfl⟩

/-- The actual native HP functor preserves this componentwise weak beta² map. -/
theorem originalCoreRawToSameUnitPairHomotopyMap_weak
    (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    WeakEquivalence ((homotopyPullback (C := SSet.{u})).map
      (originalCoreRawToSameUnitPairCospanMap W hW)) := by
  apply homotopyPullback_map_weakEquivalence
  intro j
  cases j with
  | none => exact sameBaselineBetaPair_weak W
  | some pair =>
      cases pair with
      | left => exact inferInstanceAs (WeakEquivalence (𝟙 (coreDiagonal W hW)))
      | right => exact inferInstanceAs
          (WeakEquivalence (𝟙 ((W.diagram _⦋0⦌) ⨯ (W.diagram _⦋0⦌))))

/-- The actual whole original core maps to the HP over the fixed Hat pair,
through the same raw-unit kappa and the genuine beta² base transport. -/
def originalCoreToFixedSameUnitPairHomotopyPullback
    (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (SegalHomotopy.equivalenceSubcomplex W hW : SSet.{u}) ⟶
      (homotopyPullback (C := SSet.{u})).obj
        (cospan (sameCoreBase W hW) (sameOriginalUnitPair W)) :=
  originalCoreToRawUnitHomotopyPullback W hW ≫
    (homotopyPullback (C := SSet.{u})).map (originalCoreRawToSameUnitPairCospanMap W hW)

/-- Its weakness is derived from the original diagram and baseline beta.
No full-unit-pair WE, Raw-base Kan, core WE or completeness is supplied. -/
theorem originalCoreToFixedSameUnitPairHomotopyPullback_weak
    (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    WeakEquivalence (originalCoreToFixedSameUnitPairHomotopyPullback W hW) := by
  let : WeakEquivalence (originalCoreToRawUnitHomotopyPullback W hW) :=
    originalCoreToRawUnitHomotopyPullback_weak W hW
  let : WeakEquivalence ((homotopyPullback (C := SSet.{u})).map
      (originalCoreRawToSameUnitPairCospanMap W hW)) :=
    originalCoreRawToSameUnitPairHomotopyMap_weak W hW
  unfold originalCoreToFixedSameUnitPairHomotopyPullback
  infer_instance

end SimplicialSpace.RezkCompletionCoreDiagonal
