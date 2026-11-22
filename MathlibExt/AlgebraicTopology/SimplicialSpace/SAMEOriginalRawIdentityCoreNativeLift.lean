/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Actual raw identity/core diagonal, fixed beta lift, and its literal prefix equations.
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalCorePowerDiagonalSelector
import MathlibExt.AlgebraicTopology.SimplicialSpace.SAMECoreDiagonalScalarRectification
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BetaPrefixedNativeLiftingCompletenessAssembly

/-!
# Lifting identity maps through core rectification

For a Segal space whose designated completion is Segal, the raw identity-core map and the
degree-zero baseline trivial cofibration determine a scalar lift into the rectified core. The
lift satisfies its full prefix and ordered endpoint equations, and recovers the target identity
comparison after precomposition by the baseline unit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.RezkCompletionCoreDiagonal
open RezkCompletionRaw SegalHomotopy

/-- Every original simplicial-space map preserves the actual core identity degeneracy. -/
theorem equivalenceIdentity_naturality {A B : SimplicialSpace.{u}}
    (f : A ⟶ B) (hA : segalSpaces A) (hB : segalSpaces B) :
    f.hom.app (op ⦋0⦌) ≫ equivalenceIdentity B hB =
      equivalenceIdentity A hA ≫ equivalenceMap f hA hB := by
  apply (cancel_mono (equivalenceSubcomplex B hB).ι).mp
  rw [Category.assoc, equivalenceIdentity_ι, Category.assoc,
    equivalenceMap_ι, ← Category.assoc, equivalenceIdentity_ι]
  exact (SimplicialObject.σ_naturality f.hom (0 : Fin 1)).symm

set_option linter.unusedVariables false in
/-- The actual identity maps of all original powers form a natural transformation
into the same core-power diagram, retaining every coefficient operator. -/
def powerIdentityCore (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    rowPowerDiagram W (op ⦋0⦌) ⟶ corePowerDiagram W hW where
  app n := equivalenceIdentity ((powerDiagram W).obj n) (powerDiagram_segal W hW n)
  naturality n m δ := equivalenceIdentity_naturality _ _ _

/-- The SAME raw identity-core map is the diagonal of those actual identity maps. -/
def rawIdentityCore (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (rawCompletion W).diagram _⦋0⦌ ⟶ coreDiagonal W hW :=
  SSet.simplicialDiagonalFunctor.map (powerIdentityCore W hW)

/-- Its inclusion is literally the original raw-completion identity degeneracy. -/
theorem rawIdentityCore_ι (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    rawIdentityCore W hW ≫ coreDiagonalInclusion W hW =
      (rawCompletion W).diagram.σ (0 : Fin 1) := by
  change SSet.simplicialDiagonalFunctor.map (powerIdentityCore W hW) ≫
      SSet.simplicialDiagonalFunctor.map (corePowerInclusion W hW) =
    SSet.simplicialDiagonalFunctor.map
      ((powerDiagram W ⋙ forget).flip.map (SimplexCategory.σ (0 : Fin 1)).op)
  rw [← SSet.simplicialDiagonalFunctor.map_comp]
  apply congrArg SSet.simplicialDiagonalFunctor.map
  apply NatTrans.ext
  funext n
  exact equivalenceIdentity_ι _ _

/-- The actual core comparison sends that raw identity to the same target identity
behind beta-zero, with no supplied section or identity-map weakness. -/
theorem rawIdentityCore_comparison {W V : SimplicialSpace.{u}}
    (β : rawCompletion W ⟶ V) (hW : segalSpaces W) (hV : segalSpaces V) :
    rawIdentityCore W hW ≫ coreDiagonalComparison β hW hV =
      β.hom.app (op ⦋0⦌) ≫ equivalenceIdentity V hV := by
  apply (cancel_mono (equivalenceSubcomplex V hV).ι).mp
  rw [Category.assoc, coreDiagonalComparison_ι, ← Category.assoc,
    rawIdentityCore_ι, Category.assoc, equivalenceIdentity_ι]
  exact SimplicialObject.σ_naturality β.hom (0 : Fin 1)

/-- The fixed SAME beta-zero is the baseline unit of the original raw row zero. -/
def sameBetaZero (W : SimplicialSpace.{u}) :
    (rawCompletion W).diagram _⦋0⦌ ⟶
      (RezkCompletionData.completion.obj W).diagram _⦋0⦌ :=
  (RezkBaselineReplacement.unit.app (rawCompletion W)).hom.app (op ⦋0⦌)

/-- Its genuine trivial-cofibration property is derived from the native baseline
Mono and weak component facts; no RawW-zero Kan premise is needed. -/
theorem sameBetaZero_trivialCofibration (W : SimplicialSpace.{u}) :
    trivialCofibrations SSet.{u} (sameBetaZero W) := by
  have h := RezkBaselineReplacement.unit_components (rawCompletion W) 0
  let : Mono (sameBetaZero W) := h.1
  have hcof : Cofibration (sameBetaZero W) :=
    (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
  have hweak : WeakEquivalence (sameBetaZero W) :=
    (weakEquivalence_iff _).mpr h.2
  exact (mem_trivialCofibrations_iff _).mpr ⟨hcof, hweak⟩

/-- The top arrow is the actual raw identity map followed by the scalar TCof factor. -/
def sameRawIdentityEvaluation (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    (rawCompletion W).diagram _⦋0⦌ ⟶ (sameCoreRectification W hW hHat).Z :=
  rawIdentityCore W hW ≫ (sameCoreRectification W hW hHat).i

/-- The SAME lift square uses that raw top map and the genuine beta-zero;
its bottom is the target identity followed by the ordered core endpoint. -/
theorem sameRawIdentityEvaluation_square (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    sameRawIdentityEvaluation W hW hHat ≫ sameRectifiedCoreBase W hW hHat =
      sameBetaZero W ≫ equivalenceIdentity (RezkCompletionData.completion.obj W) hHat ≫
        coreEndpoint (RezkCompletionData.completion.obj W) hHat := by
  rw [sameRawIdentityEvaluation, sameRectifiedCoreBase, ← Category.assoc,
    Category.assoc (rawIdentityCore W hW),
    (sameCoreRectification W hW hHat).fac]
  rw [← Category.assoc (sameBetaZero W)
    (equivalenceIdentity (RezkCompletionData.completion.obj W) hHat)
    (coreEndpoint (RezkCompletionData.completion.obj W) hHat)]
  exact congrArg (fun f => f ≫ coreEndpoint (RezkCompletionData.completion.obj W) hHat)
    (rawIdentityCore_comparison (RezkBaselineReplacement.unit.app (rawCompletion W)) hW hHat)

/-- Native lifting constructs L; the caller supplies no lift or completion outcome. -/
def sameCoreIdentityLift (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    (RezkCompletionData.completion.obj W).diagram _⦋0⦌ ⟶
      (sameCoreRectification W hW hHat).Z := by
  have hb := (mem_trivialCofibrations_iff _).mp (sameBetaZero_trivialCofibration W)
  letI : Cofibration (sameBetaZero W) := hb.1
  letI : WeakEquivalence (sameBetaZero W) := hb.2
  letI : Fibration (sameRectifiedCoreBase W hW hHat) :=
    (sameCoreRectification_fibrations W hW hHat).2
  exact SSet.betaLift (sameBetaZero W) (sameRawIdentityEvaluation W hW hHat)
    (sameRectifiedCoreBase W hW hHat)
    (equivalenceIdentity (RezkCompletionData.completion.obj W) hHat ≫
      coreEndpoint (RezkCompletionData.completion.obj W) hHat)
    (sameRawIdentityEvaluation_square W hW hHat)

/-- The literal beta prefix followed by L is the actual original raw top map. -/
theorem sameCoreIdentityLift_prefixed_raw (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    sameBetaZero W ≫ sameCoreIdentityLift W hW hHat =
      sameRawIdentityEvaluation W hW hHat := by
  have hb := (mem_trivialCofibrations_iff _).mp (sameBetaZero_trivialCofibration W)
  let : Cofibration (sameBetaZero W) := hb.1
  let : WeakEquivalence (sameBetaZero W) := hb.2
  let : Fibration (sameRectifiedCoreBase W hW hHat) :=
    (sameCoreRectification_fibrations W hW hHat).2
  exact SSet.betaLift_prefixed_evaluation (sameBetaZero W)
    (sameRawIdentityEvaluation W hW hHat) (sameRectifiedCoreBase W hW hHat)
    (equivalenceIdentity (RezkCompletionData.completion.obj W) hHat ≫
      coreEndpoint (RezkCompletionData.completion.obj W) hHat)
    (sameRawIdentityEvaluation_square W hW hHat)

/-- The same constructed lift has its exact original ordered identity endpoint equation. -/
theorem sameCoreIdentityLift_endpoint (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    sameCoreIdentityLift W hW hHat ≫ sameRectifiedCoreBase W hW hHat =
      equivalenceIdentity (RezkCompletionData.completion.obj W) hHat ≫
        coreEndpoint (RezkCompletionData.completion.obj W) hHat := by
  have hb := (mem_trivialCofibrations_iff _).mp (sameBetaZero_trivialCofibration W)
  let : Cofibration (sameBetaZero W) := hb.1
  let : WeakEquivalence (sameBetaZero W) := hb.2
  let : Fibration (sameRectifiedCoreBase W hW hHat) :=
    (sameCoreRectification_fibrations W hW hHat).2
  exact SSet.betaLift_endpoint_equation (sameBetaZero W)
    (sameRawIdentityEvaluation W hW hHat) (sameRectifiedCoreBase W hW hHat)
    (equivalenceIdentity (RezkCompletionData.completion.obj W) hHat ≫
      coreEndpoint (RezkCompletionData.completion.obj W) hHat)
    (sameRawIdentityEvaluation_square W hW hHat)

/-- The full SAME identity comparison equation follows behind beta-zero.
No monomorphism cancellation or supplied core weakness is used. -/
theorem sameCoreIdentityLift_prefixed_identity (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    sameBetaZero W ≫ sameCoreIdentityLift W hW hHat ≫
        (sameCoreRectification W hW hHat).p =
      sameBetaZero W ≫ equivalenceIdentity (RezkCompletionData.completion.obj W) hHat := by
  rw [← Category.assoc, sameCoreIdentityLift_prefixed_raw,
    sameRawIdentityEvaluation, Category.assoc, (sameCoreRectification W hW hHat).fac]
  exact rawIdentityCore_comparison _ _ _

end SimplicialSpace.RezkCompletionCoreDiagonal
