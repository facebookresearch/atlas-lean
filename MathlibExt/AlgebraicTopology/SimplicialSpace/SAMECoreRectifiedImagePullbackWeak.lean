/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SAMECoreImageHomotopyComparison

/-!
# Actual rectified comparison over the SAME unit image pair

The original whole-core comparison is factored by the actual scalar TCof/Fib
factorization. Native HP invariance handles its genuine TCof prefix, and the
derived original core HP comparison supplies the other side of the square.
Both rectified endpoint projections are actual fibrations. Their ordinary
pullback comparison over the full Unit9 pair is then weak, without p-WE input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.RezkCompletionCoreDiagonal

/-- The actual fibration factor uses the same native target-core endpoint. -/
def sameRectifiedNativeCoreBase (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    (sameCoreRectification W hW hHat).Z ⟶
      (RezkCompletionData.completion.obj W).diagram _⦋0⦌ ⨯
        (RezkCompletionData.completion.obj W).diagram _⦋0⦌ :=
  (sameCoreRectification W hW hHat).p ≫
    SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat

/-- Both actual maps to the fixed pair base are fibrations by composition. -/
theorem sameRectifiedNativeCoreBase_fibrations (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    Fibration (sameCoreRectification W hW hHat).p ∧
      Fibration (sameRectifiedNativeCoreBase W hW hHat) := by
  let : Fibration (sameCoreRectification W hW hHat).p :=
    (sameCoreRectification_fibrations W hW hHat).1
  let : Fibration (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat) :=
    SegalHomotopy.coreEndpoint_fibration _ hHat
  exact ⟨inferInstance, by unfold sameRectifiedNativeCoreBase; infer_instance⟩

/-- The TCof prefix retains the original SAME base equation. -/
theorem sameRectifiedNativeCoreBase_prefix (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    (sameCoreRectification W hW hHat).i ≫ sameRectifiedNativeCoreBase W hW hHat =
      sameCoreBase W hW := by
  rw [sameRectifiedNativeCoreBase, ← Category.assoc,
    (sameCoreRectification W hW hHat).fac, sameCoreComparison_native_over_base]

/-- The actual scalar prefix acts on native HP cospans over the Unit9 pair. -/
def sameCorePrefixUnitPairCospanMap (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    cospan (sameCoreBase W hW) (sameOriginalUnitPair W) ⟶
      cospan (sameRectifiedNativeCoreBase W hW hHat) (sameOriginalUnitPair W) :=
  cospanHomMk (𝟙 _) (sameCoreRectification W hW hHat).i (𝟙 _)
    (by
      change sameCoreBase W hW ≫ 𝟙 _ =
        (sameCoreRectification W hW hHat).i ≫ sameRectifiedNativeCoreBase W hW hHat
      exact (Category.comp_id _).trans (sameRectifiedNativeCoreBase_prefix W hW hHat).symm)
    (by
      change sameOriginalUnitPair W ≫ 𝟙 _ = 𝟙 _ ≫ sameOriginalUnitPair W
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The actual fibration factor acts on the same native HP image cospans. -/
def sameCoreFactorUnitPairCospanMap (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    cospan (sameRectifiedNativeCoreBase W hW hHat) (sameOriginalUnitPair W) ⟶
      cospan (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
        (sameOriginalUnitPair W) :=
  cospanHomMk (𝟙 _) (sameCoreRectification W hW hHat).p (𝟙 _)
    (by
      change sameRectifiedNativeCoreBase W hW hHat ≫ 𝟙 _ =
        (sameCoreRectification W hW hHat).p ≫
          SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat
      exact Category.comp_id _)
    (by
      change sameOriginalUnitPair W ≫ 𝟙 _ = 𝟙 _ ≫ sameOriginalUnitPair W
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The native cospan factorization preserves all three actual components. -/
theorem sameCoreUnitPairCospan_factorization (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    sameCorePrefixUnitPairCospanMap W hW hHat ≫ sameCoreFactorUnitPairCospanMap W hW hHat =
      sameCoreUnitPairComparisonCospanMap W hW hHat := by
  apply NatTrans.ext
  funext j
  cases j with
  | none => simp [sameCorePrefixUnitPairCospanMap, sameCoreFactorUnitPairCospanMap,
      sameCoreUnitPairComparisonCospanMap, cospanHomMk]
  | some pair =>
      cases pair with
      | left =>
          change (sameCoreRectification W hW hHat).i ≫ (sameCoreRectification W hW hHat).p =
            sameCoreComparison W hW hHat
          exact (sameCoreRectification W hW hHat).fac
      | right => simp [sameCorePrefixUnitPairCospanMap, sameCoreFactorUnitPairCospanMap,
          sameCoreUnitPairComparisonCospanMap, cospanHomMk]

/-- The prefix HP map is weak because its actual total component is TCof. -/
theorem sameCorePrefixUnitPairHomotopyMap_weak (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    WeakEquivalence ((homotopyPullback (C := SSet.{u})).map
      (sameCorePrefixUnitPairCospanMap W hW hHat)) := by
  have hi := (mem_trivialCofibrations_iff _).mp (sameCoreRectification W hW hHat).hi
  apply homotopyPullback_map_weakEquivalence
  intro j
  cases j with
  | none => exact inferInstanceAs (WeakEquivalence (𝟙 _))
  | some pair =>
      cases pair with
      | left => exact hi.2
      | right => exact inferInstanceAs (WeakEquivalence (𝟙 _))

/-- The factor HP map is weak by the actual native factorization and the
internally derived whole-core HP comparison; p-WE is not assumed. -/
theorem sameCoreFactorUnitPairHomotopyMap_weak (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    WeakEquivalence ((homotopyPullback (C := SSet.{u})).map
      (sameCoreFactorUnitPairCospanMap W hW hHat)) := by
  let : WeakEquivalence ((homotopyPullback (C := SSet.{u})).map
      (sameCorePrefixUnitPairCospanMap W hW hHat)) :=
          sameCorePrefixUnitPairHomotopyMap_weak W hW hHat
  let : WeakEquivalence ((homotopyPullback (C := SSet.{u})).map
      (sameCoreUnitPairComparisonCospanMap W hW hHat)) :=
          sameCoreUnitPairHomotopyComparison_weak W hW hHat
  let : WeakEquivalence ((homotopyPullback (C := SSet.{u})).map
      (sameCorePrefixUnitPairCospanMap W hW hHat) ≫ (homotopyPullback (C := SSet.{u})).map
        (sameCoreFactorUnitPairCospanMap W hW hHat)) := by
    rw [← Functor.map_comp, sameCoreUnitPairCospan_factorization]
    infer_instance
  exact weakEquivalence_of_precomp
    ((homotopyPullback (C := SSet.{u})).map (sameCorePrefixUnitPairCospanMap W hW hHat))
    ((homotopyPullback (C := SSet.{u})).map (sameCoreFactorUnitPairCospanMap W hW hHat))

/-- The ordinary comparison is the SAME original p pulled back over the
full Unit9 pair, with no changed source or target projection. -/
def sameCoreFactorUnitPairPullbackMap (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    pullback (sameRectifiedNativeCoreBase W hW hHat) (sameOriginalUnitPair W) ⟶
      pullback (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
        (sameOriginalUnitPair W) :=
  pullback.map _ _ _ _ (sameCoreRectification W hW hHat).p (𝟙 _) (𝟙 _)
    (by simp only [Category.comp_id, sameRectifiedNativeCoreBase])
    (by simp only [Category.comp_id, Category.id_comp])

/-- Both native ordinary-pullback projections identify the actual limit map. -/
theorem sameCoreFactorUnitPairPullbackMap_eq_limitMap (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    sameCoreFactorUnitPairPullbackMap W hW hHat =
        lim.map (sameCoreFactorUnitPairCospanMap W hW hHat) := by
  apply pullback.hom_ext
  · simp only [sameCoreFactorUnitPairPullbackMap, pullback.map, pullback.lift_fst]
    exact (limit.map_π (sameCoreFactorUnitPairCospanMap W hW hHat) WalkingCospan.left).symm
  · simp only [sameCoreFactorUnitPairPullbackMap, pullback.map, pullback.lift_snd,
      Category.comp_id]
    have h : lim.map (sameCoreFactorUnitPairCospanMap W hW hHat) ≫
        pullback.snd (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
          (sameOriginalUnitPair W) =
        pullback.snd (sameRectifiedNativeCoreBase W hW hHat) (sameOriginalUnitPair W) :=
      (limit.map_π (sameCoreFactorUnitPairCospanMap W hW hHat) WalkingCospan.right).trans
        (Category.comp_id _)
    exact h.symm

/-- Both rectified endpoint fibrations identify ordinary and native HP
comparisons, proving weakness of the actual full image-pair pullback map. -/
theorem sameCoreFactorUnitPairPullbackMap_weak (W : SimplicialSpace.{u})
    (hW : segalSpaces W) (hHat : segalSpaces (RezkCompletionData.completion.obj W)) :
    WeakEquivalence (sameCoreFactorUnitPairPullbackMap W hW hHat) := by
  let : Fibration (sameRectifiedNativeCoreBase W hW hHat) :=
    (sameRectifiedNativeCoreBase_fibrations W hW hHat).2
  let : Fibration (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat) :=
    SegalHomotopy.coreEndpoint_fibration _ hHat
  let : Fibration ((cospan (sameRectifiedNativeCoreBase W hW hHat)
      (sameOriginalUnitPair W)).map WalkingCospan.Hom.inl) := by
    change Fibration (sameRectifiedNativeCoreBase W hW hHat)
    infer_instance
  let : Fibration ((cospan
      (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
      (sameOriginalUnitPair W)).map WalkingCospan.Hom.inl) := by
    change Fibration (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
    infer_instance
  let sourceComparison := (homotopyPullbackComparison (C := SSet.{u})).app
    (cospan (sameRectifiedNativeCoreBase W hW hHat) (sameOriginalUnitPair W))
  let targetComparison := (homotopyPullbackComparison (C := SSet.{u})).app
    (cospan (SegalHomotopy.coreEndpoint (RezkCompletionData.completion.obj W) hHat)
      (sameOriginalUnitPair W))
  letI : WeakEquivalence sourceComparison :=
      weakEquivalence_homotopyPullbackComparison_of_rightProper_inl _
  letI : WeakEquivalence targetComparison :=
      weakEquivalence_homotopyPullbackComparison_of_rightProper_inl _
  let : WeakEquivalence ((homotopyPullback (C := SSet.{u})).map
      (sameCoreFactorUnitPairCospanMap W hW hHat)) :=
          sameCoreFactorUnitPairHomotopyMap_weak W hW hHat
  letI : WeakEquivalence (lim.map (sameCoreFactorUnitPairCospanMap W hW hHat) ≫
      targetComparison) := by
    rw [(homotopyPullbackComparison (C := SSet.{u})).naturality]
    infer_instance
  rw [sameCoreFactorUnitPairPullbackMap_eq_limitMap]
  exact weakEquivalence_of_postcomp (lim.map (sameCoreFactorUnitPairCospanMap W hW hHat))
    targetComparison

end SimplicialSpace.RezkCompletionCoreDiagonal
