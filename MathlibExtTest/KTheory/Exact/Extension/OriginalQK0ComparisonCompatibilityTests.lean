/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Extension.OriginalQK0ComparisonCompatibility

/-! Direct original-loop, actual Q/S calibration, all-component and fixed-RingK₀ clients. -/

public section

universe u v uRing vModule

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalActionCategory
open AlgebraicKTheory AlgebraicKTheory.OriginalQK0Comparison
open scoped CategoryTheory.Limits.CoreBiprodMonoidal MonoidalCategory Simplicial ZeroObject

#check @AlgebraicKTheory.OriginalQK0Comparison.generatorLoop
#print axioms AlgebraicKTheory.OriginalQK0Comparison.generatorLoop
#check @AlgebraicKTheory.OriginalQK0Comparison.canonicalLoopComponentsK0_trans
#print axioms AlgebraicKTheory.OriginalQK0Comparison.canonicalLoopComponentsK0_trans
#check @AlgebraicKTheory.OriginalQK0Comparison.generatorLoop_canonical
#print axioms AlgebraicKTheory.OriginalQK0Comparison.generatorLoop_canonical
#check @AlgebraicKTheory.OriginalQK0Comparison.comparison_all_pairs_path
#print axioms AlgebraicKTheory.OriginalQK0Comparison.comparison_all_pairs_path
#check @AlgebraicKTheory.OriginalQK0Comparison.comparison_all_pairs
#print axioms AlgebraicKTheory.OriginalQK0Comparison.comparison_all_pairs
#check @AlgebraicKTheory.OriginalQK0Comparison.comparison_components_canonical
#print axioms AlgebraicKTheory.OriginalQK0Comparison.comparison_components_canonical
#check @AlgebraicKTheory.OriginalQK0Comparison.projective_comparison_all_pairs
#print axioms AlgebraicKTheory.OriginalQK0Comparison.projective_comparison_all_pairs
#check @AlgebraicKTheory.OriginalQK0Comparison.comparison_zero
#print axioms AlgebraicKTheory.OriginalQK0Comparison.comparison_zero

section General

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

attribute [local instance] ExtensionCategory.leftSumAction
attribute [local instance] FixedTargetExtension.leftSumAction
attribute [local instance] MonoidalActionCategory.diagonalAction

example (A : C) :
    canonicalLoopComponentsK0 (ZerothHomotopy.mk (generatorLoop A)) = K0.mk A :=
  generatorLoop_canonical A

example (a : SInverse (Core C) (Core C)) :
    canonicalLoopComponentsK0 (ZerothHomotopy.mk (BasedSplitExactQLoop.comparisonMap (C := C)
      (SSet.realizedVertex
        (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v})) (ComposableArrows.mk₀ a)))) = K0.mk a.of.1.of - K0.mk a.of.2.of :=
  comparison_all_pairs a

example (a : SInverse (Core C) (Core C)) :
    (BasedSplitExactQLoop.comparisonMap (C := C) (SSet.realizedVertex
        (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v})) (ComposableArrows.mk₀ a))).Homotopic
      ((generatorLoop a.of.2.of).symm.trans (generatorLoop a.of.1.of)) :=
  comparison_all_pairs_path a

example (p q : BasedSplitExactQLoop.originalQLoops (C := C)) :
    canonicalLoopComponentsK0 (ZerothHomotopy.mk (p.trans q)) =
      canonicalLoopComponentsK0 (ZerothHomotopy.mk p) + canonicalLoopComponentsK0 (ZerothHomotopy.mk q) :=
  canonicalLoopComponentsK0_trans p q

example (p : BasedSplitExactQLoop.originalQLoops (C := C)) :
    canonicalLoopComponentsK0 (ZerothHomotopy.mk p.symm) =
      -canonicalLoopComponentsK0 (ZerothHomotopy.mk p) := canonicalLoopComponentsK0_symm p

example (c : ZerothHomotopy (BasedSplitExactQLoop.completedCoreSpace (C := C))) :
    canonicalLoopComponentsK0 (TopCat.zerothHomotopyMap (BasedSplitExactQLoop.comparisonMap (C := C)) c) =
      canonicalCoreComponentsK0 c := congrFun (comparison_components_canonical (C := C)) c

example (hSplit : ∀ S : ShortComplex C, IsAdmissibleExact S → Nonempty S.Splitting)
    (a : SInverse (Core C) (Core C)) :
    canonicalLoopComponentsK0 (ZerothHomotopy.mk ((BasedSplitExactQLoop.homotopyEquiv hSplit).toFun
      (SSet.realizedVertex
        (X := (nerve (SInverse (Core C) (Core C)) : SSet.{max u v})) (ComposableArrows.mk₀ a)))) = K0.mk a.of.1.of - K0.mk a.of.2.of := by
  rw [BasedSplitExactQLoop.homotopyEquiv_toFun]
  exact comparison_all_pairs a

example (t : unitInterval) :
    BasedSplitExactQLoop.comparisonMap (C := C) (BasedSplitExactQLoop.completedCorePoint (C := C)) t =
      OriginalQZeroComparison.zeroQVertex (C := C) := by
  rw [comparison_zero]
  rfl

end General

section Projective

attribute [local instance] MonoidalActionCategory.diagonalAction

variable (R : Type uRing) [Ring R]

example (P D : FGProjectiveCat.{max uRing vModule} R) :
    RingK0.projectiveUniverseEquiv.{uRing, vModule} R
      (canonicalLoopComponentsK0 (C := FGProjectiveCat.{max uRing vModule} R)
        (ZerothHomotopy.mk (BasedSplitExactQLoop.comparisonMap
          (C := FGProjectiveCat.{max uRing vModule} R)
            (SSet.realizedVertex
              (X := (nerve (SInverse (Core (FGProjectiveCat.{max uRing vModule} R))
                (Core (FGProjectiveCat.{max uRing vModule} R))) : SSet.{max (uRing + 1) (vModule + 1)}))
              (ComposableArrows.mk₀
              (⟨((⟨P⟩ : Core (FGProjectiveCat.{max uRing vModule} R)),
                  (⟨D⟩ : Core (FGProjectiveCat.{max uRing vModule} R)))⟩ :
                SInverse (Core (FGProjectiveCat.{max uRing vModule} R))
                  (Core (FGProjectiveCat.{max uRing vModule} R)))))))) =
      K0.mk (FGProjectiveCat.UniverseEquivalence.shrinkObject.{uRing, vModule} R P) -
        K0.mk (FGProjectiveCat.UniverseEquivalence.shrinkObject.{uRing, vModule} R D) :=
  projective_comparison_all_pairs.{uRing, vModule} R P D

example (a : SInverse (Core (FGProjectiveCat.{max uRing vModule} R))
    (Core (FGProjectiveCat.{max uRing vModule} R))) :
    RingK0.projectiveUniverseEquiv.{uRing, vModule} R
      (canonicalLoopComponentsK0 (C := FGProjectiveCat.{max uRing vModule} R)
        (ZerothHomotopy.mk (BasedSplitExactQLoop.comparisonMap
          (C := FGProjectiveCat.{max uRing vModule} R)
            (SSet.realizedVertex
              (X := (nerve (SInverse (Core (FGProjectiveCat.{max uRing vModule} R))
                (Core (FGProjectiveCat.{max uRing vModule} R))) : SSet.{max (uRing + 1) (vModule + 1)}))
              (ComposableArrows.mk₀ a))))) =
      RingK0.sInverseSComponentsUniverseEquiv.{uRing, vModule} R
        (CategoryTheory.ConnectedComponents.mk (CoreLocalizationComparison.toPairObj a)) :=
  projective_comparison_component_dictionary.{uRing, vModule} R a

example : RingK0.projectiveUniverseEquiv.{uRing, vModule} R
    (canonicalLoopComponentsK0 (C := FGProjectiveCat.{max uRing vModule} R)
      (ZerothHomotopy.mk (generatorLoop
        (FGProjectiveCat.UniverseEquivalence.liftObject.{uRing, vModule} R (FGProjectiveCat.of (R := R) R))))) =
      K0.mk (FGProjectiveCat.of (R := R) R) := by
  let CPG := FGProjectiveCat.{max uRing vModule} R
  let M : CPG := FGProjectiveCat.UniverseEquivalence.liftObject.{uRing, vModule} R
    (FGProjectiveCat.of (R := R) R)
  have hGenerator : canonicalLoopComponentsK0 (C := CPG)
      (ZerothHomotopy.mk (generatorLoop M)) = K0.mk M :=
    generatorLoop_canonical (C := CPG) M
  have hMapped := congrArg (RingK0.projectiveUniverseEquiv.{uRing, vModule} R) hGenerator
  have hRegular : RingK0.projectiveUniverseEquiv.{uRing, vModule} R (K0.mk M) =
      K0.mk (FGProjectiveCat.of (R := R) R) :=
    RingK0.projectiveUniverseEquiv_regular.{uRing, vModule} R
  exact hMapped.trans hRegular

example : canonicalLoopComponentsK0 (C := FGProjectiveCat.{max uRing vModule} R)
    (ZerothHomotopy.mk (Path.refl (OriginalQZeroComparison.zeroQVertex
      (C := FGProjectiveCat.{max uRing vModule} R)))) = 0 := canonicalLoopComponentsK0_refl

end Projective

end
