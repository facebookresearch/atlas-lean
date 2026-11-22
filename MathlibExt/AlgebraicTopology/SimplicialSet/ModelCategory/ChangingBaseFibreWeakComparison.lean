/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.SharpFibreMapWeak
import MathlibExt.AlgebraicTopology.ModelCategory.SharpFibrations
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RightProper
import MathlibExt.CategoryTheory.Limits.Shapes.PullbackFibreTargetPoints

/-!
# Actual fibre weakness of an arbitrary weak changing-base comparison

Both original endpoint projections are fibrations. Actual right
properness makes the target-base pullback projection weak, so the
literal factor is weak from the original weak total and base maps.
The general sharp-fibre theorem proves all original changing-base
fibre maps weak, using sharpness of both endpoint fibrations.
Neither base nor the total comparison is assumed fibrant.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.ChangingBaseFibreWeakComparison
open CategoryTheory.Limits.PullbackFibreBaseChange
open HomotopicalAlgebra.SharpFibreMapWeak

/-- Actual weak total and base maps make the SAME relative pullback factor weak. -/
theorem factor_weak {E E' B B' : SSet.{u}}
    (e : E ⟶ E') (p : E ⟶ B) (p' : E' ⟶ B') (b : B ⟶ B')
    (h : p ≫ b = e ≫ p') [Fibration p']
    (he : realizationWeakEquivalences e) (hb : realizationWeakEquivalences b) :
    realizationWeakEquivalences (toBasePullback p p' e b h.symm) := by
  let _ : WeakEquivalence b := (weakEquivalence_iff _).mpr hb
  have hProjection : realizationWeakEquivalences (pullback.fst p' b) :=
    (weakEquivalence_iff _).mp
      (IsRightProper.weakEquivalence_of_isPullback (IsPullback.of_hasPullback p' b).flip)
  apply realizationWeakEquivalences.of_postcomp _ _ hProjection
  simpa only [factor_fst e p p' b h] using he

/-- Every SAME actual changing-base point fibre is weak for an arbitrary weak total comparison. -/
theorem fibreMap_weak {E E' B B' : SSet.{u}}
    (e : E ⟶ E') (p : E ⟶ B) (p' : E' ⟶ B') (b : B ⟶ B')
    (h : p ≫ b = e ≫ p') [Fibration p] [Fibration p']
    (he : realizationWeakEquivalences e) (hb : realizationWeakEquivalences b)
    (a : (Δ[0] : SSet.{u}) ⟶ B) :
    realizationWeakEquivalences (fibreMap p p' e b h.symm a) := by
  let _ : WeakEquivalence e := (weakEquivalence_iff _).mpr he
  let _ : WeakEquivalence b := (weakEquivalence_iff _).mpr hb
  change weakEquivalences SSet.{u} (SharpFibreMapWeak.fibreMap p p' e b h.symm a)
  exact SharpFibreMapWeak.fibreMap_weak p p' e b h.symm a
    (sharpMaps_of_fibration p) (sharpMaps_of_fibration p')
    (mem_weakEquivalences e) (mem_weakEquivalences b)

/-- Actual original point transport preserves weakness of the SAME entire fixed-target fibre map. -/
theorem fibreMapTo_weak {E E' B B' : SSet.{u}}
    (e : E ⟶ E') (p : E ⟶ B) (p' : E' ⟶ B') (b : B ⟶ B')
    (h : p ≫ b = e ≫ p') [Fibration p] [Fibration p']
    (he : realizationWeakEquivalences e) (hb : realizationWeakEquivalences b)
    (a : (Δ[0] : SSet.{u}) ⟶ B) (a' : (Δ[0] : SSet.{u}) ⟶ B') (ha : a ≫ b = a') :
    realizationWeakEquivalences (fibreMapTo e p p' b h a a' ha) :=
  (realizationWeakEquivalences.arrow_mk_iso_iff (fibreMapToArrowIso e p p' b h a a' ha)).mp
    (fibreMap_weak e p p' b h he hb a)

end SSet.ChangingBaseFibreWeakComparison
