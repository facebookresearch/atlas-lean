/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.BoxProduct
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyGenerators
import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalSpaces
import MathlibExt.AlgebraicTopology.SimplicialSet.NerveContractiblePoint
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.GenuineTrivialFibrations

/-!
# Categorical constancy of the original rows

A vertically Reedy-fibrant simplicial space is categorically constant in
its original rows. This is Joyal–Tierney Proposition 2.8, pp.11–12,
used in the forward directions of Propositions 3.9 and 4.4. The complete
Segal corollary uses the actual vertical Reedy fibrancy in its definition.
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open CategoryTheory.MorphismProperty
open scoped Simplicial SimplicialSpace.Inner SSet.modelCategoryQuillen

universe u

namespace SimplicialSpace

private lemma rowPullbackHom_mem_I_rlp_of_reedyFibration
    {X Y : SimplicialSpace.{u}} (p : X ⟶ Y)
    (hp : SimplicialSpace.ReedyModel.modelCategory.categoryWithFibrations.fibrations p)
    {K L : SSet.{u}} (v : K ⟶ L) (hv : SSet.anodyneExtensions v) :
    SSet.modelCategoryQuillen.I.rlp (SimplicialSpace.rowPullbackHom v p) := by
  let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
  let _ : Fibration p := ⟨hp⟩
  intro A B i hi
  change MorphismProperty.ofHoms (fun m : ℕ => (SSet.boundary.{u} m).ι) i at hi
  cases hi with
  | mk m =>
    have hleft : SSet.modelCategoryQuillen.J.rlp
        (SimplicialSpace.boxLeftPullbackHom (SSet.boundary.{u} m).ι p) := by
      change SSet.modelCategoryQuillen.J.rlp
        (Functor.PullbackObjObj.ofHasPullback SimplicialSpace.innerHomFunctor
          (SimplicialSpace.ReedyGeneratingFamilies.outerBoundaryMap m) p).π
      exact ((SSet.modelCategoryQuillen.J.rlp).arrow_mk_iso_iff
        ((SimplicialSpace.relativeBoundaryMatchingArrowIso m).app (Arrow.mk p))).mpr
          ((SimplicialSpace.ReedyModel.fibration_iff p).mp inferInstance m)
    rw [SSet.anodyneExtensions_eq_llp_rlp] at hv
    exact (SimplicialSpace.box_hasLiftingProperty_iff (SSet.boundary.{u} m).ι v p).mpr
      (hv _ hleft)

private abbrev simplexVertex (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ Δ[n] :=
  SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)

private lemma simplexVertex_comp_toZero (n : ℕ) :
    simplexVertex.{u} n ≫ SSet.stdSimplex.map (SimplicialSpace.rowToZero n) =
      𝟙 (Δ[0] : SSet.{u}) :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

private lemma simplex_toZero_realizationWeak (n : ℕ) :
    SSet.realizationWeakEquivalences
      (SSet.stdSimplex.map (SimplicialSpace.rowToZero n) : (Δ[n] : SSet.{u}) ⟶ Δ[0]) := by
  have hN := NerveContractible.nerve_to_point_mem_realizationWeakEquivalences_of_hasTerminal
    (C := ULift.{u} (Fin (n + 1)))
  have h := MorphismProperty.RespectsIso.precomp SSet.realizationWeakEquivalences
    (SSet.stdSimplex.isoNerve n).hom _ hN
  rwa [show (SSet.stdSimplex.isoNerve n).hom ≫
      SSet.stdSimplex.isTerminalObj₀.from (nerve (ULift.{u} (Fin (n + 1)))) =
      SSet.stdSimplex.map (SimplicialSpace.rowToZero n) from
        SSet.stdSimplex.isTerminalObj₀.hom_ext _ _] at h

private lemma simplexVertex_anodyne (n : ℕ) :
    SSet.anodyneExtensions (simplexVertex.{u} n) := by
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  let _ : Mono (simplexVertex.{u} n) := SSet.stdSimplex.isTerminalObj₀.mono_from _
  let _ : Cofibration (simplexVertex.{u} n) :=
    (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
  have hv : SSet.realizationWeakEquivalences (simplexVertex.{u} n) := by
    apply SSet.realizationWeakEquivalences.of_postcomp _ _ (simplex_toZero_realizationWeak n)
    rw [simplexVertex_comp_toZero]
    exact SSet.realizationWeakEquivalences.id_mem _
  let _ : WeakEquivalence (simplexVertex.{u} n) := ⟨hv⟩
  rw [SSet.anodyneExtensions_eq_llp_rlp]
  intro A B p hp
  let _ : Fibration p := (SSet.modelCategoryQuillen.fibration_iff p).mpr hp
  infer_instance

private lemma rowRestriction_comp {A B C : SSet.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (X : SimplicialSpace.{u}) :
    SimplicialSpace.rowRestriction g X ≫ SimplicialSpace.rowRestriction f X =
      SimplicialSpace.rowRestriction (f ≫ g) X := by
  dsimp only [SimplicialSpace.rowRestriction, SimplicialSpace.discreteInnerMap]
  rw [← NatTrans.comp_app, ← SimplicialSpace.innerHomFunctor.map_comp, ← op_comp,
    ← SimplicialSpace.ofSimplicialObject.map_comp, ← SSet.simplicialSpaceDiscrete.map_comp]

private lemma rowRestriction_id (A : SSet.{u}) (X : SimplicialSpace.{u}) :
    SimplicialSpace.rowRestriction (𝟙 A) X =
      𝟙 ((SimplicialSpace.rowPowerFunctor A).obj X) := by
  simp only [SimplicialSpace.rowRestriction, SimplicialSpace.discreteInnerMap,
    SimplicialSpace.rowPowerFunctor, Functor.comp_obj,
    SSet.simplicialSpaceDiscrete.map_id, SimplicialSpace.ofSimplicialObject.map_id,
    op_id, SimplicialSpace.innerHomFunctor.map_id, NatTrans.id_app]

/-- Every original zero-to-n row map is categorical weak, including n=0. -/
private theorem rowZeroTo_categorical_of_reedyFibrant (X : SimplicialSpace.{u})
    (hX : let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
      IsFibrant X) (n : ℕ) :
    SSet.categoricalEquivalences ((SimplicialSpace.rowZeroTo n).app X) := by
  let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
  have hp : SimplicialSpace.ReedyModel.modelCategory.categoryWithFibrations.fibrations
      (terminal.from X) :=
    (HomotopicalAlgebra.fibration_iff _).mp
      ((HomotopicalAlgebra.isFibrant_iff X).mp hX)
  have hPull := rowPullbackHom_mem_I_rlp_of_reedyFibration (terminal.from X) hp
    (simplexVertex n) (simplexVertex_anodyne n)
  have hi : SSet.categoricalEquivalences
      (SimplicialSpace.rowRestriction (simplexVertex n) X) := by
    have hI : SSet.modelCategoryQuillen.I.rlp
        (SimplicialSpace.rowRestriction (simplexVertex n) X) :=
      ((SSet.modelCategoryQuillen.I.rlp).arrow_mk_iso_iff
        (SimplicialSpace.rowPullbackHomTerminalArrowIso (simplexVertex n) X)).mp hPull
    exact ((SSet.categoricalFibrations_and_categoricalEquivalences_iff _).mpr hI).2
  have hSection :
      SimplicialSpace.rowRestriction (SSet.stdSimplex.map (SimplicialSpace.rowToZero n)) X ≫
        SimplicialSpace.rowRestriction (simplexVertex n) X =
      𝟙 ((SimplicialSpace.rowPowerFunctor (Δ[0] : SSet.{u})).obj X) := by
    rw [rowRestriction_comp, simplexVertex_comp_toZero, rowRestriction_id]
  have ht : SSet.categoricalEquivalences
      (SimplicialSpace.rowRestriction
        (SSet.stdSimplex.map (SimplicialSpace.rowToZero n)) X) := by
    apply SSet.categoricalEquivalences.of_postcomp _ _ hi
    rw [hSection]
    exact SSet.categoricalEquivalences.id_mem _
  let e : Arrow.mk (SimplicialSpace.rowRestriction
      (SSet.stdSimplex.map (SimplicialSpace.rowToZero n)) X) ≅
      Arrow.mk ((SimplicialSpace.rowZeroTo n).app X) :=
    Arrow.isoMk (SimplicialSpace.rowRepresentableIso 0 X)
      (SimplicialSpace.rowRepresentableIso n X)
      (SimplicialSpace.rowRestriction_const_toZero n X).symm
  exact (SSet.categoricalEquivalences.arrow_mk_iso_iff e).mp ht

/-- JT2.8 on the native designated vertical Reedy model. -/
theorem categoricallyConstant_of_reedyFibrant (X : SimplicialSpace.{u})
    (hX : let _ : ModelCategory SimplicialSpace.{u} := SimplicialSpace.ReedyModel.modelCategory
      IsFibrant X) : SimplicialSpace.categoricallyConstant X :=
  rowZeroTo_categorical_of_reedyFibrant X hX

/-- The forward categorical-constancy clause cited by JT4.4. -/
theorem categoricallyConstant_of_completeSegalSpaces (X : SimplicialSpace.{u})
    (hX : SimplicialSpace.completeSegalSpaces X) :
    SimplicialSpace.categoricallyConstant X :=
  categoricallyConstant_of_reedyFibrant X hX.1

end SimplicialSpace
