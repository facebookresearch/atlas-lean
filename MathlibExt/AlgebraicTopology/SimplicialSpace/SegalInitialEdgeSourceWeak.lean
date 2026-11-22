/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalInitialEdgeSourceFibration
import MathlibExt.AlgebraicTopology.SimplicialSet.SharpComparison

/-!
# Genuine weak leading-edge comparison at the same fixed original source

Both original source maps are sharp because they are actual Reedy
restriction fibrations. The genuine weak leading-edge/tail comparison
therefore remains weak on the original fixed-source pullback. The
map is the original pullback map, with its entire source point retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.InitialEdgeTailMapping

private theorem congr_fst {X Y Z : SSet.{u}} {a c : X ⟶ Z} (h : a = c) (b : Y ⟶ Z) :
    (pullback.congrHom h (show b = b from rfl)).hom ≫ pullback.fst c b = pullback.fst a b := by
  subst c
  simp [pullback.congrHom_hom, pullback.map]

private theorem congr_snd {X Y Z : SSet.{u}} {a c : X ⟶ Z} (h : a = c) (b : Y ⟶ Z) :
    (pullback.congrHom h (show b = b from rfl)).hom ≫ pullback.snd c b = pullback.snd a b := by
  subst c
  simp [pullback.congrHom_hom, pullback.map]

set_option backward.isDefEq.respectTransparency false in
/-- The original first-vertex augmentation is a Kan fibration under actual Reedy fibrancy. -/
theorem rowAugmentation_fibration (W : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → ∀ n : ℕ, Fibration
      ((SimplicialObject.LeftDecalage.augmentation W.diagram).app (op (SimplexCategory.mk n))) := by
  intro hW n
  let f := SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk (n + 1)) 0
  let i := SSet.stdSimplex.{u}.map f
  let _ : Mono i := by
    rw [NatTrans.mono_iff_mono_app]
    intro d
    rw [CategoryTheory.mono_iff_injective]
    intro x y _
    apply SSet.stdSimplex.objEquiv.injective
    exact SimplexCategory.isTerminalZero.hom_ext _ _
  let _ : Fibration ((discreteSourceMapping W).map i.op) :=
    VertexRestriction.discreteRestriction_fibration i W hW
  let _ : Fibration (discreteYonedaIso W (n + 1)).inv := inferInstance
  let _ : Fibration (discreteYonedaIso W 0).hom := inferInstance
  have he : (discreteYonedaIso W (n + 1)).inv ≫
      (discreteSourceMapping W).map i.op ≫ (discreteYonedaIso W 0).hom =
      (SimplicialObject.LeftDecalage.augmentation W.diagram).app (op (SimplexCategory.mk n)) := by
    rw [discreteYonedaIso_naturality_index, Iso.inv_hom_id_assoc]
    rfl
  rw [← he]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The actual leading-edge row comparison is weak after fixing the same original source vertex. -/
theorem sourceFibreComparison_weak (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (x : (W.diagram _⦋0⦌) _⦋0⦌) (n : ℕ) :
    SSet.realizationWeakEquivalences (sourceFibreComparison W x n) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let f := rowComparison W n
  let p := rowSource W n
  let b := SSet.yonedaEquiv.symm x
  let _ : WeakEquivalence f := (HomotopicalAlgebra.weakEquivalence_iff _).mpr (rowComparison_weak W hW n)
  have hp := rowSource_sharp W hW.1 n
  have hfp : SSet.SharpComparisonDraft.Sharp (f ≫ p) := by
    dsimp only [f, p]
    rw [rowComparison_source]
    let _ := rowAugmentation_fibration W hW.1 n
    exact SSet.SharpComparisonDraft.sharp_of_fibration _
  have hw := SSet.SharpComparisonDraft.ordinaryMap_weak f p b (inferInstanceAs (WeakEquivalence f)) hp hfp
  let e := pullback.congrHom (rowComparison_source W n) (show b = b from rfl)
  have he : e.hom ≫ sourceFibreComparison W x n = SSet.SharpComparisonDraft.ordinaryMap f p b := by
    apply pullback.hom_ext
    · have hp : sourceFibreComparison W x n ≫ pullback.fst (rowSource W n) b =
          pullback.fst ((SimplicialObject.LeftDecalage.augmentation W.diagram).app
            (op (SimplexCategory.mk n))) b ≫ f := by
        exact pullback.lift_fst _ _ _
      have hq : SSet.SharpComparisonDraft.ordinaryMap f p b ≫ pullback.fst p b =
          pullback.fst (f ≫ p) b ≫ f := by exact pullback.lift_fst _ _ _
      rw [Category.assoc, hp, hq, ← Category.assoc]
      exact congrArg (fun q => q ≫ f) (congr_fst (rowComparison_source W n) b)
    · have hp : sourceFibreComparison W x n ≫ pullback.snd (rowSource W n) b =
          pullback.snd ((SimplicialObject.LeftDecalage.augmentation W.diagram).app
            (op (SimplexCategory.mk n))) b := by
        unfold sourceFibreComparison
        rw [pullback.map, pullback.lift_snd]
        exact Category.comp_id _
      have hq : SSet.SharpComparisonDraft.ordinaryMap f p b ≫ pullback.snd p b =
          pullback.snd (f ≫ p) b := by exact pullback.lift_snd _ _ _
      rw [Category.assoc, hp, hq]
      exact congr_snd (rowComparison_source W n) b
  have h := (HomotopicalAlgebra.weakEquivalence_iff _).mp hw
  rw [← he] at h
  exact (SSet.realizationWeakEquivalences.precomp_iff _ _ (SSet.realizationWeakEquivalences.of_isIso e.hom)).mp h

end SimplicialSpace.InitialEdgeTailMapping
