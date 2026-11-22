/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerLeibnizHom
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyWeakEquivalences

/-!
# Rezk weak equivalences and inner scalar pushout-products

For every supplied inner pushout-product of two original monomorphisms,
its original comparison map is monic. It is Rezk weak when the space input
is Rezk weak or the scalar input is Kan–Quillen weak. The first case tests
every complete Segal target using raw Reedy mapping fibrancy and the whole
Leibniz–Hom Arrow isomorphism; the second uses the original Reedy inclusion.
This is the scalar compatibility in Rezk, *A model for the homotopy theory
of homotopy theory*, Theorem 7.2 and Section 9.1.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.MorphismProperty

namespace SimplicialSpace

/-- The original supplied inner pushout-product of monomorphisms is monic. -/
theorem inner_pushoutObjObj_mono {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L) [Mono i] [Mono j]
    (pp : innerTensorBifunctor.PushoutObjObj i j) : Mono pp.ι := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  have hi : cofibrations SimplicialSpace.{u} i :=
    (HomotopicalAlgebra.cofibration_iff i).1
      ((ReedyModel.cofibration_iff i).2 inferInstance)
  have hj : cofibrations SSet.{u} j :=
    (HomotopicalAlgebra.cofibration_iff j).1
      (SSet.modelCategoryQuillen.cofibration_of_mono j)
  have hpp := ReedyModel.inner_pushoutObjObj_cofibration i j pp hi hj
  exact (ReedyModel.cofibration_iff pp.ι).1
    ((HomotopicalAlgebra.cofibration_iff pp.ι).2 hpp)

/-- Rezk weakness of the space input gives Rezk weakness of the same supplied corner. -/
theorem inner_pushoutObjObj_rezkWeak_of_left
    {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L) [Mono i] [Mono j]
    (pp : innerTensorBifunctor.PushoutObjObj i j) (hiW : rezkWeakEquivalences i) :
    rezkWeakEquivalences pp.ι := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  have hi : cofibrations SimplicialSpace.{u} i :=
    (HomotopicalAlgebra.cofibration_iff i).1
      ((ReedyModel.cofibration_iff i).2 inferInstance)
  let _ : Cofibration j := SSet.modelCategoryQuillen.cofibration_of_mono j
  intro Z hZ
  let g := (innerHomFunctor.map i.op).app Z
  have hgF : fibrations SSet.{u} g :=
    ReedyModel.inner_precomp_fibration i Z hi hZ.1
  have hgW : SSet.realizationWeakEquivalences g := hiW Z hZ
  let _ : Fibration g := (HomotopicalAlgebra.fibration_iff g).2 hgF
  let _ : WeakEquivalence g := (HomotopicalAlgebra.weakEquivalence_iff g).2 hgW
  have hpower : trivialFibrations SSet.{u} (SSet.ihomToPullback j g) :=
    SSet.ihomToPullback_mem_trivialFibrations_of_right j g
  exact (SSet.realizationWeakEquivalences.arrow_mk_iso_iff
    (innerLeibnizHomIso i j pp Z)).2 hpower.2

/-- Kan–Quillen weakness of the scalar input gives Rezk weakness of the same corner. -/
theorem inner_pushoutObjObj_rezkWeak_of_right
    {A B : SimplicialSpace.{u}} {K L : SSet.{u}}
    (i : A ⟶ B) (j : K ⟶ L) [Mono i] [Mono j]
    (pp : innerTensorBifunctor.PushoutObjObj i j) (hjW : SSet.realizationWeakEquivalences j) :
    rezkWeakEquivalences pp.ι := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  have hi : cofibrations SimplicialSpace.{u} i :=
    (HomotopicalAlgebra.cofibration_iff i).1
      ((ReedyModel.cofibration_iff i).2 inferInstance)
  have hj : trivialCofibrations SSet.{u} j :=
    ⟨(HomotopicalAlgebra.cofibration_iff j).1
      (SSet.modelCategoryQuillen.cofibration_of_mono j), hjW⟩
  have hpp := ReedyModel.inner_pushoutObjObj_trivialCofibration_of_right i j pp hi hj
  exact reedyWeak_le_rezkWeak pp.ι hpp.2

end SimplicialSpace
