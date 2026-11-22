/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalizingMonomorphisms
import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalGenerators
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyGenerators
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerLeibnizHom
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyWeakEquivalences

/-!
# Monicity and Rezk weakness of the literal auxiliary generators

For the full horn/localizing-boundary index, the horn summand uses the named
Reedy lifting class. The added summand uses every same-universe complete Segal
test target and the whole Leibniz–Hom Arrow comparison for the original chosen
pushout, including scalar boundary zero. This proves the joint containment for
the localizing family motivated by Rezk, *A model for the homotopy theory of
homotopy theory*, §§9 and 12; it supplies no localization model as a premise.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open CategoryTheory.MorphismProperty
open scoped SimplicialSpace.Inner Simplicial
namespace SimplicialSpace.LocalGenerators

private theorem horn_properties (h : ReedyGeneratingFamilies.HornIndex) :
    Mono (ReedyGeneratingFamilies.hornFamily.{u} h).hom ∧
      rezkWeakEquivalences (ReedyGeneratingFamilies.hornFamily.{u} h).hom := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  have hmem : ReedyGeneratingFamilies.J.{u}
      (ReedyGeneratingFamilies.hornFamily.{u} h).hom :=
    MorphismProperty.ofHoms.mk
      (f := fun h : ReedyGeneratingFamilies.HornIndex =>
        (ReedyGeneratingFamilies.hornFamily.{u} h).hom) h
  have hleft : ReedyGeneratingFamilies.J.{u}.rlp.llp
      (ReedyGeneratingFamilies.hornFamily.{u} h).hom :=
    ReedyGeneratingFamilies.J.{u}.le_llp_rlp _ hmem
  have hTC : trivialCofibrations SimplicialSpace.{u}
      (ReedyGeneratingFamilies.hornFamily.{u} h).hom := by
    rw [ReedyGeneratingFamilies.J_rlp_eq_fibrations.{u}] at hleft
    rw [fibrations_llp SimplicialSpace.{u}] at hleft
    exact hleft
  refine ⟨(ReedyModel.cofibration_iff _).1
    ((HomotopicalAlgebra.cofibration_iff _).2 hTC.1), ?_⟩
  exact reedyWeak_le_rezkWeak _ hTC.2

private theorem boundary_properties (i : SSet.Rezk.LocalizingIndex) (n : ℕ) :
    Mono (boundaryPushout.{u} i n).ι ∧
      rezkWeakEquivalences (boundaryPushout.{u} i n).ι := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  let s := (localizingArrow.{u} i).hom
  let j := (SSet.boundary.{u} n).ι
  let pp := boundaryPushout.{u} i n
  have hsMono : Mono s := by
    change Mono (ofSimplicialObject.mapArrow.obj (SSet.Rezk.localizingMap.{u} i)).hom
    exact SimplicialSpace.localizingMap_mono i
  have hsCof : cofibrations SimplicialSpace.{u} s :=
    (HomotopicalAlgebra.cofibration_iff s).1 ((ReedyModel.cofibration_iff s).2 hsMono)
  let _ : Mono j := inferInstance
  have hjCof : cofibrations SSet.{u} j :=
    (HomotopicalAlgebra.cofibration_iff j).1
      (SSet.modelCategoryQuillen.cofibration_of_mono j)
  have hppCof : cofibrations SimplicialSpace.{u} pp.ι :=
    ReedyModel.inner_pushoutObjObj_cofibration s j pp hsCof hjCof
  change Mono pp.ι ∧ rezkWeakEquivalences pp.ι
  refine ⟨(ReedyModel.cofibration_iff pp.ι).1
    ((HomotopicalAlgebra.cofibration_iff pp.ι).2 hppCof), ?_⟩
  intro Z hZ
  let g := (innerHomFunctor.{u}.map s.op).app Z
  have hgF : fibrations SSet.{u} g :=
    ReedyModel.inner_precomp_fibration s Z hsCof hZ.1
  have hgW : SSet.realizationWeakEquivalences g := by
    change SSet.realizationWeakEquivalences
      ((innerHomFunctor.{u}.map
        (ofSimplicialObject.map (SSet.Rezk.localizingMap.{u} i).hom).op).app Z)
    exact hZ.2 i
  have hgTF : trivialFibrations SSet.{u} g := ⟨hgF, hgW⟩
  let _ : Cofibration j := (HomotopicalAlgebra.cofibration_iff j).2 hjCof
  let _ : Fibration g := (HomotopicalAlgebra.fibration_iff g).2 hgTF.1
  let _ : WeakEquivalence g := (HomotopicalAlgebra.weakEquivalence_iff g).2 hgTF.2
  have hpowerTF : trivialFibrations SSet.{u} (SSet.ihomToPullback j g) :=
    SSet.ihomToPullback_mem_trivialFibrations_of_right j g
  let e := innerLeibnizHomIso s j pp Z
  exact (SSet.realizationWeakEquivalences.arrow_mk_iso_iff e).2 hpowerTF.2

/-- Every literal auxiliary generator is monic and genuinely ALL-CSS Rezk weak. -/
theorem le_monomorphisms_inf_rezkWeakEquivalences :
    J.{u} ≤ monomorphisms SimplicialSpace.{u} ⊓ rezkWeakEquivalences.{u} := by
  change MorphismProperty.ofHoms (fun i : Index => (family.{u} i).hom) ≤ _
  refine (MorphismProperty.ofHoms_le_iff
    (fun i : Index => (family.{u} i).hom)
    (monomorphisms SimplicialSpace.{u} ⊓ rezkWeakEquivalences.{u})).2 ?_
  intro index
  cases index with
  | inl h =>
      simpa only [family, MorphismProperty.inf_iff, monomorphisms.iff] using horn_properties h
  | inr b =>
      rcases b with ⟨i, n⟩
      simpa only [family, boundaryFamily, Arrow.mk_hom, MorphismProperty.inf_iff,
          monomorphisms.iff] using
        boundary_properties i n

end SimplicialSpace.LocalGenerators
