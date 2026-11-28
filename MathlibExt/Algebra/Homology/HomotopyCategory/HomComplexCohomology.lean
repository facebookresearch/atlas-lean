/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import MathlibExt.Algebra.Homology.HomotopyCategory.HomComplexCocycle

/-!
# Base actions on Hom-complex cohomology

Let C be preadditive and n an integer. A degree-n Hom-complex cohomology class between integer
cochain complexes can be precomposed with a source complex map and postcomposed with a target
complex map. The actions are defined through the homotopy-category quotient, so they depend only
on the homotopy classes of the degree-zero maps.

These actions satisfy the identity and composition laws, and independent source and target
actions commute.
-/

@[expose] public section

open CategoryTheory
universe u v

namespace CochainComplex.HomComplex.CohomologyClass

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {F G H K L : CochainComplex C ℤ} {n : ℤ}

noncomputable def precomp (f : F ⟶ G) :
    CohomologyClass G K n →+ CohomologyClass F K n where
  toFun x := homAddEquiv.symm ((HomotopyCategory.quotient C _).map f ≫ homAddEquiv x)
  map_zero' := by simp
  map_add' x y := by simp

noncomputable def postcomp (f : G ⟶ K) :
    CohomologyClass F G n →+ CohomologyClass F K n where
  toFun x := homAddEquiv.symm
    (homAddEquiv x ≫ (HomotopyCategory.quotient C _).map
      ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).map f))
  map_zero' := by simp
  map_add' x y := by simp

@[simp] lemma precomp_mk (f : F ⟶ G) (z : Cocycle G K n) :
    precomp f (mk z) = mk (z.precomp f) := by
  apply homAddEquiv.injective
  simp only [precomp]
  simp [CohomologyClass.toHom_mk, Cocycle.equivHomShift_symm_precomp]

@[simp] lemma postcomp_mk (f : G ⟶ K) (z : Cocycle F G n) :
    postcomp f (mk z) = mk (z.postcomp f) := by
  apply homAddEquiv.injective
  simp only [postcomp]
  simp [CohomologyClass.toHom_mk, Cocycle.equivHomShift_symm_postcomp]

@[simp] lemma precomp_id :
    precomp (K := K) (n := n) (𝟙 F) = AddMonoidHom.id _ := by
  ext x
  obtain ⟨z, rfl⟩ := mk_surjective x
  simp [precomp_mk]

@[simp] lemma precomp_comp (f : F ⟶ G) (g : G ⟶ H) :
    precomp (K := K) (n := n) (f ≫ g) =
      (precomp (K := K) (n := n) f).comp
        (precomp (K := K) (n := n) g) := by
  ext x
  obtain ⟨z, rfl⟩ := mk_surjective x
  simp [precomp_mk]

@[simp] lemma postcomp_id :
    postcomp (F := F) (n := n) (𝟙 G) = AddMonoidHom.id _ := by
  ext x
  obtain ⟨z, rfl⟩ := mk_surjective x
  simp [postcomp_mk]

@[simp] lemma postcomp_comp (f : G ⟶ K) (g : K ⟶ L) :
    postcomp (F := F) (n := n) (f ≫ g) =
      (postcomp (F := F) (n := n) g).comp
        (postcomp (F := F) (n := n) f) := by
  ext x
  obtain ⟨z, rfl⟩ := mk_surjective x
  simp [postcomp_mk]

lemma precomp_postcomp (f : F ⟶ G) (g : K ⟶ L) :
    (precomp (K := L) (n := n) f).comp (postcomp (F := G) (n := n) g) =
      (postcomp (F := F) (n := n) g).comp
        (precomp (K := K) (n := n) f) := by
  ext x
  obtain ⟨z, rfl⟩ := mk_surjective x
  simp [precomp_mk, postcomp_mk, Cocycle.precomp_postcomp]

end CochainComplex.HomComplex.CohomologyClass
