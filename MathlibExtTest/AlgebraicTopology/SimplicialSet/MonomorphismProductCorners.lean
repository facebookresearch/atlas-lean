/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.MonomorphismProductCorners

/-!
# Public use of the complete product-corner comparison

The combined result cancels through the actual corner. Its source
comparison gives both directions of the degreewise image-union description,
including an actual preimage in the specified pushout domain.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace MonomorphismProductCornersTest

variable {A B K L : SSet.{u}} (i : A ⟶ B) (j : K ⟶ L) [Mono i] [Mono j]

/-- Native cancellation follows from the monicity part of the complete public result. -/
lemma cancel_corner {X : SSet.{u}} {f g : X ⟶ (Arrow.mk i □ Arrow.mk j).left}
    (h : f ≫ (Arrow.mk i □ Arrow.mk j).hom = g ≫ (Arrow.mk i □ Arrow.mk j).hom) :
    f = g := by
  have : Mono (Arrow.mk i □ Arrow.mk j).hom := (SSet.monomorphism_product_corner i j).1
  exact (cancel_mono (Arrow.mk i □ Arrow.mk j).hom).1 h

/-- Every point of the actual corner source maps into the indicated image union. -/
lemma image_in_union (n : SimplexCategoryᵒᵖ) (x : (Arrow.mk i □ Arrow.mk j).left.obj n) :
    ((Arrow.mk i □ Arrow.mk j).hom.app n x).2 ∈ Set.range (j.app n) ∨
      ((Arrow.mk i □ Arrow.mk j).hom.app n x).1 ∈ Set.range (i.app n) := by
  obtain ⟨_, e, he⟩ := SSet.monomorphism_product_corner i j
  have hz := (e.hom.app n x).property
  have hval : (e.hom.app n x).val = (Arrow.mk i □ Arrow.mk j).hom.app n x := by
    simpa only [SSet.comp_app, Subfunctor.ι_app, types_comp_apply, TypeCat.ofHom_apply] using!
      congrArg (fun f : (Arrow.mk i □ Arrow.mk j).left ⟶ B ⊗ L => f.app n x) he
  rw [hval] at hz
  simpa only [Subfunctor.range_obj] using
    (SSet.Subcomplex.mem_unionProd_iff (SSet.Subcomplex.range i)
      (SSet.Subcomplex.range j) ((Arrow.mk i □ Arrow.mk j).hom.app n x)).1 hz

/-- Every point of the union has an actual preimage in the specified pushout domain. -/
lemma exists_corner_preimage (n : SimplexCategoryᵒᵖ) (b : B.obj n) (l : L.obj n)
    (h : l ∈ Set.range (j.app n) ∨ b ∈ Set.range (i.app n)) :
    ∃ x : (Arrow.mk i □ Arrow.mk j).left.obj n,
      (Arrow.mk i □ Arrow.mk j).hom.app n x = (b, l) := by
  obtain ⟨_, e, he⟩ := SSet.monomorphism_product_corner i j
  have hz : (b, l) ∈
      ((SSet.Subcomplex.range i).unionProd (SSet.Subcomplex.range j)).obj n := by
    apply (SSet.Subcomplex.mem_unionProd_iff (SSet.Subcomplex.range i)
      (SSet.Subcomplex.range j) (b, l)).2
    simpa only [Subfunctor.range_obj] using h
  let z : ((SSet.Subcomplex.range i).unionProd (SSet.Subcomplex.range j) : SSet.{u}).obj n :=
    ⟨(b, l), hz⟩
  refine ⟨e.inv.app n z, ?_⟩
  have hval : (e.hom.app n (e.inv.app n z)).val =
      (Arrow.mk i □ Arrow.mk j).hom.app n (e.inv.app n z) := by
    simpa only [SSet.comp_app, Subfunctor.ι_app, types_comp_apply, TypeCat.ofHom_apply] using!
      congrArg (fun f : (Arrow.mk i □ Arrow.mk j).left ⟶ B ⊗ L =>
        f.app n (e.inv.app n z)) he
  rw [← hval]
  change (((e.inv ≫ e.hom).app n) z).val = (b, l)
  rw [e.inv_hom_id]
  rfl

end MonomorphismProductCornersTest
