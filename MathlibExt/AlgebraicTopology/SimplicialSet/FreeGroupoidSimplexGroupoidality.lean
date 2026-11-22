/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.FreeGroupoidSimplex
public import MathlibExt.AlgebraicTopology.Quasicategory.Core
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Groupoidality of the actual homotopy category of the k-image
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.FreeGroupoidSimplex

private theorem cell_surjective (X : SSet.{u}) (m : SimplexCategory)
    (z : (kFunctor.obj X).obj (op m)) :
    ∃ (n : SimplexCategory) (a : stdSimplex.obj n ⟶ X) (t : (J.obj n).obj (op m)),
      (kRepresentableIso.inv.app n ≫ kFunctor.map a).app (op m) t = z := by
  let _ : PreservesColimitsOfSize.{u, u} kFunctor.{u} :=
    kAdjunction.leftAdjoint_preservesColimits
  let _ : PreservesColimitsOfShape
      (CostructuredArrow (uliftYoneda.{u} (C := SimplexCategory)) X) kFunctor.{u} :=
    kAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
  let cX := Presheaf.tautologicalCocone'.{u} X
  let cK := kFunctor.mapCocone cX
  have hK : IsColimit cK :=
    isColimitOfPreserves kFunctor (Presheaf.isColimitTautologicalCocone'.{u} X)
  let ev := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op m)
  have hm : IsColimit (ev.mapCocone cK) := isColimitOfPreserves ev hK
  obtain ⟨j, tRaw, ht⟩ := Types.jointly_surjective_of_isColimit hm z
  refine ⟨j.left, j.hom, (kRepresentableIso.hom.app j.left).app (op m) tRaw, ?_⟩
  have hi : (kRepresentableIso.inv.app j.left).app (op m)
      ((kRepresentableIso.hom.app j.left).app (op m) tRaw) = tRaw :=
    ConcreteCategory.congr_hom
      (NatTrans.congr_app ((kRepresentableIso.app j.left).hom_inv_id) (op m)) tRaw
  change (kFunctor.map j.hom).app (op m)
    ((kRepresentableIso.inv.app j.left).app (op m)
      ((kRepresentableIso.hom.app j.left).app (op m) tRaw)) = z
  rw [hi]
  exact ht

private theorem fullJ_mem_core (n m : SimplexCategory) (t : (J.obj n).obj (op m)) :
    t ∈ (core (J.obj n)).obj (op m) := by
  change t ∈ (core (nerve (Grpd.free.obj (ordinal.obj n)))).obj (op m)
  apply (mem_core_nerve_iff_forall_map'_isIso t).mpr
  intro i j hij hjn
  infer_instance

private theorem kImage_mem_core (X : SSet.{u}) (m : SimplexCategory)
    (z : (kFunctor.obj X).obj (op m)) : z ∈ (core (kFunctor.obj X)).obj (op m) := by
  obtain ⟨n, a, t, ht⟩ := cell_surjective X m z
  have h := (core_le_preimage (kRepresentableIso.inv.app n ≫ kFunctor.map a))
    (op m) (fullJ_mem_core n m t)
  change (kRepresentableIso.inv.app n ≫ kFunctor.map a).app (op m) t ∈
    (core (kFunctor.obj X)).obj (op m) at h
  exact ht ▸ h

private theorem cell_operator {X : SSet.{u}} {n n' : SimplexCategory}
    (h : n ⟶ n') (a : stdSimplex.obj n' ⟶ X) :
    J.map h ≫ (kRepresentableIso.inv.app n' ≫ kFunctor.map a) =
      kRepresentableIso.inv.app n ≫ kFunctor.map (stdSimplex.map h ≫ a) := by
  rw [← Category.assoc, kRepresentableIso.inv.naturality h,
    Functor.comp_map, Category.assoc, ← Functor.map_comp]

private theorem cell_target {X Y : SSet.{u}} (f : X ⟶ Y)
    (n : SimplexCategory) (a : stdSimplex.obj n ⟶ X) :
    (kRepresentableIso.inv.app n ≫ kFunctor.map a) ≫ kFunctor.map f =
      kRepresentableIso.inv.app n ≫ kFunctor.map (a ≫ f) := by
  rw [Category.assoc, Functor.map_comp]

private theorem cell_inner_operator {X : SSet.{u}} (n : SimplexCategory)
    (a : stdSimplex.obj n ⟶ X) {p q : SimplexCategory} (h : p ⟶ q)
    (t : (J.obj n).obj (op q)) :
    (kFunctor.obj X).map h.op ((kRepresentableIso.inv.app n ≫ kFunctor.map a).app (op q) t) =
      (kRepresentableIso.inv.app n ≫ kFunctor.map a).app (op p) ((J.obj n).map h.op t) :=
  (NatTrans.naturality_apply (kRepresentableIso.inv.app n ≫ kFunctor.map a) h.op t).symm

/-- The actual homotopy category of the same k-image is a groupoid for every original X. -/
theorem kFunctor_obj_isGroupoid_homotopyCategory (X : SSet.{u}) :
    CategoryTheory.IsGroupoid (kFunctor.obj X).HomotopyCategory where
  all_isIso f := by
    induction f using HomotopyCategory.hom_rec with
    | homMk e =>
      have he : e.IsEquivalence :=
        ((mem_core_obj_one_iff).mp (kImage_mem_core X ⦋1⦌ e.edge)).of_edge_eq rfl
      simpa only [Edge.IsEquivalence, Edge.toHoHom_eq_homMk] using he
    | comp f g hf hg =>
      let _ : IsIso f := hf
      let _ : IsIso g := hg
      infer_instance

end SSet.FreeGroupoidSimplex
