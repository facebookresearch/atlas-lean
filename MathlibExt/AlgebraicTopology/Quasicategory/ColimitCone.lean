/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.Quasicategory.InitialVertexCriterion
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceAdjunction
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinAssociatorNaturality
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceIndexIso

/-!
# Native colimit cones and original iterated under-slices

Currying the entire original right cone identifies its under-slice with the
under-slice at its actual point in the diagram under-slice. The Day associator
and its original inclusion equations retain all simplices and operators.
The native colimit condition is consequently initiality of that point.

The construction is dual to the original iterated over-slice construction.
The source definition is Higher Topos Theory, Definition 1.2.13.4.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

open CategoryTheory MonoidalCategory Limits Opposite
open scoped Simplicial CategoryTheory.MonoidalCategory.DayFunctor

universe u

namespace SSet

namespace sliceUnder

variable {X K : SSet.{u}}

/-- Whole-map currying commutes with original precomposition in the free factor. -/
theorem homEquiv_precomp_val (f : K ⟶ X) {A B : SSet.{u}}
    (a : A ⟶ B) (g : B ⟶ sliceUnder X f) :
    ((homEquiv X f A) (a ≫ g)).val =
      (join.obj K).map a ≫ ((homEquiv X f B) g).val := by
  simp only [homEquiv_apply, Functor.map_comp, Category.assoc]

/-- On a representing simplex, currying reads the same whole original joined map. -/
theorem homEquiv_yoneda_val (f : K ⟶ X) (n : SimplexCategory)
    (g : stdSimplex.obj n ⟶ sliceUnder X f) :
    ((homEquiv X f (stdSimplex.obj n)) g).val = (yonedaEquiv g).val := by
  conv_lhs => rw [← yonedaEquiv.symm_apply_apply g, homEquiv_apply]
  exact evaluation_wholeMap X f n (yonedaEquiv g)

/-- The given entire right cone, as its actual point in the original diagram under-slice. -/
def conePoint (f : K ⟶ X) (q : K ⋆ (Δ[0] : SSet.{u}) ⟶ X)
    (hq : joinInl K Δ[0] ≫ q = f) : (Δ[0] : SSet.{u}) ⟶ sliceUnder X f :=
  yonedaEquiv.symm ⟨q, hq⟩

/-- The point reads back to the same entire original right cone. -/
theorem conePoint_wholeMap (f : K ⟶ X) (q : K ⋆ (Δ[0] : SSet.{u}) ⟶ X)
    (hq : joinInl K Δ[0] ≫ q = f) :
    ((homEquiv X f Δ[0]) (conePoint f q hq)).val = q := by
  rw [homEquiv_yoneda_val]
  exact congrArg Subtype.val
    ((yonedaEquiv (X := sliceUnder X f) (n := ⦋0⦌)).apply_symm_apply ⟨q, hq⟩)

/-- The actual cone point projects to the given original right cone vertex. -/
@[reassoc]
theorem conePoint_proj (f : K ⟶ X) (q : K ⋆ (Δ[0] : SSet.{u}) ⟶ X)
    (hq : joinInl K Δ[0] ≫ q = f) :
    conePoint f q hq ≫ proj X f = joinInr K Δ[0] ≫ q := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp]
  have h : yonedaEquiv (conePoint f q hq) =
      (⟨q, hq⟩ : (sliceUnder X f).obj (op ⦋0⦌)) :=
    (yonedaEquiv (X := sliceUnder X f) (n := ⦋0⦌)).apply_symm_apply ⟨q, hq⟩
  rw [h]
  rfl

/-- Curry each whole original under-cone simplex through the actual join associator. -/
def nestedSimplex (f : K ⟶ X) (q : K ⋆ (Δ[0] : SSet.{u}) ⟶ X)
    (hq : joinInl K Δ[0] ≫ q = f) (n : SimplexCategory)
    (s : (sliceUnder X q).obj (op n)) :
    (sliceUnder (sliceUnder X f) (conePoint f q hq)).obj (op n) := by
  let A := stdSimplex.obj n
  let g : K ⋆ (Δ[0] ⋆ A) ⟶ X := (joinAssocIso K Δ[0] A).inv ≫ s.val
  have hi : joinInl K (Δ[0] ⋆ A) ≫ (joinAssocIso K Δ[0] A).inv =
      joinInl K Δ[0] ≫ joinInl (K ⋆ Δ[0]) A := by
    apply (cancel_mono (joinAssocIso K Δ[0] A).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Category.assoc, joinInl_comp_joinAssocIso_hom]
  have hg : joinInl K (Δ[0] ⋆ A) ≫ g = f := by
    dsimp only [g]
    rw [← Category.assoc, hi, Category.assoc, s.property, hq]
  let k : Δ[0] ⋆ A ⟶ sliceUnder X f := (homEquiv X f (Δ[0] ⋆ A)).symm ⟨g, hg⟩
  have hk : joinInl Δ[0] A ≫ k = conePoint f q hq := by
    apply (homEquiv X f Δ[0]).injective
    apply Subtype.ext
    rw [homEquiv_precomp_val, conePoint_wholeMap]
    have hkg : ((homEquiv X f (Δ[0] ⋆ A)) k).val = g :=
      congrArg Subtype.val ((homEquiv X f (Δ[0] ⋆ A)).apply_symm_apply ⟨g, hg⟩)
    rw [hkg]
    dsimp only [g]
    have hp : (join.obj K).map (joinInl Δ[0] A) ≫ (joinAssocIso K Δ[0] A).inv =
        joinInl (K ⋆ Δ[0]) A := by
      apply (cancel_mono (joinAssocIso K Δ[0] A).hom).mp
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
        joinInl_pair_comp_joinAssocIso_hom]
    rw [← Category.assoc, hp, s.property]
  exact ⟨k, hk⟩

/-- Currying retains the whole original joined map through the canonical associator. -/
theorem nestedSimplex_wholeMap (f : K ⟶ X) (q : K ⋆ (Δ[0] : SSet.{u}) ⟶ X)
    (hq : joinInl K Δ[0] ≫ q = f) (n : SimplexCategory)
    (s : (sliceUnder X q).obj (op n)) :
    ((homEquiv X f (Δ[0] ⋆ stdSimplex.obj n)) (nestedSimplex f q hq n s).val).val =
      (joinAssocIso K Δ[0] (stdSimplex.obj n)).inv ≫ s.val := by
  exact congrArg Subtype.val ((homEquiv X f (Δ[0] ⋆ stdSimplex.obj n)).apply_symm_apply _)

/-- Uncurry the same original nested simplex into the whole original cone diagram. -/
def unnestedSimplex (f : K ⟶ X) (q : K ⋆ (Δ[0] : SSet.{u}) ⟶ X)
    (hq : joinInl K Δ[0] ≫ q = f) (n : SimplexCategory)
    (s : (sliceUnder (sliceUnder X f) (conePoint f q hq)).obj (op n)) :
    (sliceUnder X q).obj (op n) := by
  let A := stdSimplex.obj n
  let g := ((homEquiv X f (Δ[0] ⋆ A)) s.val).val
  refine ⟨(joinAssocIso K Δ[0] A).hom ≫ g, ?_⟩
  rw [← Category.assoc, joinInl_pair_comp_joinAssocIso_hom]
  change (join.obj K).map (joinInl Δ[0] A) ≫
    ((homEquiv X f (Δ[0] ⋆ A)) s.val).val = q
  rw [← homEquiv_precomp_val, s.property, conePoint_wholeMap]

/-- Uncurrying reads the entire original joined map. -/
theorem unnestedSimplex_val (f : K ⟶ X) (q : K ⋆ (Δ[0] : SSet.{u}) ⟶ X)
    (hq : joinInl K Δ[0] ≫ q = f) (n : SimplexCategory)
    (s : (sliceUnder (sliceUnder X f) (conePoint f q hq)).obj (op n)) :
    (unnestedSimplex f q hq n s).val =
      (joinAssocIso K Δ[0] (stdSimplex.obj n)).hom ≫
        ((homEquiv X f (Δ[0] ⋆ stdSimplex.obj n)) s.val).val := rfl

/-- Original whole-map currying is natural for every original simplex operator. -/
def nest (f : K ⟶ X) (q : K ⋆ (Δ[0] : SSet.{u}) ⟶ X)
    (hq : joinInl K Δ[0] ≫ q = f) :
    sliceUnder X q ⟶ sliceUnder (sliceUnder X f) (conePoint f q hq) where
  app n := ↾fun s => nestedSimplex f q hq n.unop s
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply (homEquiv X f (Δ[0] ⋆ stdSimplex.obj m.unop)).injective
    apply Subtype.ext
    change ((homEquiv X f (Δ[0] ⋆ stdSimplex.obj m.unop))
        (nestedSimplex f q hq m.unop ((sliceUnder X q).map α s)).val).val =
      ((homEquiv X f (Δ[0] ⋆ stdSimplex.obj m.unop))
        ((join.obj Δ[0]).map (stdSimplex.map α.unop) ≫
          (nestedSimplex f q hq n.unop s).val)).val
    rw [nestedSimplex_wholeMap, homEquiv_precomp_val, nestedSimplex_wholeMap]
    change (joinAssocIso K Δ[0] (stdSimplex.obj m.unop)).inv ≫
        ((join.obj (K ⋆ Δ[0])).map (stdSimplex.map α.unop) ≫ s.val) =
      (join.obj K).map ((join.obj Δ[0]).map (stdSimplex.map α.unop)) ≫
        ((joinAssocIso K Δ[0] (stdSimplex.obj n.unop)).inv ≫ s.val)
    have hnat : (joinAssocIso K Δ[0] (stdSimplex.obj m.unop)).inv ≫
        (join.obj (K ⋆ Δ[0])).map (stdSimplex.map α.unop) =
      (join.obj K).map ((join.obj Δ[0]).map (stdSimplex.map α.unop)) ≫
        (joinAssocIso K Δ[0] (stdSimplex.obj n.unop)).inv := by
      apply (cancel_epi (joinAssocIso K Δ[0] (stdSimplex.obj m.unop)).hom).mp
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
        ← Category.assoc, ← joinAssocIso_naturality_right,
        Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, hnat, Category.assoc]

/-- Original uncurrying is natural for every original simplex operator. -/
def unnest (f : K ⟶ X) (q : K ⋆ (Δ[0] : SSet.{u}) ⟶ X)
    (hq : joinInl K Δ[0] ≫ q = f) :
    sliceUnder (sliceUnder X f) (conePoint f q hq) ⟶ sliceUnder X q where
  app n := ↾fun s => unnestedSimplex f q hq n.unop s
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change (unnestedSimplex f q hq m.unop
        ((sliceUnder (sliceUnder X f) (conePoint f q hq)).map α s)).val =
      (join.obj (K ⋆ Δ[0])).map (stdSimplex.map α.unop) ≫
        (unnestedSimplex f q hq n.unop s).val
    rw [unnestedSimplex_val, unnestedSimplex_val]
    change (joinAssocIso K Δ[0] (stdSimplex.obj m.unop)).hom ≫
        ((homEquiv X f (Δ[0] ⋆ stdSimplex.obj m.unop))
          ((join.obj Δ[0]).map (stdSimplex.map α.unop) ≫ s.val)).val =
      (join.obj (K ⋆ Δ[0])).map (stdSimplex.map α.unop) ≫
        ((joinAssocIso K Δ[0] (stdSimplex.obj n.unop)).hom ≫
          ((homEquiv X f (Δ[0] ⋆ stdSimplex.obj n.unop)) s.val).val)
    rw [homEquiv_precomp_val, ← Category.assoc, ← Category.assoc,
      joinAssocIso_naturality_right]

/-- The actual under-slice of the whole right cone is its iterated diagram under-slice. -/
def coneUnderSliceIso (f : K ⟶ X) (q : K ⋆ (Δ[0] : SSet.{u}) ⟶ X)
    (hq : joinInl K Δ[0] ≫ q = f) :
    sliceUnder X q ≅ sliceUnder (sliceUnder X f) (conePoint f q hq) where
  hom := nest f q hq
  inv := unnest f q hq
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change (unnestedSimplex f q hq n.unop (nestedSimplex f q hq n.unop s)).val = s.val
    rw [unnestedSimplex_val, nestedSimplex_wholeMap,
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply (homEquiv X f (Δ[0] ⋆ stdSimplex.obj n.unop)).injective
    apply Subtype.ext
    change ((homEquiv X f (Δ[0] ⋆ stdSimplex.obj n.unop))
        (nestedSimplex f q hq n.unop (unnestedSimplex f q hq n.unop s)).val).val =
      ((homEquiv X f (Δ[0] ⋆ stdSimplex.obj n.unop)) s.val).val
    rw [nestedSimplex_wholeMap, unnestedSimplex_val,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The actual iterated under-projection is the original cone-to-diagram restriction. -/
theorem coneUnderSliceIso_hom_proj (f : K ⟶ X) (q : K ⋆ (Δ[0] : SSet.{u}) ⟶ X)
    (hq : joinInl K Δ[0] ≫ q = f) :
    (coneUnderSliceIso f q hq).hom ≫ proj (sliceUnder X f) (conePoint f q hq) =
      restrict X q (joinInl K Δ[0]) ≫ eqToHom (congrArg (sliceUnder X) hq) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  let A := stdSimplex.obj n.unop
  let k := (nestedSimplex f q hq n.unop s).val
  have hc := fixedDiagramEq_app_val hq n ((restrict X q (joinInl K Δ[0])).app n s)
  change (yonedaEquiv (joinInr Δ[0] A ≫ k)).val =
    ((eqToHom (congrArg (sliceUnder X) hq)).app n
      ((restrict X q (joinInl K Δ[0])).app n s)).val
  calc
    (yonedaEquiv (joinInr Δ[0] A ≫ k)).val =
        ((homEquiv X f A) (joinInr Δ[0] A ≫ k)).val :=
      (homEquiv_yoneda_val f n.unop _).symm
    _ = (join.obj K).map (joinInr Δ[0] A) ≫
        ((homEquiv X f (Δ[0] ⋆ A)) k).val := homEquiv_precomp_val f _ k
    _ = (join.obj K).map (joinInr Δ[0] A) ≫
        ((joinAssocIso K Δ[0] A).inv ≫ s.val) := by rw [nestedSimplex_wholeMap]
    _ = (join.map (joinInl K Δ[0])).app A ≫ s.val := by
      have hi : (join.obj K).map (joinInr Δ[0] A) ≫ (joinAssocIso K Δ[0] A).inv =
          (join.map (joinInl K Δ[0])).app A := by
        apply (cancel_mono (joinAssocIso K Δ[0] A).hom).mp
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
          join_map_joinInl_comp_joinAssocIso_hom]
      rw [← Category.assoc, hi]
    _ = ((restrict X q (joinInl K Δ[0])).app n s).val := rfl
    _ = ((eqToHom (congrArg (sliceUnder X) hq)).app n
        ((restrict X q (joinInl K Δ[0])).app n s)).val := hc.symm

/-- The two original cone-restriction maps are isomorphic as actual arrows. -/
def coneRestrictionArrowIso (f : K ⟶ X) (q : K ⋆ (Δ[0] : SSet.{u}) ⟶ X)
    (hq : joinInl K Δ[0] ≫ q = f) :
    Arrow.mk (restrict X q (joinInl K Δ[0])) ≅
      Arrow.mk (proj (sliceUnder X f) (conePoint f q hq)) :=
  Arrow.isoMk (coneUnderSliceIso f q hq) (eqToIso (congrArg (sliceUnder X) hq))
    (coneUnderSliceIso_hom_proj f q hq)

end sliceUnder

/-- The native colimit condition lifts every original boundary against the whole
right-cone restriction. -/
def IsColimitCone {X K : SSet.{u}} (q : K ⋆ (Δ[0] : SSet.{u}) ⟶ X) : Prop :=
  ∀ n : ℕ, HasLiftingProperty (boundary n).ι (sliceUnder.restrict X q (joinInl K Δ[0]))

/-- The native colimit condition is initiality of the actual whole cone point. -/
theorem isColimitCone_iff_isInitialVertex {X K : SSet.{u}} (f : K ⟶ X)
    (q : K ⋆ (Δ[0] : SSet.{u}) ⟶ X) (hq : joinInl K Δ[0] ≫ q = f) :
    IsColimitCone q ↔ IsInitialVertex (sliceUnder.conePoint f q hq) := by
  rw [isInitialVertex_iff]
  unfold IsColimitCone
  apply forall_congr'
  intro n
  exact HasLiftingProperty.iff_of_arrow_iso_right (boundary n).ι
    (sliceUnder.coneRestrictionArrowIso f q hq)

end SSet
