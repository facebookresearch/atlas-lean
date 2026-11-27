/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinAssociatorNaturality
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceAdjunction
public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinSliceIndexIso

/-!
# Original iterated over-slices and cone vertices

Currying a whole map from a left cone identifies its over-slice with
the over-slice at the corresponding vertex of the diagram over-slice.
All maps use the actual join associator and the original whole-map
universal property.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace SSet.sliceOver

variable {X K : SSet.{u}}

/-- The whole-map universal property commutes with original precomposition. -/
theorem homEquiv_precomp_val (f : K ⟶ X) {A B : SSet.{u}}
    (a : A ⟶ B) (g : B ⟶ sliceOver X f) :
    ((homEquiv X f A) (a ≫ g)).1 =
      (join.map a).app K ≫ ((homEquiv X f B) g).1 := by
  simp only [homEquiv_apply, CategoryTheory.Functor.map_comp,
    NatTrans.comp_app, Category.assoc]

/-- On a representing simplex, the whole-map equivalence is the literal joined map. -/
theorem homEquiv_yoneda_val (f : K ⟶ X) (n : SimplexCategory)
    (g : stdSimplex.obj n ⟶ sliceOver X f) :
    ((homEquiv X f (stdSimplex.obj n)) g).1 = (yonedaEquiv g).1 := by
  conv_lhs => rw [← yonedaEquiv.symm_apply_apply g, homEquiv_apply]
  exact evaluation_wholeMap X f n (yonedaEquiv g)

/-- The given whole cone, as the actual vertex of the original diagram over-slice. -/
def conePoint (f : K ⟶ X) (q : (Δ[0] : SSet.{u}) ⋆ K ⟶ X)
    (hq : joinInr Δ[0] K ≫ q = f) :
    (Δ[0] : SSet.{u}) ⟶ sliceOver X f :=
  yonedaEquiv.symm ⟨q, hq⟩

/-- The cone point reads back to the same original entire cone. -/
theorem conePoint_wholeMap (f : K ⟶ X) (q : (Δ[0] : SSet.{u}) ⋆ K ⟶ X)
    (hq : joinInr Δ[0] K ≫ q = f) :
    ((homEquiv X f Δ[0]) (conePoint f q hq)).1 = q := by
  rw [homEquiv_yoneda_val]
  have h := (SSet.yonedaEquiv (X := sliceOver X f) (n := ⦋0⦌)).apply_symm_apply
    (⟨q, hq⟩ : (sliceOver X f).obj (op ⦋0⦌))
  exact congrArg (fun s : (sliceOver X f).obj (op ⦋0⦌) => s.1) h

/-- Restricting the fixed diagram restricts its whole cone point. -/
theorem conePoint_restrict {X K L : SSet.{u}} (f : K ⟶ X)
    (q : (Δ[0] : SSet.{u}) ⋆ K ⟶ X) (hq : joinInr Δ[0] K ≫ q = f) (i : L ⟶ K) :
    sliceOver.conePoint f q hq ≫ sliceOver.restrict X f i =
      sliceOver.conePoint (i ≫ f) ((join.obj Δ[0]).map i ≫ q) (by
        rw [← Category.assoc, ← map_comp_joinInr, Category.assoc, hq]) := by
  apply (sliceOver.homEquiv X (i ≫ f) Δ[0]).injective
  apply Subtype.ext
  rw [sliceOver.conePoint_wholeMap, sliceOver.homEquiv_yoneda_val,
    yonedaEquiv_comp, sliceOver.restrict_app_val,
    ← sliceOver.homEquiv_yoneda_val, sliceOver.conePoint_wholeMap]

/-- Curry every original joined simplex into the original diagram slice. -/
def nestedSimplex (f : K ⟶ X) (q : (Δ[0] : SSet.{u}) ⋆ K ⟶ X)
    (hq : joinInr Δ[0] K ≫ q = f) (n : SimplexCategory)
    (s : (sliceOver X q).obj (op n)) :
    (sliceOver (sliceOver X f) (conePoint f q hq)).obj (op n) := by
  let A := stdSimplex.obj n
  let g : (A ⋆ Δ[0]) ⋆ K ⟶ X := (joinAssocIso A Δ[0] K).hom ≫ s.1
  have hg : joinInr (A ⋆ Δ[0]) K ≫ g = f := by
    dsimp only [g]
    rw [← Category.assoc, joinInr_comp_joinAssocIso_hom, Category.assoc, s.2, hq]
  let k : A ⋆ Δ[0] ⟶ sliceOver X f := (homEquiv X f (A ⋆ Δ[0])).symm ⟨g, hg⟩
  have hk : joinInr A Δ[0] ≫ k = conePoint f q hq := by
    apply (homEquiv X f Δ[0]).injective
    apply Subtype.ext
    rw [homEquiv_precomp_val, conePoint_wholeMap]
    have hkg : ((homEquiv X f (A ⋆ Δ[0])) k).1 = g :=
      congrArg Subtype.val ((homEquiv X f (A ⋆ Δ[0])).apply_symm_apply ⟨g, hg⟩)
    rw [hkg]
    dsimp only [g]
    rw [← Category.assoc, join_map_joinInr_comp_joinAssocIso_hom, s.2]
  exact ⟨k, hk⟩

/-- Currying retains the actual whole joined simplex through the canonical associator. -/
theorem nestedSimplex_wholeMap (f : K ⟶ X)
    (q : (Δ[0] : SSet.{u}) ⋆ K ⟶ X) (hq : joinInr Δ[0] K ≫ q = f)
    (n : SimplexCategory) (s : (sliceOver X q).obj (op n)) :
    ((homEquiv X f (stdSimplex.obj n ⋆ Δ[0])) (nestedSimplex f q hq n s).1).1 =
      (joinAssocIso (stdSimplex.obj n) Δ[0] K).hom ≫ s.1 := by
  exact congrArg Subtype.val ((homEquiv X f (stdSimplex.obj n ⋆ Δ[0])).apply_symm_apply _)

/-- Uncurry the same original nested simplex into the whole cone diagram. -/
def unnestedSimplex (f : K ⟶ X) (q : (Δ[0] : SSet.{u}) ⋆ K ⟶ X)
    (hq : joinInr Δ[0] K ≫ q = f) (n : SimplexCategory)
    (s : (sliceOver (sliceOver X f) (conePoint f q hq)).obj (op n)) :
    (sliceOver X q).obj (op n) := by
  let A := stdSimplex.obj n
  let g := ((homEquiv X f (A ⋆ Δ[0])) s.1).1
  have hi : joinInr A (Δ[0] ⋆ K) ≫ (joinAssocIso A Δ[0] K).inv =
      (join.map (joinInr A Δ[0])).app K := by
    apply (cancel_mono (joinAssocIso A Δ[0] K).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (join_map_joinInr_comp_joinAssocIso_hom A Δ[0] K).symm
  refine ⟨(joinAssocIso A Δ[0] K).inv ≫ g, ?_⟩
  rw [← Category.assoc, hi]
  change (join.map (joinInr A Δ[0])).app K ≫
      ((homEquiv X f (A ⋆ Δ[0])) s.1).1 = q
  rw [← homEquiv_precomp_val, s.2, conePoint_wholeMap]

/-- Uncurrying retains the entire original joined map. -/
theorem unnestedSimplex_val (f : K ⟶ X)
    (q : (Δ[0] : SSet.{u}) ⋆ K ⟶ X) (hq : joinInr Δ[0] K ≫ q = f)
    (n : SimplexCategory)
    (s : (sliceOver (sliceOver X f) (conePoint f q hq)).obj (op n)) :
    (unnestedSimplex f q hq n s).1 =
      (joinAssocIso (stdSimplex.obj n) Δ[0] K).inv ≫
        ((homEquiv X f (stdSimplex.obj n ⋆ Δ[0])) s.1).1 :=
  rfl

/-- The original whole-map currying is natural in every simplex operator. -/
def nest (f : K ⟶ X) (q : (Δ[0] : SSet.{u}) ⋆ K ⟶ X)
    (hq : joinInr Δ[0] K ≫ q = f) :
    sliceOver X q ⟶ sliceOver (sliceOver X f) (conePoint f q hq) where
  app n := ↾fun s => nestedSimplex f q hq n.unop s
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply (homEquiv X f (stdSimplex.obj m.unop ⋆ Δ[0])).injective
    apply Subtype.ext
    change ((homEquiv X f (stdSimplex.obj m.unop ⋆ Δ[0]))
        (nestedSimplex f q hq m.unop ((sliceOver X q).map α s)).1).1 =
      ((homEquiv X f (stdSimplex.obj m.unop ⋆ Δ[0]))
        ((join.map (stdSimplex.map α.unop)).app Δ[0] ≫
          (nestedSimplex f q hq n.unop s).1)).1
    rw [nestedSimplex_wholeMap, homEquiv_precomp_val, nestedSimplex_wholeMap]
    change (joinAssocIso (stdSimplex.obj m.unop) Δ[0] K).hom ≫
        ((join.map (stdSimplex.map α.unop)).app (Δ[0] ⋆ K) ≫ s.1) =
      (join.map ((join.map (stdSimplex.map α.unop)).app Δ[0])).app K ≫
        ((joinAssocIso (stdSimplex.obj n.unop) Δ[0] K).hom ≫ s.1)
    rw [← Category.assoc, ← Category.assoc, joinAssocIso_naturality_left]

/-- The original uncurrying is natural in every simplex operator. -/
def unnest (f : K ⟶ X) (q : (Δ[0] : SSet.{u}) ⋆ K ⟶ X)
    (hq : joinInr Δ[0] K ≫ q = f) :
    sliceOver (sliceOver X f) (conePoint f q hq) ⟶ sliceOver X q where
  app n := ↾fun s => unnestedSimplex f q hq n.unop s
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change (unnestedSimplex f q hq m.unop
        ((sliceOver (sliceOver X f) (conePoint f q hq)).map α s)).1 =
      (join.map (stdSimplex.map α.unop)).app (Δ[0] ⋆ K) ≫
        (unnestedSimplex f q hq n.unop s).1
    rw [unnestedSimplex_val, unnestedSimplex_val]
    change (joinAssocIso (stdSimplex.obj m.unop) Δ[0] K).inv ≫
        ((homEquiv X f (stdSimplex.obj m.unop ⋆ Δ[0]))
          ((join.map (stdSimplex.map α.unop)).app Δ[0] ≫ s.1)).1 =
      (join.map (stdSimplex.map α.unop)).app (Δ[0] ⋆ K) ≫
        ((joinAssocIso (stdSimplex.obj n.unop) Δ[0] K).inv ≫
          ((homEquiv X f (stdSimplex.obj n.unop ⋆ Δ[0])) s.1).1)
    rw [homEquiv_precomp_val]
    have hnat : (joinAssocIso (stdSimplex.obj m.unop) Δ[0] K).inv ≫
        (join.map ((join.map (stdSimplex.map α.unop)).app Δ[0])).app K =
      (join.map (stdSimplex.map α.unop)).app (Δ[0] ⋆ K) ≫
        (joinAssocIso (stdSimplex.obj n.unop) Δ[0] K).inv := by
      apply (cancel_epi (joinAssocIso (stdSimplex.obj m.unop) Δ[0] K).hom).mp
      rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      rw [← Category.assoc, ← joinAssocIso_naturality_left, Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, hnat, Category.assoc]

/-- The actual over-slice of a whole cone is its iterated diagram over-slice. -/
def coneOverSliceIso (f : K ⟶ X) (q : (Δ[0] : SSet.{u}) ⋆ K ⟶ X)
    (hq : joinInr Δ[0] K ≫ q = f) :
    sliceOver X q ≅ sliceOver (sliceOver X f) (conePoint f q hq) where
  hom := nest f q hq
  inv := unnest f q hq
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change (unnestedSimplex f q hq n.unop (nestedSimplex f q hq n.unop s)).1 = s.1
    rw [unnestedSimplex_val, nestedSimplex_wholeMap]
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    apply (homEquiv X f (stdSimplex.obj n.unop ⋆ Δ[0])).injective
    apply Subtype.ext
    change ((homEquiv X f (stdSimplex.obj n.unop ⋆ Δ[0]))
        (nestedSimplex f q hq n.unop (unnestedSimplex f q hq n.unop s)).1).1 =
      ((homEquiv X f (stdSimplex.obj n.unop ⋆ Δ[0])) s.1).1
    rw [nestedSimplex_wholeMap, unnestedSimplex_val]
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The actual iterated-slice projection is the original cone-to-diagram restriction. -/
theorem coneOverSliceIso_hom_proj (f : K ⟶ X)
    (q : (Δ[0] : SSet.{u}) ⋆ K ⟶ X) (hq : joinInr Δ[0] K ≫ q = f) :
    (coneOverSliceIso f q hq).hom ≫
        proj (sliceOver X f) (conePoint f q hq) =
      restrict X q (joinInr Δ[0] K) ≫ eqToHom (congrArg (sliceOver X) hq) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  let A := stdSimplex.obj n.unop
  let k := (nestedSimplex f q hq n.unop s).1
  have hc := fixedDiagramEq_app_val hq n ((restrict X q (joinInr Δ[0] K)).app n s)
  change (yonedaEquiv (joinInl A Δ[0] ≫ k)).1 =
    (((eqToHom (congrArg (sliceOver X) hq)).app n
      ((restrict X q (joinInr Δ[0] K)).app n s)).1)
  calc
    (yonedaEquiv (joinInl A Δ[0] ≫ k)).1 =
        ((homEquiv X f A) (joinInl A Δ[0] ≫ k)).1 :=
      (homEquiv_yoneda_val f n.unop _).symm
    _ = (join.map (joinInl A Δ[0])).app K ≫
        ((homEquiv X f (A ⋆ Δ[0])) k).1 :=
      homEquiv_precomp_val f (joinInl A Δ[0]) k
    _ = (join.map (joinInl A Δ[0])).app K ≫
        ((joinAssocIso A Δ[0] K).hom ≫ s.1) := by
      rw [nestedSimplex_wholeMap]
    _ = (join.obj A).map (joinInr Δ[0] K) ≫ s.1 := by
      rw [← Category.assoc, join_map_joinInl_comp_joinAssocIso_hom]
    _ = ((restrict X q (joinInr Δ[0] K)).app n s).1 := rfl
    _ = (((eqToHom (congrArg (sliceOver X) hq)).app n
        ((restrict X q (joinInr Δ[0] K)).app n s)).1) := hc.symm

/-- The original cone restriction and the projection at its actual cone
point are isomorphic as arrows, with both original maps retained. -/
def coneRestrictionArrowIso (f : K ⟶ X)
    (q : (Δ[0] : SSet.{u}) ⋆ K ⟶ X) (hq : joinInr Δ[0] K ≫ q = f) :
    Arrow.mk (restrict X q (joinInr Δ[0] K)) ≅
      Arrow.mk (proj (sliceOver X f) (conePoint f q hq)) :=
  Arrow.isoMk (coneOverSliceIso f q hq) (eqToIso (congrArg (sliceOver X) hq))
    (coneOverSliceIso_hom_proj f q hq)

end SSet.sliceOver
