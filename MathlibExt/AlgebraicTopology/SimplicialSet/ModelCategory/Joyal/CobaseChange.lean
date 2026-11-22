/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.InnerAnodyneCategorical
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.InnerIsoFibrations
public import MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalenceInv
public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomVertices

/-!
# Cobase-change stability of Joyal categorical equivalences (the supporting results)

```text
(SSet.categoricalEquivalences).IsStableUnderCobaseChangeAgainst
  (MorphismProperty.monomorphisms SSet.{u}),
```

i.e. for every pushout square `IsPushout i f f' j` of simplicial sets with
`i` a monomorphism and `f` a categorical equivalence, the cobase change
`f'` is a categorical equivalence.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

variable {A B X Y Z : SSet.{u}}

/-! ## Homotopy-category objects as vertices

Objects of `SSet.hoFunctor.obj Z` are the vertices of `Z`, through
`SSet.HomotopyCategory.mk` and the bijection
`SSet.HomotopyCategory.objEquiv`. -/

private lemma hoFunctor_obj_exists_mk (Z : SSet.{u}) (x : hoFunctor.obj Z) :
    ∃ v : Z _⦋0⦌, (HomotopyCategory.mk v : hoFunctor.obj Z) = x :=
  ⟨HomotopyCategory.objEquiv x, HomotopyCategory.objEquiv.left_inv x⟩

private lemma HomotopyCategory.mk_inj {a b : Z _⦋0⦌}
    (h : (HomotopyCategory.mk a : hoFunctor.obj Z) = HomotopyCategory.mk b) :
    a = b := by
  have h2 := congrArg HomotopyCategory.objEquiv h
  simpa only [← HomotopyCategory.objEquiv_symm_apply, Equiv.apply_symm_apply]
    using h2

/-- Precomposition with a monomorphism `i` into a quasicategory `C` is an
inner fibration. This is the named form of the upstream instance obtained
from the inner pushout-product theorem
(`SSet.innerFibration_pullbackObjObjπ` in
`Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct`). -/
theorem innerFibration_pre_app_of_mono (i : A ⟶ B) [Mono i] (C : SSet.{u})
    [Quasicategory C] : InnerFibration ((pre i).app C) :=
  inferInstance

variable {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}

/-- **Precomposition with an inner anodyne extension induces an
isofibration on homotopy categories.** For `i` inner anodyne and `C` a
quasicategory, `(pre i).app C` is a trivial Kan fibration (the supporting results,
`SSet.rlp_I_pre_app_of_innerAnodyneExtensions`), hence induces an
equivalence of homotopy categories
(`SSet.hoFunctor_map_isEquivalence_of_rlp_I`) which is surjective on
objects by vertex lifting (`SSet.exists_vertex_lift_of_rlp_I`), and a
surjective equivalence is an isofibration. This is the inner anodyne
case of the additional comparison obligation in the module header. -/
theorem hoFunctor_pre_isIsofibration_of_innerAnodyneExtensions
    (hi : innerAnodyneExtensions i) (C : SSet.{u}) [Quasicategory C] :
    (hoFunctor.map ((pre i).app C)).toFunctor.IsIsofibration := by
  have hp : modelCategoryQuillen.I.rlp ((pre i).app C) :=
    rlp_I_pre_app_of_innerAnodyneExtensions hi C
  have : (hoFunctor.map ((pre i).app C)).toFunctor.IsEquivalence :=
    hoFunctor_map_isEquivalence_of_rlp_I hp
  apply Functor.isIsofibration_of_isEquivalence_of_surjective
  intro t
  obtain ⟨a, rfl⟩ := hoFunctor_obj_exists_mk ((ihom A).obj C) t
  obtain ⟨b, hb⟩ := exists_vertex_lift_of_rlp_I hp a
  refine ⟨HomotopyCategory.mk b, ?_⟩
  have hobj : (hoFunctor.map ((pre i).app C)).toFunctor.obj
        (HomotopyCategory.mk b) =
      HomotopyCategory.mk (((pre i).app C).app _ b) := rfl
  rw [hobj]
  exact congrArg HomotopyCategory.mk hb

/-! ## The isofibration property as lifting of equivalence edges

For a quasicategory `C`, the homotopy categories of `(ihom A).obj C` and
`(ihom B).obj C` have vertices as objects and every morphism between
vertices represented by an edge (`SSet.Edge.exists_toHoHom_eq`), so the
isofibration property of precomposition on homotopy categories is
exactly the statement that equivalence edges lift with prescribed source
and strict target restriction. -/

/-- The equivalence-edge lifting property for precomposition with
`i : A ⟶ B` into `C`: every equivalence edge `e` of `(ihom A).obj C`
whose source is the restriction of a vertex `b` of `(ihom B).obj C`
lifts to an equivalence edge `e'` of `(ihom B).obj C` out of `b` whose
target restricts on the nose to the target of `e` and whose image in
the homotopy category of `(ihom A).obj C` is the morphism represented
by `e`. By `SSet.hoFunctor_pre_isIsofibration_iff`, for `C` a
quasicategory this is equivalent to precomposition with `i` inducing
an isofibration on homotopy categories. -/
def HoPreEquivalenceEdgeLifting (i : A ⟶ B) (C : SSet.{u}) : Prop :=
  ∀ {b : ((ihom B).obj C) _⦋0⦌} {a' : ((ihom A).obj C) _⦋0⦌}
    (e : Edge (((pre i).app C).app _ b) a'), e.IsEquivalence →
      ∃ (b' : ((ihom B).obj C) _⦋0⦌)
        (hb' : ((pre i).app C).app _ b' = a') (e' : Edge b b'),
        e'.IsEquivalence ∧
          (e'.map ((pre i).app C)).toHoHom ≫
            eqToHom (congrArg HomotopyCategory.mk hb') = e.toHoHom

variable (C : SSet.{u}) [Quasicategory C]

/-- **Isofibrations on `hFun` are equivalence-edge lifting.** For a
quasicategory `C`, precomposition with `i` induces an isofibration
`h Fun(B, C) ⟶ h Fun(A, C)` of ordinary categories if and only if
equivalence edges of `Fun(A, C)` lift along `(pre i).app C` in the
sense of `SSet.HoPreEquivalenceEdgeLifting`. -/
theorem hoFunctor_pre_isIsofibration_iff :
    (hoFunctor.map ((pre i).app C)).toFunctor.IsIsofibration ↔
      HoPreEquivalenceEdgeLifting i C := by
  change (mapHomotopyCategory ((pre i).app C)).IsIsofibration ↔
    HoPreEquivalenceEdgeLifting i C
  constructor
  · intro hIso b a' e he
    have := hIso
    have : IsIso (show (mapHomotopyCategory ((pre i).app C)).obj
        (HomotopyCategory.mk b) ⟶ HomotopyCategory.mk a' from
        e.toHoHom) := he
    obtain ⟨Y', φ, hY, hφ⟩ := Functor.exists_iso_lift
      (mapHomotopyCategory ((pre i).app C))
      (asIso (show (mapHomotopyCategory ((pre i).app C)).obj
        (HomotopyCategory.mk b) ⟶ HomotopyCategory.mk a' from
        e.toHoHom))
    obtain ⟨b', hb'⟩ := hoFunctor_obj_exists_mk ((ihom B).obj C) Y'
    have hY' : ((pre i).app C).app _ b' = a' := by
      have h2 : (mapHomotopyCategory ((pre i).app C)).obj
            (HomotopyCategory.mk b') = HomotopyCategory.mk a' := by
        rw [hb']
        exact hY
      have hobj : (mapHomotopyCategory ((pre i).app C)).obj
            (HomotopyCategory.mk b') =
          HomotopyCategory.mk (((pre i).app C).app _ b') := rfl
      rw [hobj] at h2
      exact HomotopyCategory.mk_inj h2
    let φ' : HomotopyCategory.mk b ≅ HomotopyCategory.mk b' :=
      φ ≪≫ (eqToIso hb').symm
    obtain ⟨e', he'⟩ := Edge.exists_toHoHom_eq φ'.hom
    have he'iso : e'.IsEquivalence := by
      rw [Edge.isEquivalence_iff, he']
      infer_instance
    refine ⟨b', hY', e', he'iso, ?_⟩
    have hFφ' : (mapHomotopyCategory ((pre i).app C)).map φ'.hom ≫
          eqToHom (congrArg HomotopyCategory.mk hY') = e.toHoHom := by
      have h4 : (mapHomotopyCategory ((pre i).app C)).map φ.hom ≫
            eqToHom hY = e.toHoHom :=
        congrArg Iso.hom hφ
      have e1 : (mapHomotopyCategory ((pre i).app C)).map φ'.hom =
          (mapHomotopyCategory ((pre i).app C)).map φ.hom ≫
            eqToHom (congrArg
              (mapHomotopyCategory ((pre i).app C)).obj hb'.symm) := by
        change (mapHomotopyCategory ((pre i).app C)).map
            (φ ≪≫ (eqToIso hb').symm).hom = _
        rw [Iso.trans_hom, Functor.map_comp]
        congr 1
        rw [show (eqToIso hb').symm.hom = eqToHom hb'.symm from rfl,
          eqToHom_map]
      have hst : eqToHom (congrArg
            (mapHomotopyCategory ((pre i).app C)).obj hb'.symm) ≫
          eqToHom (congrArg
            (mapHomotopyCategory ((pre i).app C)).obj hb') =
          𝟙 ((mapHomotopyCategory ((pre i).app C)).obj Y') := by
        rw [eqToHom_trans]
        change eqToHom (rfl : (mapHomotopyCategory ((pre i).app C)).obj Y' =
          (mapHomotopyCategory ((pre i).app C)).obj Y') = _
        rw [eqToHom_refl]
      have stepA : (mapHomotopyCategory ((pre i).app C)).map φ'.hom ≫
            eqToHom ((congrArg
              (mapHomotopyCategory ((pre i).app C)).obj hb').trans
              hY) =
          ((mapHomotopyCategory ((pre i).app C)).map φ'.hom ≫
            eqToHom (congrArg
              (mapHomotopyCategory ((pre i).app C)).obj hb')) ≫
            eqToHom hY := by
        rw [← eqToHom_trans, Category.assoc]
      have stepB : ((mapHomotopyCategory ((pre i).app C)).map φ'.hom ≫
            eqToHom (congrArg
              (mapHomotopyCategory ((pre i).app C)).obj hb')) ≫
            eqToHom hY =
          (mapHomotopyCategory ((pre i).app C)).map φ.hom ≫
            eqToHom hY := by
        rw [e1,
          Category.assoc ((mapHomotopyCategory ((pre i).app C)).map
            φ.hom)
            (eqToHom (congrArg
              (mapHomotopyCategory ((pre i).app C)).obj hb'.symm))
            (eqToHom (congrArg
              (mapHomotopyCategory ((pre i).app C)).obj hb')),
          hst, Category.comp_id]
      change (mapHomotopyCategory ((pre i).app C)).map φ'.hom ≫
          eqToHom ((congrArg
            (mapHomotopyCategory ((pre i).app C)).obj hb').trans
            hY) = e.toHoHom
      exact stepA.trans (stepB.trans h4)
    rw [← he', ← Edge.toHoHom_map] at hFφ'
    exact hFφ'
  · intro hLift
    apply Functor.isIsofibration_of_exists_lift_hom
    intro X₀ Y₀ g hg
    obtain ⟨b, rfl⟩ := hoFunctor_obj_exists_mk ((ihom B).obj C) X₀
    obtain ⟨a', rfl⟩ := hoFunctor_obj_exists_mk ((ihom A).obj C) Y₀
    obtain ⟨e, he⟩ := Edge.exists_toHoHom_eq (show
      (HomotopyCategory.mk (((pre i).app C).app _ b)) ⟶
        HomotopyCategory.mk a' from g)
    have heiso : e.IsEquivalence := by
      rw [Edge.isEquivalence_iff, he]
      exact hg
    obtain ⟨b', hb', e', he'iso, hcomp⟩ := hLift e heiso
    refine ⟨HomotopyCategory.mk b', e'.toHoHom,
      congrArg HomotopyCategory.mk hb', by
        rw [Edge.isEquivalence_iff] at he'iso
        exact he'iso, ?_⟩
    have hFg : (e'.map ((pre i).app C)).toHoHom ≫
          eqToHom (congrArg HomotopyCategory.mk hb') = g :=
      hcomp.trans he
    rw [← Edge.toHoHom_map]
    exact hFg

omit [Quasicategory C] in
/-- Strict simplex-level lifts of equivalence edges give the homotopy
category lifting property: if every equivalence edge of
`(ihom A).obj C` out of a restricted vertex is the strict image
`(e'.map ((pre i).app C)).edge = e.edge` of an equivalence edge `e'` of
`(ihom B).obj C` with strict target restriction, then
`SSet.HoPreEquivalenceEdgeLifting i C` holds, hence (for `C` a
quasicategory) precomposition with `i` induces an isofibration on
homotopy categories. This is the form in which a proof of
the additional comparison obligation by horn filling in `C` produces its lifts (the general case
is now proved, by shuffle-derived prism extension, in
`DwyerKanFinal.lean`). -/
theorem hoPreEquivalenceEdgeLifting_of_strict_lift
    (h : ∀ {b : ((ihom B).obj C) _⦋0⦌} {a' : ((ihom A).obj C) _⦋0⦌}
      (e : Edge (((pre i).app C).app _ b) a'), e.IsEquivalence →
        ∃ (b' : ((ihom B).obj C) _⦋0⦌)
          (_hb' : ((pre i).app C).app _ b' = a') (e' : Edge b b'),
          e'.IsEquivalence ∧ (e'.map ((pre i).app C)).edge = e.edge) :
    HoPreEquivalenceEdgeLifting i C := by
  intro b a' e he
  obtain ⟨b', hb', e', he'iso, hedge⟩ := h e he
  subst hb'
  have hEq : e'.map ((pre i).app C) = e := Edge.ext hedge
  refine ⟨b', rfl, e', he'iso, ?_⟩
  rw [hEq]
  change e.toHoHom ≫ eqToHom
      (rfl : HomotopyCategory.mk (((pre i).app C).app _ b') =
        HomotopyCategory.mk (((pre i).app C).app _ b')) = e.toHoHom
  rw [eqToHom_refl, Category.comp_id]

/-! ## Cobase change in the cases closed by the landed calculus -/

/-- Cobase change of an inner anodyne extension along any map is a
categorical equivalence: inner anodyne extensions are stable under
cobase change (they are a left lifting class,
`SSet.innerAnodyneExtensions.IsStableUnderCobaseChange` upstream) and
inner anodyne extensions are categorical (the supporting results). -/
theorem categoricalEquivalences.of_isPushout_of_innerAnodyneExtensions
    (sq : IsPushout i f f' j) (hf : innerAnodyneExtensions f) :
    categoricalEquivalences f' :=
  categoricalEquivalences.of_innerAnodyneExtensions
    (MorphismProperty.IsStableUnderCobaseChange.of_isPushout sq hf)

/-- **Cobase change of a categorical equivalence along an inner anodyne
extension is categorical.** The opposite map `j` is inner anodyne
(cobase change of `i`), hence categorical; then `i ≫ f' = f ≫ j` is
categorical, and `f'` is categorical by right cancellation
(two-out-of-three) against the categorical equivalence `i`. -/
theorem categoricalEquivalences.of_isPushout_along_innerAnodyneExtensions
    (sq : IsPushout i f f' j) (hi : innerAnodyneExtensions i)
    (hf : categoricalEquivalences f) : categoricalEquivalences f' := by
  have hj : innerAnodyneExtensions j :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout sq.flip hi
  have hcomp : categoricalEquivalences (i ≫ f') := by
    rw [sq.w]
    exact MorphismProperty.comp_mem _ f j hf
      (categoricalEquivalences.of_innerAnodyneExtensions hj)
  exact MorphismProperty.HasOfPrecompProperty.of_precomp i f'
    (categoricalEquivalences.of_innerAnodyneExtensions hi) hcomp

/-- Categorical equivalences are stable under cobase change against
inner anodyne extensions. This is the proved restriction of the target
stability against all monomorphisms; the general monomorphism case is
the additional comparison obligation/(the supporting result) in the module header (the additional comparison obligation is now proved in
`DwyerKanFinal.lean`). -/
instance categoricalEquivalences.isStableUnderCobaseChangeAgainst_innerAnodyneExtensions :
    categoricalEquivalences.IsStableUnderCobaseChangeAgainst
      innerAnodyneExtensions := by
  constructor
  intro A B i hi
  constructor
  intro Z W f' g' g sq hf
  exact categoricalEquivalences.of_isPushout_along_innerAnodyneExtensions
    sq hi hf

/-- Cobase change of a categorical equivalence along an isomorphism is
categorical: the opposite map is again an isomorphism (isomorphisms
are stable under cobase change), and the same two-out-of-three
argument applies. -/
theorem categoricalEquivalences.of_isPushout_along_isIso
    (sq : IsPushout i f f' j) [IsIso i]
    (hf : categoricalEquivalences f) : categoricalEquivalences f' := by
  have hj : IsIso j :=
    (MorphismProperty.isomorphisms.iff j).1
      (MorphismProperty.IsStableUnderCobaseChange.of_isPushout sq.flip
        ((MorphismProperty.isomorphisms.iff i).2 inferInstance))
  have hcomp : categoricalEquivalences (i ≫ f') := by
    rw [sq.w]
    exact MorphismProperty.comp_mem _ f j hf
      (categoricalEquivalences.of_isIso j)
  exact MorphismProperty.HasOfPrecompProperty.of_precomp i f'
    (categoricalEquivalences.of_isIso i) hcomp

end SSet

end
