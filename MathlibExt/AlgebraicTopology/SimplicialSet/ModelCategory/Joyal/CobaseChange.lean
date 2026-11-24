/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.InnerAnodyneCategorical
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.InnerIsoFibrations
public import MathlibExt.AlgebraicTopology.Quasicategory.EdgeEquivalenceInv
public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomVertices

/-! # Cobase-change stability of Joyal categorical equivalences (packet T26)

Target of this packet (JY3 red gate of `Blueprint/JoyalModelStructure/README.md`):
categorical equivalences are stable under cobase change along monomorphisms,
in the `MorphismProperty` form consumed by left properness,

```text
(SSet.categoricalEquivalences).IsStableUnderCobaseChangeAgainst
  (MorphismProperty.monomorphisms SSet.{u}),
```

i.e. for every pushout square `IsPushout i f f' j` of simplicial sets with
`i` a monomorphism and `f` a categorical equivalence, the cobase change
`f'` is a categorical equivalence.

## Proof strategy and what this module proves

The intended proof (Joyal, cf. HTT §2.3 and Stevenson §2) tests against a
quasicategory `C`. Precomposition turns the pushout into a pullback
square of functor quasicategories, the top map `(pre f).app C` induces
an equivalence on homotopy categories by assumption, and the left map
`(pre i).app C` lies in `SSet.innerIsoFibrations`: it is an inner
fibration by the upstream pushout-product theorem (`SSet.innerFibration_pre_app_of_mono`
here) whose induced functor on homotopy categories is an isofibration.
Essential surjectivity of the base change then follows from the
isofibration property alone, and full faithfulness from gluing
simplices over the pullback. Of this assembly, the present module
proves the isofibration half: it characterizes the required
isofibration property by lifting of equivalence edges
(`SSet.HoPreEquivalenceEdgeLifting` and
`SSet.hoFunctor_pre_isIsofibration_iff`), records the strict
simplex-level form in which horn filling will supply the lifts
(`SSet.hoPreEquivalenceEdgeLifting_of_strict_lift`), and proves the
isofibration property when `i` is inner anodyne
(`SSet.hoFunctor_pre_isIsofibration_of_innerAnodyneExtensions`, where
`(pre i).app C` is even a trivial Kan fibration by packet T10). The
pullback assembly itself is TODO(T26-C) below and is *not* proved
here.

Consequently the cobase-change theorem itself is proved here in the cases
that the landed calculus closes:

* `f` inner anodyne, `i` arbitrary
  (`SSet.categoricalEquivalences.of_isPushout_of_innerAnodyneExtensions`);
* `i` inner anodyne, `f` categorical, by two-out-of-three along the
  pushout square
  (`SSet.categoricalEquivalences.of_isPushout_along_innerAnodyneExtensions`),
  packaged as the instance
  `SSet.categoricalEquivalences.isStableUnderCobaseChangeAgainst_innerAnodyneExtensions`;
* `i` an isomorphism
  (`SSet.categoricalEquivalences.of_isPushout_along_isIso`).

## What is not proved here (precise TODOs)

The general monomorphism case is *not* proved in this module, and no
statement here should be read as claiming it. By the results above it is
reduced to the following three inputs; the first (TODO(T26-A)) is now
proved in full generality in `DwyerKanFinal.lean` (packet T66), while the
other two remain open. The first two are
equivalent in content to Joyal's extension theorem for maps into a
quasicategory along a monomorphism (relative special outer horn
filling), and the third is the formal pullback assembly:

* TODO(T26-A) — CLOSED (`SSet.hoFunctor_pre_isIsofibration_of_mono`, now
  in `DwyerKanFinal.lean`): for `i : A ⟶ B` a
  monomorphism and `C` a quasicategory,
  `(SSet.hoFunctor.map ((MonoidalClosed.pre i).app C)).toFunctor.IsIsofibration`.
  By `SSet.hoFunctor_pre_isIsofibration_iff` this is the statement that
  equivalence edges of `(ihom A).obj C` lift along `(pre i).app C` with
  prescribed source and strict target restriction. Transposed along
  `MonoidalClosed.internalHomAdjunction₂` this is extension of maps
  `B ⊗ Δ[0] ∪ A ⊗ Δ[1] ⟶ C` (with inverse data over `A`) along the
  pushout-product of `i` with an endpoint inclusion, which is filled
  skeletal-inductively by special outer horns in `C`
  (`SSet.exists_fill_horn_left_of_isEquivalence`, landed on this
  base by #6840 in `SpecialOuterHornGeneral.lean`; not imported
  here) together with
  extension of equivalence edges along `Δ[1] ⟶ SSet.coherentIso`, i.e.
  TODO(T15) of `MathlibExt/AlgebraicTopology/Quasicategory/CoherentIsoExtension.lean`,
  which remains open for a general quasicategory (only the
  `2`-coskeletal case is proved there). The special cases `i` an
  isomorphism (formal) and `i` inner anodyne
  (`SSet.hoFunctor_pre_isIsofibration_of_innerAnodyneExtensions`
  here) are proved. The general case, formerly blocked on TODO(T15),
  is now proved by shuffle-derived prism extension rather than the
  coherent-`Iso` route sketched above.
* TODO(T26-B) fullness and faithfulness of
  `(SSet.hoFunctor.map ((MonoidalClosed.pre f').app C)).toFunctor` in the
  situation above. Even granting TODO(T26-A) and the essential
  surjectivity assembly of TODO(T26-C), fullness requires correcting
  an edge of `(ihom B).obj C` within its homotopy class so that its
  restriction to `(ihom A).obj C` agrees on the nose with a prescribed
  edge: lifting a `2`-simplex through the inner fibration
  `(pre i).app C` along a special outer horn `Λ[2, 2]` whose special
  edge is degenerate, equivalently the dimension-`≤ 2` relative case
  of the same Joyal extension input as TODO(T26-A); faithfulness
  requires the analogous correction of `CompStruct` witnesses through
  inner horns `Λ[3, 1]`/`Λ[3, 2]`. (The alternative mapping-space
  proof via right properness of the Kan model structure is packet T28
  territory and has not landed either.)
* TODO(T26-C) the pullback assembly, in two formal steps whose
  ingredients are all landed but which were not carried out in this
  packet:
  (1) `SSet.isPullback_pre_app_of_isPushout`: for
  `sq : IsPushout i f f' j` and any `C`,
  `IsPullback ((pre f').app C) ((pre j).app C) ((pre i).app C)
  ((pre f).app C)` in `SSet`. Expected proof:
  `PullbackCone.IsLimit.mk` with lift
  `s ↦ curry (sqT.desc (uncurry s.fst) (uncurry s.snd) _)` where
  `sqT := Functor.map_isPushout (tensorRight s.pt) sq`, the
  compatibility of the uncurried cone legs by
  `MonoidalClosed.uncurry_pre_app` and `PullbackCone.condition`, and
  the factorization and uniqueness clauses by `uncurry_pre_app`,
  `MonoidalClosed.uncurry_curry`/`curry_uncurry`,
  `IsPushout.inl_desc`/`inr_desc` and `IsPushout.hom_ext`.
  (2) `SSet.hoFunctor_pre_essSurj_of_isPushout_of_isIsofibration`:
  in the situation of the target theorem, if furthermore
  `(hoFunctor.map ((pre i).app C)).toFunctor.IsIsofibration` (the
  conclusion of TODO(T26-A)), then
  `(hoFunctor.map ((pre f').app C)).toFunctor` is essentially
  surjective. Expected proof: at a vertex `b` of `(ihom B).obj C`,
  take `objPreimage`/`isoPreimage` for the equivalence induced by
  `f`, correct `b` up to isomorphism by
  `Functor.exists_iso_lift` so that its restriction agrees on the
  nose with the preimage vertex, glue the two maps along the
  pushout by `IsPushout.desc`, and transport back along
  `SSet.ihomVertexEquiv` using `SSet.ihomVertexEquiv_pre_app` and
  `IsPushout.inl_desc`. With (A), (B) and (C) in place the target
  instance is then the conjunction of essential surjectivity (C)(2)
  with the full-and-faithful statement (B).

## References

* J. Lurie, *Higher Topos Theory*, Corollary 2.3.2.5 (internal Homs of
  quasicategories) and Corollary 2.4.6.5 (the fibration criterion with a
  quasicategory codomain).
* D. Stevenson, *Notes on the Joyal model structure*, arXiv:1810.05233,
  §2 (pushout stability of categorical equivalences).
* *Kerodon*, Corollary 4.5.4.14 (stability under pushout along
  monomorphisms).
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
quasicategory, `(pre i).app C` is a trivial Kan fibration (packet T10,
`SSet.rlp_I_pre_app_of_innerAnodyneExtensions`), hence induces an
equivalence of homotopy categories
(`SSet.hoFunctor_map_isEquivalence_of_rlp_I`) which is surjective on
objects by vertex lifting (`SSet.exists_vertex_lift_of_rlp_I`), and a
surjective equivalence is an isofibration. This is the inner anodyne
case of TODO(T26-A) in the module header. -/
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
vertices represented by an edge (`SSet.Edge.exists_homMk_eq`), so the
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
          (HomotopyCategory.homMk (e'.map ((pre i).app C))) ≫
            eqToHom (congrArg HomotopyCategory.mk hb') = (HomotopyCategory.homMk e)

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
        (HomotopyCategory.homMk e)) := he
    obtain ⟨Y', φ, hY, hφ⟩ := Functor.exists_iso_lift
      (mapHomotopyCategory ((pre i).app C))
      (asIso (show (mapHomotopyCategory ((pre i).app C)).obj
        (HomotopyCategory.mk b) ⟶ HomotopyCategory.mk a' from
        (HomotopyCategory.homMk e)))
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
    obtain ⟨e', he'⟩ := Edge.exists_homMk_eq φ'.hom
    have he'iso : e'.IsEquivalence := by
      rw [Edge.isEquivalence_iff, he']
      infer_instance
    refine ⟨b', hY', e', he'iso, ?_⟩
    have hFφ' : (mapHomotopyCategory ((pre i).app C)).map φ'.hom ≫
          eqToHom (congrArg HomotopyCategory.mk hY') = (HomotopyCategory.homMk e) := by
      have h4 : (mapHomotopyCategory ((pre i).app C)).map φ.hom ≫
            eqToHom hY = (HomotopyCategory.homMk e) :=
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
            hY) = (HomotopyCategory.homMk e)
      exact stepA.trans (stepB.trans h4)
    rw [← he', mapHomotopyCategory_map_homMk] at hFφ'
    exact hFφ'
  · intro hLift
    apply Functor.isIsofibration_of_exists_lift_hom
    intro X₀ Y₀ g hg
    obtain ⟨b, rfl⟩ := hoFunctor_obj_exists_mk ((ihom B).obj C) X₀
    obtain ⟨a', rfl⟩ := hoFunctor_obj_exists_mk ((ihom A).obj C) Y₀
    obtain ⟨e, he⟩ := Edge.exists_homMk_eq (show
      (HomotopyCategory.mk (((pre i).app C).app _ b)) ⟶
        HomotopyCategory.mk a' from g)
    have heiso : e.IsEquivalence := by
      rw [Edge.isEquivalence_iff, he]
      exact hg
    obtain ⟨b', hb', e', he'iso, hcomp⟩ := hLift e heiso
    refine ⟨HomotopyCategory.mk b', (HomotopyCategory.homMk e'),
      congrArg HomotopyCategory.mk hb', by
        rw [Edge.isEquivalence_iff] at he'iso
        exact he'iso, ?_⟩
    have hFg : (HomotopyCategory.homMk (e'.map ((pre i).app C))) ≫
          eqToHom (congrArg HomotopyCategory.mk hb') = g :=
      hcomp.trans he
    rw [mapHomotopyCategory_map_homMk]
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
TODO(T26-A) by horn filling in `C` produces its lifts (the general case
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
  change (HomotopyCategory.homMk e) ≫ eqToHom
      (rfl : HomotopyCategory.mk (((pre i).app C).app _ b') =
        HomotopyCategory.mk (((pre i).app C).app _ b')) = (HomotopyCategory.homMk e)
  rw [eqToHom_refl, Category.comp_id]

/-! ## Cobase change in the cases closed by the landed calculus -/

/-- Cobase change of an inner anodyne extension along any map is a
categorical equivalence: inner anodyne extensions are stable under
cobase change (they are a left lifting class,
`SSet.innerAnodyneExtensions.IsStableUnderCobaseChange` upstream) and
inner anodyne extensions are categorical (packet T10). -/
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
TODO(T26-B)/(T26-C) in the module header (TODO(T26-A) is now proved in
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
