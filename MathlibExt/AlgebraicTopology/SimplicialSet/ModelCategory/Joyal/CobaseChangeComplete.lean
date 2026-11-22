/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomPrism
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CobaseChange

/-!
# Cobase-change stability: completion of the formal assembly (the supporting results)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

variable {A B X Y Z : SSet.{u}} {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}

/-!
## Precomposition sends pushouts to pullbacks (the additional comparison obligation(1))
-/

/-- **Precomposition turns pushouts into pullbacks.** For a pushout
square `IsPushout i f f' j` of simplicial sets and any simplicial set
`C`, the induced square of functor objects

```text
Fun(Y, C) ⟶ Fun(B, C)
   |            |
   v            v
Fun(X, C) ⟶ Fun(A, C)
```

is a pullback square in `SSet`. The lift of a cone `s` is the curry
of the map out of the pushout tensored with `s.pt` classifying the
two uncurried cone legs, which agree over `A ⊗ s.pt` by
`MonoidalClosed.uncurry_pre_app` and the cone condition; the
factorization and uniqueness clauses are the dual computation with
`MonoidalClosed.curry_pre_app`, `MonoidalClosed.uncurry_curry` and
`IsPushout.inl_desc`/`IsPushout.inr_desc`/`IsPushout.hom_ext`. This
discharges the additional comparison obligation(1) of the `CobaseChange.lean` header. -/
theorem isPullback_pre_app_of_isPushout (sq : IsPushout i f f' j)
    (C : SSet.{u}) :
    IsPullback ((pre f').app C) ((pre j).app C) ((pre i).app C)
      ((pre f).app C) where
  w := by
    have h1 : (pre f').app C ≫ (pre i).app C = (pre (i ≫ f')).app C := by
      rw [pre_map]; rfl
    have h2 : (pre j).app C ≫ (pre f).app C = (pre (f ≫ j)).app C := by
      rw [pre_map]; rfl
    rw [h1, h2, sq.w]
  isLimit' := by
    have hw : (pre f').app C ≫ (pre i).app C = (pre j).app C ≫ (pre f).app C := by
      have h1 : (pre f').app C ≫ (pre i).app C = (pre (i ≫ f')).app C := by
        rw [pre_map]; rfl
      have h2 : (pre j).app C ≫ (pre f).app C = (pre (f ≫ j)).app C := by
        rw [pre_map]; rfl
      rw [h1, h2, sq.w]
    refine ⟨PullbackCone.IsLimit.mk hw
      (fun s => MonoidalClosed.curry
        (((tensorRight s.pt).map_isPushout sq).desc
          (MonoidalClosed.uncurry s.fst) (MonoidalClosed.uncurry s.snd)
          (by
            have hcond : s.fst ≫ (pre i).app C = s.snd ≫ (pre f).app C :=
              s.condition
            have e1 : (i ▷ s.pt) ≫ MonoidalClosed.uncurry s.fst =
                MonoidalClosed.uncurry (s.fst ≫ (pre i).app C) :=
              (MonoidalClosed.uncurry_pre_app C s.fst i).symm
            have e2 : (f ▷ s.pt) ≫ MonoidalClosed.uncurry s.snd =
                MonoidalClosed.uncurry (s.snd ≫ (pre f).app C) :=
              (MonoidalClosed.uncurry_pre_app C s.snd f).symm
            change (i ▷ s.pt) ≫ MonoidalClosed.uncurry s.fst =
              (f ▷ s.pt) ≫ MonoidalClosed.uncurry s.snd
            rw [e1, e2, hcond])))
      (fun s => by
        apply MonoidalClosed.uncurry_injective (A := B)
        rw [MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_curry]
        exact ((tensorRight s.pt).map_isPushout sq).inl_desc _ _ _)
      (fun s => by
        apply MonoidalClosed.uncurry_injective (A := X)
        rw [MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_curry]
        exact ((tensorRight s.pt).map_isPushout sq).inr_desc _ _ _)
      (fun s m hm1 hm2 => by
        apply MonoidalClosed.uncurry_injective (A := Y)
        rw [MonoidalClosed.uncurry_curry]
        apply ((tensorRight s.pt).map_isPushout sq).hom_ext
        · change (f' ▷ s.pt) ≫ MonoidalClosed.uncurry m = (f' ▷ s.pt) ≫ _
          rw [← MonoidalClosed.uncurry_pre_app C m f', hm1]
          exact (((tensorRight s.pt).map_isPushout sq).inl_desc _ _ _).symm
        · change (j ▷ s.pt) ≫ MonoidalClosed.uncurry m = (j ▷ s.pt) ≫ _
          rw [← MonoidalClosed.uncurry_pre_app C m j, hm2]
          exact (((tensorRight s.pt).map_isPushout sq).inr_desc _ _ _).symm)⟩

/-!
## The isomorphism case of the additional comparison obligation
-/

private lemma cobaseMk_inj {Z : SSet.{u}} {a b : Z _⦋0⦌}
    (h : (HomotopyCategory.mk a : hoFunctor.obj Z) = HomotopyCategory.mk b) :
    a = b := by
  have h2 := congrArg HomotopyCategory.objEquiv h
  simpa only [← HomotopyCategory.objEquiv_symm_apply, Equiv.apply_symm_apply]
    using h2

/-- **Precomposition with an isomorphism induces an isofibration on
homotopy categories.** This is the isomorphism case of the additional comparison obligation
in the `CobaseChange.lean` header: precomposition with `i` induces
an equivalence (`SSet.categoricalEquivalences.of_isIso`) which is
surjective on objects, with preimage of a vertex given by
precomposition with `inv i`, and a surjective equivalence is an
isofibration. -/
theorem hoFunctor_pre_isIsofibration_of_isIso [IsIso i] (C : SSet.{u})
    [Quasicategory C] :
    (hoFunctor.map ((pre i).app C)).toFunctor.IsIsofibration := by
  have : (hoFunctor.map ((pre i).app C)).toFunctor.IsEquivalence :=
    (categoricalEquivalences.mem_iff i).1 (categoricalEquivalences.of_isIso i)
      C inferInstance
  apply Functor.isIsofibration_of_isEquivalence_of_surjective
  intro t
  obtain ⟨a, rfl⟩ : ∃ a, HomotopyCategory.mk a = t :=
    ⟨_, HomotopyCategory.objEquiv.left_inv t⟩
  refine ⟨HomotopyCategory.mk (((pre (inv i)).app C).app _ a), ?_⟩
  have hobj : (hoFunctor.map ((pre i).app C)).toFunctor.obj
        (HomotopyCategory.mk (((pre (inv i)).app C).app _ a)) =
      HomotopyCategory.mk (((pre i).app C).app _
        (((pre (inv i)).app C).app _ a)) := rfl
  rw [hobj]
  have hcomp : (pre (inv i)).app C ≫ (pre i).app C = 𝟙 ((ihom A).obj C) := by
    have h1 : (pre (inv i)).app C ≫ (pre i).app C = (pre (i ≫ inv i)).app C := by
      rw [pre_map]; rfl
    have h2 : (pre (𝟙 A)).app C = 𝟙 ((ihom A).obj C) := by
      rw [pre_id]; rfl
    rw [h1, IsIso.hom_inv_id, h2]
  have happ : ((pre i).app C).app _ (((pre (inv i)).app C).app _ a) = a := by
    have h3 : ((pre i).app C).app _ (((pre (inv i)).app C).app _ a) =
        (((pre (inv i)).app C ≫ (pre i).app C).app _ a) := rfl
    rw [h3, hcomp]
    rfl
  exact congrArg HomotopyCategory.mk happ

/-!
## Essential surjectivity of the cobase change (the additional comparison obligation(2))
-/

/-- **Essential surjectivity of precomposition with a cobase change,
granted the isofibration property of the left leg.** In a pushout
square `IsPushout i f f' j` with `f` a categorical equivalence, if
precomposition with `i` into a quasicategory `C` induces an
isofibration on homotopy categories (the conclusion of
the additional comparison obligation for this `i` and `C`), then precomposition with `f'`
is essentially surjective on homotopy categories of functor objects
into `C`. At a vertex `b` of `(ihom B).obj C`, essential
surjectivity for `f` supplies a vertex of `(ihom X).obj C` and an
isomorphism over `(ihom A).obj C`; the isofibration property
corrects `b` up to isomorphism so that its restriction to
`(ihom A).obj C` agrees on the nose, and the two classifying maps
then glue along the pushout. This discharges the additional comparison obligation(2) of the
`CobaseChange.lean` header, conditionally on (A). -/
theorem hoFunctor_pre_essSurj_of_isPushout_of_isIsofibration
    (sq : IsPushout i f f' j) (hf : categoricalEquivalences f)
    (C : SSet.{u}) [Quasicategory C]
    (hIso : (hoFunctor.map ((pre i).app C)).toFunctor.IsIsofibration) :
    (hoFunctor.map ((pre f').app C)).toFunctor.EssSurj := by
  have hFf : (hoFunctor.map ((pre f).app C)).toFunctor.IsEquivalence :=
    (categoricalEquivalences.mem_iff f).1 hf C inferInstance
  have := hIso
  refine ⟨fun Gb => ?_⟩
  obtain ⟨b, rfl⟩ : ∃ b, HomotopyCategory.mk b = Gb :=
    ⟨_, HomotopyCategory.objEquiv.left_inv Gb⟩
  set Ff := (hoFunctor.map ((pre f).app C)).toFunctor with hFfdef
  set Fi := (hoFunctor.map ((pre i).app C)).toFunctor with hFidef
  obtain ⟨x, hx⟩ : ∃ x : ((ihom X).obj C) _⦋0⦌, HomotopyCategory.mk x =
      Ff.objPreimage (HomotopyCategory.mk (((pre i).app C).app _ b)) :=
    ⟨_, HomotopyCategory.objEquiv.left_inv _⟩
  have hφ : Ff.obj (HomotopyCategory.mk x) ≅
      HomotopyCategory.mk (((pre i).app C).app _ b) :=
    (eqToIso (congrArg Ff.obj hx)) ≪≫
      Ff.objObjPreimageIso (HomotopyCategory.mk (((pre i).app C).app _ b))
  have hg : Fi.obj (HomotopyCategory.mk b) ≅
      HomotopyCategory.mk (((pre f).app C).app _ x) := hφ.symm
  obtain ⟨Q, ψ, hQ, _hψ⟩ := Functor.exists_iso_lift Fi hg
  obtain ⟨b', hb'⟩ : ∃ b' : ((ihom B).obj C) _⦋0⦌, HomotopyCategory.mk b' = Q :=
    ⟨_, HomotopyCategory.objEquiv.left_inv Q⟩
  have hv : ((pre i).app C).app _ b' = ((pre f).app C).app _ x := by
    have h2 : Fi.obj (HomotopyCategory.mk b') =
        HomotopyCategory.mk (((pre f).app C).app _ x) := by
      rw [hb']; exact hQ
    have hobj : Fi.obj (HomotopyCategory.mk b') =
        HomotopyCategory.mk (((pre i).app C).app _ b') := rfl
    rw [hobj] at h2
    exact cobaseMk_inj h2
  have hglue : i ≫ (ihomVertexEquiv B C).symm b' =
      f ≫ (ihomVertexEquiv X C).symm x := by
    apply (ihomVertexEquiv A C).injective
    have e1 : ihomVertexEquiv A C (i ≫ (ihomVertexEquiv B C).symm b') =
        ((pre i).app C).app _ b' := by
      rw [← ihomVertexEquiv_pre_app, Equiv.apply_symm_apply]
    have e2 : ihomVertexEquiv A C (f ≫ (ihomVertexEquiv X C).symm x) =
        ((pre f).app C).app _ x := by
      rw [← ihomVertexEquiv_pre_app, Equiv.apply_symm_apply]
    rw [e1, e2]
    exact hv
  set η := sq.desc ((ihomVertexEquiv B C).symm b') ((ihomVertexEquiv X C).symm x)
    hglue with hηdef
  have hpre : ((pre f').app C).app _ (ihomVertexEquiv Y C η) = b' := by
    rw [ihomVertexEquiv_pre_app, sq.inl_desc, Equiv.apply_symm_apply]
  refine ⟨HomotopyCategory.mk (ihomVertexEquiv Y C η), ⟨?_⟩⟩
  have hobjY : (hoFunctor.map ((pre f').app C)).toFunctor.obj
        (HomotopyCategory.mk (ihomVertexEquiv Y C η)) =
      HomotopyCategory.mk b' := by
    have hr : (hoFunctor.map ((pre f').app C)).toFunctor.obj
          (HomotopyCategory.mk (ihomVertexEquiv Y C η)) =
        HomotopyCategory.mk (((pre f').app C).app _ (ihomVertexEquiv Y C η)) :=
      rfl
    rw [hr, hpre]
  exact (eqToIso hobjY) ≪≫ (ψ ≪≫ (eqToIso hb'.symm)).symm

/-- Essential surjectivity of precomposition with a cobase change
along an inner anodyne extension, unconditionally: this is
`SSet.hoFunctor_pre_essSurj_of_isPushout_of_isIsofibration` with
the isofibration input supplied by the inner anodyne case of
the additional comparison obligation proved in the supporting results. -/
theorem hoFunctor_pre_essSurj_of_isPushout_along_innerAnodyneExtensions
    (sq : IsPushout i f f' j) (hi : innerAnodyneExtensions i)
    (hf : categoricalEquivalences f) (C : SSet.{u}) [Quasicategory C] :
    (hoFunctor.map ((pre f').app C)).toFunctor.EssSurj :=
  hoFunctor_pre_essSurj_of_isPushout_of_isIsofibration sq hf C
    (hoFunctor_pre_isIsofibration_of_innerAnodyneExtensions hi C)

/-- **Cobase change of a categorical equivalence along a
monomorphism, granted (A) and (B).** If precomposition with `i`
induces an isofibration on homotopy categories of functor objects
into every quasicategory (the additional comparison obligation for `i`) and precomposition
with the cobase change `f'` is full and faithful on those homotopy
categories (the additional comparison obligation for this square), then `f'` is a
categorical equivalence: essential surjectivity is
`SSet.hoFunctor_pre_essSurj_of_isPushout_of_isIsofibration`. (the supporting result)
is now proved (`DwyerKanFinal.lean`); once (the supporting result) of the module
header is proved, this theorem with those inputs is the statement
`(SSet.categoricalEquivalences).IsStableUnderCobaseChangeAgainst
(MorphismProperty.monomorphisms SSet.{u})` with no further formal
steps. -/
theorem categoricalEquivalences.of_isPushout_of_isIsofibration_of_full_faithful
    (sq : IsPushout i f f' j) (hf : categoricalEquivalences f)
    (hIso : ∀ (C : SSet.{u}) [Quasicategory C],
      (hoFunctor.map ((pre i).app C)).toFunctor.IsIsofibration)
    (hFF : ∀ (C : SSet.{u}) [Quasicategory C],
      (hoFunctor.map ((pre f').app C)).toFunctor.Full ∧
        (hoFunctor.map ((pre f').app C)).toFunctor.Faithful) :
    categoricalEquivalences f' := by
  rw [categoricalEquivalences.mem_iff]
  intro C hC
  have := hC
  obtain ⟨hFull, hFaith⟩ := hFF C
  exact { faithful := hFaith
          full := hFull
          essSurj := hoFunctor_pre_essSurj_of_isPushout_of_isIsofibration
            sq hf C (hIso C) }

/-!
## The prism form of strict equivalence-edge lifting

The strict simplex-level lifting hypothesis of
`SSet.hoPreEquivalenceEdgeLifting_of_strict_lift` (the supporting results) is,
through the prism dictionary of `IhomPrism.lean`, an
extension problem for maps out of prisms: an edge of
`(ihom A).obj C` is a prism `A ⊗ Δ[1] ⟶ C`
(`SSet.ihomPrismOfSimplex`), and a strict lift is a prism
`B ⊗ Δ[1] ⟶ C` extending it along `i ▷ Δ[1]` whose source vertex
is prescribed and which is itself an equivalence edge. The
remaining content of the additional comparison obligation is exactly
`SSet.HoPrePrismStrictExtension i C` for `i` a monomorphism and
`C` a quasicategory; see the module header for the coherent data
and relative special-horn induction this hides.
-/

/-- The **prism strict extension property** for `i : A ⟶ B` into
`C`: every equivalence edge `e` of `(ihom A).obj C` out of a
restricted vertex is, as a prism `A ⊗ Δ[1] ⟶ C`, the restriction
along `i ▷ Δ[1]` of a prism `B ⊗ Δ[1] ⟶ C` out of the prescribed
vertex which is an equivalence edge of `(ihom B).obj C` with
strict target restriction. By
`SSet.hoFunctor_pre_isIsofibration_of_prismStrictExtension`, for
`C` a quasicategory this implies that precomposition with `i`
induces an isofibration on homotopy categories. -/
def HoPrePrismStrictExtension (i : A ⟶ B) (C : SSet.{u}) : Prop :=
  ∀ {b : ((ihom B).obj C) _⦋0⦌} {a' : ((ihom A).obj C) _⦋0⦌}
    (e : Edge (((pre i).app C).app _ b) a'), e.IsEquivalence →
      ∃ (F : B ⊗ Δ[1] ⟶ C) (b' : ((ihom B).obj C) _⦋0⦌)
        (_hb' : ((pre i).app C).app _ b' = a')
        (h₀ : ((ihom B).obj C).δ 1 (ihomSimplexOfPrism F) = b)
        (h₁ : ((ihom B).obj C).δ 0 (ihomSimplexOfPrism F) = b'),
        (edgeOfPrism F h₀ h₁).IsEquivalence ∧
          (i ▷ Δ[1]) ≫ F = ihomPrismOfSimplex e.edge

/-- The prism strict extension property is the strict
simplex-level lifting hypothesis of
`SSet.hoPreEquivalenceEdgeLifting_of_strict_lift`, read through
the prism dictionary: precomposition of prism simplices is
whiskering of prisms (`SSet.ihomSimplexOfPrism_pre_app`), and
every edge is the edge of its own prism
(`SSet.ihomSimplexOfPrism_ihomPrismOfSimplex`). -/
theorem hoPrePrismStrictExtension_iff_strict_lift (C : SSet.{u}) :
    HoPrePrismStrictExtension i C ↔
      ∀ {b : ((ihom B).obj C) _⦋0⦌} {a' : ((ihom A).obj C) _⦋0⦌}
        (e : Edge (((pre i).app C).app _ b) a'), e.IsEquivalence →
          ∃ (b' : ((ihom B).obj C) _⦋0⦌)
            (_hb' : ((pre i).app C).app _ b' = a') (e' : Edge b b'),
            e'.IsEquivalence ∧ (e'.map ((pre i).app C)).edge = e.edge := by
  constructor
  · intro h b a' e he
    obtain ⟨F, b', hb', h₀, h₁, hequiv, hF⟩ := h e he
    refine ⟨b', hb', edgeOfPrism F h₀ h₁, hequiv, ?_⟩
    rw [Edge.map_edge, edgeOfPrism_edge, ihomSimplexOfPrism_pre_app, hF,
      ihomSimplexOfPrism_ihomPrismOfSimplex]
  · intro h b a' e he
    obtain ⟨b', hb', e', hequiv, hedge⟩ := h e he
    have h₀ : ((ihom B).obj C).δ 1
        (ihomSimplexOfPrism (ihomPrismOfSimplex e'.edge)) = b := by
      rw [ihomSimplexOfPrism_ihomPrismOfSimplex]
      exact e'.src_eq
    have h₁ : ((ihom B).obj C).δ 0
        (ihomSimplexOfPrism (ihomPrismOfSimplex e'.edge)) = b' := by
      rw [ihomSimplexOfPrism_ihomPrismOfSimplex]
      exact e'.tgt_eq
    have hEdge : edgeOfPrism (ihomPrismOfSimplex e'.edge) h₀ h₁ = e' :=
      Edge.ext (by rw [edgeOfPrism_edge, ihomSimplexOfPrism_ihomPrismOfSimplex])
    refine ⟨ihomPrismOfSimplex e'.edge, b', hb', h₀, h₁, by rw [hEdge]; exact hequiv, ?_⟩
    apply (ihomSimplexEquiv A C 1).injective
    change ihomSimplexOfPrism ((i ▷ Δ[1]) ≫ ihomPrismOfSimplex e'.edge) =
      ihomSimplexOfPrism (ihomPrismOfSimplex e.edge)
    rw [← ihomSimplexOfPrism_pre_app, ihomSimplexOfPrism_ihomPrismOfSimplex,
      ihomSimplexOfPrism_ihomPrismOfSimplex, ← Edge.map_edge, hedge]

/-- **the additional comparison obligation follows from prism strict extension.** If
equivalence-edge prisms into a quasicategory `C` extend strictly
along `i ▷ Δ[1]` (`SSet.HoPrePrismStrictExtension i C`), then
precomposition with `i` induces an isofibration on homotopy
categories of functor objects into `C`. This is the prism
restatement of `SSet.hoPreEquivalenceEdgeLifting_of_strict_lift`
combined with `SSet.hoFunctor_pre_isIsofibration_iff`; the
extension property itself for a general monomorphism, formerly
the additional comparison obligation of the module header, is now proved by shuffle-derived
prism extension (see `DwyerKanFinal.lean`). -/
theorem hoFunctor_pre_isIsofibration_of_prismStrictExtension (C : SSet.{u})
    [Quasicategory C] (h : HoPrePrismStrictExtension i C) :
    (hoFunctor.map ((pre i).app C)).toFunctor.IsIsofibration :=
  (hoFunctor_pre_isIsofibration_iff C).2
    (hoPreEquivalenceEdgeLifting_of_strict_lift (C := C)
      ((hoPrePrismStrictExtension_iff_strict_lift C).1 h))

/-- The **gluing interface** of
`SSet.isPullback_pre_app_of_isPushout`: maps into `(ihom Y).obj C`
are exactly pairs of maps into `(ihom B).obj C` and
`(ihom X).obj C` whose restrictions to `(ihom A).obj C` agree.
At `W = Δ[0]` this is vertex gluing along the pushout (compare
the proof of
`SSet.hoFunctor_pre_essSurj_of_isPushout_of_isIsofibration`); at
`W = Δ[1]` and `W = Δ[2]` it is the simplex-gluing step to which
the additional comparison obligation is reduced once the correction of simplices within
their homotopy classes is available. -/
theorem exists_pre_lift_of_isPushout (sq : IsPushout i f f' j) (C : SSet.{u})
    {W : SSet.{u}} (u : W ⟶ (ihom B).obj C) (v : W ⟶ (ihom X).obj C)
    (h : u ≫ (pre i).app C = v ≫ (pre f).app C) :
    ∃ w : W ⟶ (ihom Y).obj C, w ≫ (pre f').app C = u ∧ w ≫ (pre j).app C = v :=
  ⟨(isPullback_pre_app_of_isPushout sq C).lift u v h,
    (isPullback_pre_app_of_isPushout sq C).lift_fst u v h,
    (isPullback_pre_app_of_isPushout sq C).lift_snd u v h⟩

end SSet

end
