/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.IhomPrism
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CobaseChange

/-! # Cobase-change stability: completion of the formal assembly (packet T30)

This module continues
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.CobaseChange`
(packet T26) towards the red-gate statement
`(SSet.categoricalEquivalences).IsStableUnderCobaseChangeAgainst
(MorphismProperty.monomorphisms SSet.{u})`. The assembly is phrased
to consume the tools developed since T26 stalled once they land:
general special outer horns (`SpecialOuterHornGeneral.lean`,
landed on this base by #6840 but not imported or used in any proof
here), natural isomorphisms of precomposition (`HoPreNatIso.lean`),
the Dwyer–Kan characterization (`DwyerKan.lean`) and the nerve gate
(`NerveGate.lean`) — the latter three modules are not on this base.
Of that toolset, this module actually uses only the prism
dictionary from `IhomPrism.lean`
(`SSet.ihomSimplexOfPrism`/`SSet.ihomPrismOfSimplex`/`SSet.edgeOfPrism`).

## What this module proves

* TODO(T26-C)(1), unconditionally:
  `SSet.isPullback_pre_app_of_isPushout`. Precomposition sends a
  pushout square of simplicial sets to a pullback square of functor
  objects, for every target `C` (no quasicategory or monomorphism
  hypothesis). The proof is the currying argument sketched in the
  T26 header: the lift of a pullback cone is the curry of the map
  out of the tensored pushout classifying the two uncurried cone
  legs.
* The isomorphism case of TODO(T26-A):
  `SSet.hoFunctor_pre_isIsofibration_of_isIso`. Together with the
  inner anodyne case
  `SSet.hoFunctor_pre_isIsofibration_of_innerAnodyneExtensions`
  (packet T26), these are the cases of (A) closed by the landed
  calculus.
* TODO(T26-C)(2), conditionally on (A) for the left leg:
  `SSet.hoFunctor_pre_essSurj_of_isPushout_of_isIsofibration`. If
  `f` is categorical and precomposition with `i` induces an
  isofibration on homotopy categories of functor objects into a
  quasicategory `C`, then precomposition with the cobase change
  `f'` is essentially surjective on those homotopy categories.
  This is the vertex-gluing argument of the T26 header, carried
  out through `SSet.ihomVertexEquiv` and `IsPushout.desc`.
* The assembly: `SSet.categoricalEquivalences.of_isPushout_of_isIsofibration_of_full_faithful`
  combines (C)(2) with fullness/faithfulness hypotheses for `f'`
  (the content of TODO(T26-B)) to conclude that the cobase change
  of a categorical equivalence along a monomorphism is
  categorical. The packaged instance
  `(SSet.categoricalEquivalences).IsStableUnderCobaseChangeAgainst
  (MorphismProperty.monomorphisms SSet.{u})` is therefore reduced,
  with no further formal steps, to the two extension inputs below.
* The prism form of the strict-lifting reduction of (A):
  `SSet.HoPrePrismStrictExtension`,
  `SSet.hoPrePrismStrictExtension_iff_strict_lift` and
  `SSet.hoFunctor_pre_isIsofibration_of_prismStrictExtension`
  restate TODO(T26-A), through the prism dictionary of
  `IhomPrism.lean`, as strict extension of
  equivalence-edge prisms along `i ▷ Δ[1]`; and
  `SSet.exists_pre_lift_of_isPushout` is the simplex-gluing
  interface (at `Δ[1]` and `Δ[2]`) to which TODO(T26-B) is
  reduced by the pullback theorem.

## What is not proved here (precise remaining TODOs)

* TODO(T30-A) = TODO(T26-A) in general — CLOSED, now
  `SSet.hoFunctor_pre_isIsofibration_of_mono` in `DwyerKanFinal.lean`
  (packet T66), proved unconditionally by shuffle-derived prism
  extension. The analysis below is retained as the record of the
  coherent-`Iso` route, which the landed proof bypasses. Statement:
  for `i : A ⟶ B` a monomorphism and `C` a quasicategory,
  `(SSet.hoFunctor.map ((MonoidalClosed.pre i).app C)).toFunctor.IsIsofibration`.
  By `SSet.hoFunctor_pre_isIsofibration_iff` and
  `SSet.hoPreEquivalenceEdgeLifting_of_strict_lift` (packet T26),
  it suffices to strictly lift equivalence edges of
  `(ihom A).obj C` along `(pre i).app C`, i.e. (here) to prove
  `SSet.HoPrePrismStrictExtension i C`. Transposed along the
  prism dictionary of `IhomPrism.lean`
  (`SSet.ihomSimplexOfPrism`/`SSet.ihomPrismOfSimplex`,
  `SSet.ihomSimplexOfPrism_pre_app`), a strict lift is an
  extension of a map out of the pushout
  `B ⊗ Δ[0] ∪_{A ⊗ Δ[0]} A ⊗ SSet.coherentIso` (the coherent
  inverse data over `A` supplied by extending the equivalence
  edge along `Δ[1] ⟶ SSet.coherentIso`) along the pushout-product
  of `i` with the endpoint inclusion
  `Δ[0] ⟶ SSet.coherentIso`. The coherent-`Iso` route would have
  needed two inputs, neither of which is formal (both bypassed by
  the landed shuffle proof):
  (A1) TODO(T15) of `CoherentIsoExtension.lean` for a general
  quasicategory: an equivalence edge extends along
  `Δ[1] ⟶ SSet.coherentIso`. Only the `2`-coskeletal case
  (`SSet.Edge.isEquivalence_iff_coherentIso_extension_of_isCoskeletal`,
  hence nerves) and the `2`-coskeleton-valued form
  (`SSet.Edge.IsEquivalence.exists_coherentIso_extension_cosk`)
  are landed. The general case is a skeletal induction over the
  alternating simplices of `SSet.coherentIso` whose attaching
  steps are special outer horns, now available in all dimensions
  as `SSet.hasSpecialOuterHornFilling_of_quasicategory`
  (`SpecialOuterHornGeneral.lean`); the induction itself has not
  been formalized.
  (A2) The relative form: extension along the pushout-product of
  a monomorphism with `Δ[0] ⟶ SSet.coherentIso` (equivalently
  with an endpoint inclusion `Δ[0] ⟶ Δ[1]` carrying coherent
  data), by skeletal induction on `i` reducing each cell
  attachment to a special outer horn in `C`. No relative
  special-horn extension API is landed. Note that
  `SSet.coherentIso.edgeExtensionProperty_of_quasicategory`
  (packet T22) is the case `i = ` endpoint inclusion of the
  analogous prism problem and does not substitute for (A2).
* TODO(T30-B) = TODO(T26-B): fullness and faithfulness of
  `(SSet.hoFunctor.map ((MonoidalClosed.pre f').app C)).toFunctor`
  in the pushout situation. By
  `SSet.isPullback_pre_app_of_isPushout` here, `1`-simplices (resp.
  `2`-simplices) of `(ihom Y).obj C` are exactly the pairs of
  simplices of `(ihom B).obj C` and `(ihom X).obj C` whose images
  in `(ihom A).obj C` agree on the nose; the remaining step is to
  correct a simplex of `(ihom B).obj C` within its homotopy class
  (resp. a `CompStruct` witness) so that agreement holds. As
  recorded in the T26 header this is special outer horn lifting
  through the inner fibration `(pre i).app C` in dimensions
  `≤ 3`, i.e. the low-dimensional relative case of (A2); it is
  not formalized here, and the assembly theorem above takes
  fullness/faithfulness as explicit hypotheses.

Consequently no statement in this module claims cobase-change
stability against a general monomorphism unconditionally; the
unconditional cases remain those of packet T26 (inner anodyne or
isomorphism left leg, inner anodyne top leg).

## References

* J. Lurie, *Higher Topos Theory*, §2.3.
* D. Stevenson, *Notes on the Joyal model structure*,
  arXiv:1810.05233, §2.
* *Kerodon*, Corollary 4.5.4.14.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits MonoidalClosed MonoidalCategory Opposite

open scoped Simplicial

namespace SSet

variable {A B X Y Z : SSet.{u}} {i : A ⟶ B} {f : A ⟶ X} {f' : B ⟶ Y} {j : X ⟶ Y}

/-! ## Precomposition sends pushouts to pullbacks (TODO(T26-C)(1)) -/

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
discharges TODO(T26-C)(1) of the `CobaseChange.lean` header. -/
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

/-! ## The isomorphism case of TODO(T26-A) -/

private lemma cobaseMk_inj {Z : SSet.{u}} {a b : Z _⦋0⦌}
    (h : (HomotopyCategory.mk a : hoFunctor.obj Z) = HomotopyCategory.mk b) :
    a = b := by
  have h2 := congrArg HomotopyCategory.objEquiv h
  simpa only [← HomotopyCategory.objEquiv_symm_apply, Equiv.apply_symm_apply]
    using h2

/-- **Precomposition with an isomorphism induces an isofibration on
homotopy categories.** This is the isomorphism case of TODO(T26-A)
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

/-! ## Essential surjectivity of the cobase change (TODO(T26-C)(2)) -/

/-- **Essential surjectivity of precomposition with a cobase change,
granted the isofibration property of the left leg.** In a pushout
square `IsPushout i f f' j` with `f` a categorical equivalence, if
precomposition with `i` into a quasicategory `C` induces an
isofibration on homotopy categories (the conclusion of
TODO(T26-A) for this `i` and `C`), then precomposition with `f'`
is essentially surjective on homotopy categories of functor objects
into `C`. At a vertex `b` of `(ihom B).obj C`, essential
surjectivity for `f` supplies a vertex of `(ihom X).obj C` and an
isomorphism over `(ihom A).obj C`; the isofibration property
corrects `b` up to isomorphism so that its restriction to
`(ihom A).obj C` agrees on the nose, and the two classifying maps
then glue along the pushout. This discharges TODO(T26-C)(2) of the
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
TODO(T26-A) proved in packet T26. -/
theorem hoFunctor_pre_essSurj_of_isPushout_along_innerAnodyneExtensions
    (sq : IsPushout i f f' j) (hi : innerAnodyneExtensions i)
    (hf : categoricalEquivalences f) (C : SSet.{u}) [Quasicategory C] :
    (hoFunctor.map ((pre f').app C)).toFunctor.EssSurj :=
  hoFunctor_pre_essSurj_of_isPushout_of_isIsofibration sq hf C
    (hoFunctor_pre_isIsofibration_of_innerAnodyneExtensions hi C)

/-- **Cobase change of a categorical equivalence along a
monomorphism, granted (A) and (B).** If precomposition with `i`
induces an isofibration on homotopy categories of functor objects
into every quasicategory (TODO(T26-A) for `i`) and precomposition
with the cobase change `f'` is full and faithful on those homotopy
categories (TODO(T26-B) for this square), then `f'` is a
categorical equivalence: essential surjectivity is
`SSet.hoFunctor_pre_essSurj_of_isPushout_of_isIsofibration`. (T30-A)
is now proved (`DwyerKanFinal.lean`); once (T30-B) of the module
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

/-! ## The prism form of strict equivalence-edge lifting

The strict simplex-level lifting hypothesis of
`SSet.hoPreEquivalenceEdgeLifting_of_strict_lift` (packet T26) is,
through the prism dictionary of `IhomPrism.lean`, an
extension problem for maps out of prisms: an edge of
`(ihom A).obj C` is a prism `A ⊗ Δ[1] ⟶ C`
(`SSet.ihomPrismOfSimplex`), and a strict lift is a prism
`B ⊗ Δ[1] ⟶ C` extending it along `i ▷ Δ[1]` whose source vertex
is prescribed and which is itself an equivalence edge. The
remaining content of TODO(T30-A) is exactly
`SSet.HoPrePrismStrictExtension i C` for `i` a monomorphism and
`C` a quasicategory; see the module header for the coherent data
and relative special-horn induction this hides. -/

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

/-- **TODO(T26-A) follows from prism strict extension.** If
equivalence-edge prisms into a quasicategory `C` extend strictly
along `i ▷ Δ[1]` (`SSet.HoPrePrismStrictExtension i C`), then
precomposition with `i` induces an isofibration on homotopy
categories of functor objects into `C`. This is the prism
restatement of `SSet.hoPreEquivalenceEdgeLifting_of_strict_lift`
combined with `SSet.hoFunctor_pre_isIsofibration_iff`; the
extension property itself for a general monomorphism, formerly
TODO(T30-A) of the module header, is now proved by shuffle-derived
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
TODO(T30-B) is reduced once the correction of simplices within
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
