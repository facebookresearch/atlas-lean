/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Topology.LocalAtTarget
public import MathlibExt.Topology.Category.TopCat.PushoutOpenComplement
public import MathlibExt.Topology.Category.TopCat.QuotientPushout
public import MathlibExt.Topology.Category.TopCat.Subspace

/-!
# Open restrictions of topological pushouts

Given a topological pushout square and a subset `U` of its apex, take the
preimage of `U` in each object and restrict every map to those preimages.
The resulting square commutes for any subset. If `U` is open, it is again
a pushout square, with the induced subspace topologies.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace TopCat

/--
A topological pushout square `X₁ → X₂`, `X₁ → X₃`, with apex `X₄`,
together with an arbitrary subset `U ⊆ X₄`.
-/
structure RestrictedPushout where
  /--
  The common source object of the topological pushout span.
  -/
  X₁ : TopCat.{u}
  /--
  The top-right object of the original pushout square.
  -/
  X₂ : TopCat.{u}
  /--
  The bottom-left object of the original pushout square.
  -/
  X₃ : TopCat.{u}
  /--
  The apex object of the original topological pushout.
  -/
  X₄ : TopCat.{u}
  /--
  The map from the common source `X₁` to the top leg object `X₂`.
  -/
  t : X₁ ⟶ X₂
  /--
  The map from the common source `X₁` to the left leg object `X₃`.
  -/
  l : X₁ ⟶ X₃
  /--
  The map from `X₂` to the pushout apex `X₄`.
  -/
  r : X₂ ⟶ X₄
  /--
  The map from `X₃` to the pushout apex `X₄`.
  -/
  b : X₃ ⟶ X₄
  /--
  The assertion that the four specified maps form a pushout square.
  -/
  h : IsPushout t l r b
  /--
  The chosen subset of the apex; openness is required only by the restricted
  pushout theorem.
  -/
  U : Set X₄

namespace RestrictedPushout

/--
The restricted-pushout data determined by a topological pushout square and
an arbitrary subset of its apex.
-/
def of {X₁ X₂ X₃ X₄ : TopCat.{u}}
    {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}
    (h : IsPushout t l r b) (U : Set X₄) : RestrictedPushout.{u} :=
  { X₁ := X₁
    X₂ := X₂
    X₃ := X₃
    X₄ := X₄
    t := t
    l := l
    r := r
    b := b
    h := h
    U := U }

/--
The preimage of `U` under the composite `t ≫ r`, with its subspace topology.
-/
abbrev obj₁ (P : RestrictedPushout.{u}) : TopCat.{u} :=
  TopCat.of (Set.preimage (P.t ≫ P.r) P.U)

/--
The preimage `r⁻¹(U)` with its subspace topology.
-/
abbrev obj₂ (P : RestrictedPushout.{u}) : TopCat.{u} :=
  TopCat.of (Set.preimage P.r P.U)

/--
The preimage `b⁻¹(U)` with its subspace topology.
-/
abbrev obj₃ (P : RestrictedPushout.{u}) : TopCat.{u} :=
  TopCat.of (Set.preimage P.b P.U)

/--
The subset `U` of the apex with its induced topology.
-/
abbrev obj₄ (P : RestrictedPushout.{u}) : TopCat.{u} :=
  TopCat.of P.U

/--
The top span map restricted to the corresponding preimages of `U`.
-/
noncomputable def tU (P : RestrictedPushout.{u}) : P.obj₁ ⟶ P.obj₂ :=
  AlgebraicTopology.subspaceMap P.t (by
    intro x hx
    simpa only [Set.mem_preimage, ConcreteCategory.comp_apply] using hx)

/--
The left span map restricted to the corresponding preimages of `U`.
-/
noncomputable def lU (P : RestrictedPushout.{u}) : P.obj₁ ⟶ P.obj₃ :=
  AlgebraicTopology.subspaceMap P.l (by
    intro x hx
    simp only [Set.mem_preimage, ConcreteCategory.comp_apply] at hx ⊢
    have heq : P.r (P.t x) = P.b (P.l x) := by
      simpa only [ConcreteCategory.comp_apply] using
        ConcreteCategory.congr_hom P.h.w x
    rwa [← heq])

/--
The map from `r⁻¹(U)` to `U` induced by the original right map.
-/
noncomputable def rU (P : RestrictedPushout.{u}) : P.obj₂ ⟶ P.obj₄ :=
  AlgebraicTopology.subspaceMap P.r (fun _ hx => hx)

/--
The map from `b⁻¹(U)` to `U` induced by the original bottom map.
-/
noncomputable def bU (P : RestrictedPushout.{u}) : P.obj₃ ⟶ P.obj₄ :=
  AlgebraicTopology.subspaceMap P.b (fun _ hx => hx)

/--
The preimages of `U` under `t ≫ r` and `l ≫ b` are equal, by commutativity
of the original pushout square.
-/
theorem source_preimage_eq (P : RestrictedPushout.{u}) :
    Set.preimage (P.t ≫ P.r) P.U = Set.preimage (P.l ≫ P.b) P.U := by
  ext x
  have heq := ConcreteCategory.congr_hom P.h.w x
  simp only [ConcreteCategory.comp_apply] at heq
  change P.r (P.t x) ∈ P.U ↔ P.b (P.l x) ∈ P.U
  rw [heq]

/--
The restricted maps satisfy `tU ≫ rU = lU ≫ bU`.
-/
theorem w (P : RestrictedPushout.{u}) : P.tU ≫ P.rU = P.lU ≫ P.bU := by
  apply TopCat.hom_ext
  ext x
  exact ConcreteCategory.congr_hom P.h.w x.1

/--
The restricted top map followed by its target inclusion equals its source
inclusion followed by the original top map.
-/
@[reassoc]
theorem tU_incl (P : RestrictedPushout.{u}) :
    P.tU ≫ AlgebraicTopology.subspaceIncl (Set.preimage P.r P.U) =
      AlgebraicTopology.subspaceIncl (Set.preimage (P.t ≫ P.r) P.U) ≫ P.t :=
  AlgebraicTopology.subspaceMap_comp_subspaceIncl _ _

/--
The restricted left map followed by its target inclusion equals its source
inclusion followed by the original left map.
-/
@[reassoc]
theorem lU_incl (P : RestrictedPushout.{u}) :
    P.lU ≫ AlgebraicTopology.subspaceIncl (Set.preimage P.b P.U) =
      AlgebraicTopology.subspaceIncl (Set.preimage (P.t ≫ P.r) P.U) ≫ P.l :=
  AlgebraicTopology.subspaceMap_comp_subspaceIncl _ _

/--
The restricted right map followed by inclusion into the apex equals the
preimage inclusion followed by the original right map.
-/
@[reassoc]
theorem rU_incl (P : RestrictedPushout.{u}) :
    P.rU ≫ AlgebraicTopology.subspaceIncl P.U =
      AlgebraicTopology.subspaceIncl (Set.preimage P.r P.U) ≫ P.r :=
  AlgebraicTopology.subspaceMap_comp_subspaceIncl _ _

/--
The restricted bottom map followed by inclusion into the apex equals the
preimage inclusion followed by the original bottom map.
-/
@[reassoc]
theorem bU_incl (P : RestrictedPushout.{u}) :
    P.bU ≫ AlgebraicTopology.subspaceIncl P.U =
      AlgebraicTopology.subspaceIncl (Set.preimage P.b P.U) ≫ P.b :=
  AlgebraicTopology.subspaceMap_comp_subspaceIncl _ _

private noncomputable def preimageSumHomeomorph
    {A B C : Type u} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] (r : C(A, C)) (b : C(B, C)) (U : Set C) :
    Set.preimage r U ⊕ Set.preimage b U ≃ₜ
      Set.preimage (Sum.elim r b) U := by
  let S : Set (A ⊕ B) := Set.preimage (Sum.elim r b) U
  let f : Set.preimage r U ⊕ Set.preimage b U → S :=
    Sum.elim (S.restrictPreimage Sum.inl) (S.restrictPreimage Sum.inr)
  have hleft : IsOpenEmbedding
      (S.restrictPreimage (Sum.inl : A → A ⊕ B)) :=
    Topology.IsOpenEmbedding.inl.restrictPreimage S
  have hright : IsOpenEmbedding
      (S.restrictPreimage (Sum.inr : B → A ⊕ B)) :=
    Topology.IsOpenEmbedding.inr.restrictPreimage S
  have hinj : Function.Injective f := by
    apply Function.Injective.sumElim hleft.injective hright.injective
    intro x y hxy
    have h := congrArg Subtype.val hxy
    cases h
  have hsurj : Function.Surjective f := by
    rintro ⟨z, hz⟩
    cases z with
    | inl x => exact ⟨Sum.inl ⟨x, hz⟩, rfl⟩
    | inr x => exact ⟨Sum.inr ⟨x, hz⟩, rfl⟩
  exact IsHomeomorph.homeomorph f
    ⟨hleft.continuous.sumElim hright.continuous,
      hleft.isOpenMap.sumElim hright.isOpenMap, hinj, hsurj⟩

private theorem restrictedCoproduct_isQuotientMap
    (P : RestrictedPushout.{u}) (hU : IsOpen P.U) :
    IsQuotientMap (coprod.desc P.rU P.bU).hom := by
  let q : C(P.X₂ ⊕ P.X₃, P.X₄) :=
    ⟨Sum.elim P.r P.b, P.r.hom.continuous.sumElim P.b.hom.continuous⟩
  let qU : C(Set.preimage q P.U, P.U) :=
    ⟨P.U.restrictPreimage q, q.continuous.restrictPreimage⟩
  let eSum := preimageSumHomeomorph P.r.hom P.b.hom P.U
  let m : P.obj₂ ⨿ P.obj₃ ⟶ P.obj₄ :=
    (TopCat.coprodIsoSum P.obj₂ P.obj₃).hom ≫
      (TopCat.isoOfHomeo eSum).hom ≫ TopCat.ofHom qU
  have hqU : IsQuotientMap qU :=
    (TopCat.isQuotientMap_sumElim_of_isPushout P.h).restrictPreimage_isOpen hU
  have hmQ : IsQuotientMap m.hom := by
    have h₁ := (TopCat.coprodHomeomorphSum P.obj₂ P.obj₃).isQuotientMap
    have h₂ := eSum.isQuotientMap
    exact hqU.comp (h₂.comp h₁)
  have hm : m = coprod.desc P.rU P.bU := by
    apply coprod.hom_ext
    · rw [coprod.inl_desc]
      apply TopCat.hom_ext
      ext x
      dsimp only [m]
      simp only [ConcreteCategory.comp_apply]
      have hc :
          (TopCat.coprodIsoSum P.obj₂ P.obj₃).hom
              ((coprod.inl : P.obj₂ ⟶ P.obj₂ ⨿ P.obj₃) x) =
            (Sum.inl x : Set.preimage P.r P.U ⊕ Set.preimage P.b P.U) :=
        TopCat.coprodHomeomorphSum_inl _ _ x
      rw [hc]
      rfl
    · rw [coprod.inr_desc]
      apply TopCat.hom_ext
      ext x
      dsimp only [m]
      simp only [ConcreteCategory.comp_apply]
      have hc :
          (TopCat.coprodIsoSum P.obj₂ P.obj₃).hom
              ((coprod.inr : P.obj₃ ⟶ P.obj₂ ⨿ P.obj₃) x) =
            (Sum.inr x : Set.preimage P.r P.U ⊕ Set.preimage P.b P.U) :=
        TopCat.coprodHomeomorphSum_inr _ _ x
      rw [hc]
      rfl
  rw [← hm]
  exact hmQ

private def rawQuotientMap (P : RestrictedPushout.{u}) :
    P.X₂ ⊕ P.X₃ → P.X₄ :=
  Sum.elim P.r P.b

private noncomputable def rawCoconeMap (P : RestrictedPushout.{u})
    (s : PushoutCocone P.tU P.lU) :
    Set.preimage P.rawQuotientMap P.U → s.pt
  | ⟨Sum.inl x, hx⟩ => s.inl ⟨x, hx⟩
  | ⟨Sum.inr x, hx⟩ => s.inr ⟨x, hx⟩

private theorem eqvGen_of_fiber (P : RestrictedPushout.{u})
    {x y : P.X₂ ⊕ P.X₃} (hxy : P.rawQuotientMap x = P.rawQuotientMap y) :
    Relation.EqvGen
      (Types.Pushout.Rel ((forget TopCat).map P.t) ((forget TopCat).map P.l)) x y := by
  let hType := P.h.map (forget TopCat)
  let e := hType.isColimit.coconePointUniqueUpToIso
    (Types.Pushout.isColimitCocone ((forget TopCat).map P.t)
      ((forget TopCat).map P.l))
  have he_inl (z : P.X₂) :
      e.hom (P.r z) =
        Types.Pushout.inl ((forget TopCat).map P.t) ((forget TopCat).map P.l) z := by
    have he := ConcreteCategory.congr_hom
      (IsColimit.comp_coconePointUniqueUpToIso_hom hType.isColimit
        (Types.Pushout.isColimitCocone ((forget TopCat).map P.t)
          ((forget TopCat).map P.l)) WalkingSpan.left) z
    change e.hom (P.r z) =
      Types.Pushout.inl ((forget TopCat).map P.t) ((forget TopCat).map P.l) z at he
    exact he
  have he_inr (z : P.X₃) :
      e.hom (P.b z) =
        Types.Pushout.inr ((forget TopCat).map P.t) ((forget TopCat).map P.l) z := by
    have he := ConcreteCategory.congr_hom
      (IsColimit.comp_coconePointUniqueUpToIso_hom hType.isColimit
        (Types.Pushout.isColimitCocone ((forget TopCat).map P.t)
          ((forget TopCat).map P.l)) WalkingSpan.right) z
    change e.hom (P.b z) =
      Types.Pushout.inr ((forget TopCat).map P.t) ((forget TopCat).map P.l) z at he
    exact he
  apply Quot.eqvGen_exact
  have hc (z : P.X₂ ⊕ P.X₃) :
      (Quot.mk _ z : Types.Pushout ((forget TopCat).map P.t)
        ((forget TopCat).map P.l)) = e.hom (P.rawQuotientMap z) := by
    cases z with
    | inl z => exact (he_inl z).symm
    | inr z => exact (he_inr z).symm
  exact (hc x).trans ((congrArg e.hom.hom hxy).trans (hc y).symm)

private theorem rawQuotientMap_eq_of_eqvGen (P : RestrictedPushout.{u})
    {x y : P.X₂ ⊕ P.X₃}
    (hxy : Relation.EqvGen
      (Types.Pushout.Rel ((forget TopCat).map P.t) ((forget TopCat).map P.l)) x y) :
    P.rawQuotientMap x = P.rawQuotientMap y := by
  induction hxy with
  | rel x y hrel =>
      rcases hrel with ⟨z⟩
      exact ConcreteCategory.congr_hom P.h.w z
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem rawCoconeMap_eq_of_eqvGen (P : RestrictedPushout.{u})
    (s : PushoutCocone P.tU P.lU) {x y : P.X₂ ⊕ P.X₃}
    (hxy : Relation.EqvGen
      (Types.Pushout.Rel ((forget TopCat).map P.t) ((forget TopCat).map P.l)) x y)
    (hx : P.rawQuotientMap x ∈ P.U) (hy : P.rawQuotientMap y ∈ P.U) :
    P.rawCoconeMap s ⟨x, hx⟩ = P.rawCoconeMap s ⟨y, hy⟩ := by
  induction hxy with
  | rel x y hrel =>
      rcases hrel with ⟨z⟩
      have hz₁ : (P.t ≫ P.r) z ∈ P.U := by
        exact hx
      let zU : P.obj₁ := ⟨z, hz₁⟩
      have hc := ConcreteCategory.congr_hom s.condition zU
      have ht : P.tU zU = (⟨P.t z, hx⟩ : P.obj₂) := by
        apply Subtype.ext
        rfl
      have hl : P.lU zU = (⟨P.l z, hy⟩ : P.obj₃) := by
        apply Subtype.ext
        rfl
      change s.inl ⟨P.t z, hx⟩ = s.inr ⟨P.l z, hy⟩
      simpa only [ConcreteCategory.comp_apply, ht, hl] using hc
  | refl => rfl
  | symm x y hxy ih => exact (ih hy hx).symm
  | trans x y z hxy hyz ih₁ ih₂ =>
      have hy' : P.rawQuotientMap y ∈ P.U := by
        rw [← P.rawQuotientMap_eq_of_eqvGen hxy]
        exact hx
      exact (ih₁ hx hy').trans (ih₂ hy' hy)

private theorem coprod_cases (X Y : TopCat.{u}) (z : ↑(X ⨿ Y)) :
    (∃ x : X, z = (coprod.inl : X ⟶ X ⨿ Y) x) ∨
      ∃ y : Y, z = (coprod.inr : Y ⟶ X ⨿ Y) y := by
  let e := TopCat.coprodHomeomorphSum X Y
  cases hz : e z with
  | inl x =>
      left
      refine ⟨x, e.injective ?_⟩
      rw [hz, TopCat.coprodHomeomorphSum_inl]
  | inr y =>
      right
      refine ⟨y, e.injective ?_⟩
      rw [hz, TopCat.coprodHomeomorphSum_inr]

private theorem restrictedCocone_factors (P : RestrictedPushout.{u})
    (s : PushoutCocone P.tU P.lU) :
    Function.FactorsThrough (coprod.desc s.inl s.inr)
      (coprod.desc P.rU P.bU) := by
  let eCop := TopCat.coprodHomeomorphSum P.obj₂ P.obj₃
  let eSum := preimageSumHomeomorph P.r.hom P.b.hom P.U
  let pre : ↑(P.obj₂ ⨿ P.obj₃) → Set.preimage P.rawQuotientMap P.U :=
    fun z => eSum (eCop z)
  have hq (z : ↑(P.obj₂ ⨿ P.obj₃)) :
      P.U.restrictPreimage P.rawQuotientMap (pre z) =
        (coprod.desc P.rU P.bU) z := by
    obtain ⟨x, rfl⟩ | ⟨x, rfl⟩ := coprod_cases P.obj₂ P.obj₃ z
    · dsimp only [pre]
      rw [TopCat.coprodHomeomorphSum_inl]
      rw [← ConcreteCategory.comp_apply, coprod.inl_desc]
      rfl
    · dsimp only [pre]
      rw [TopCat.coprodHomeomorphSum_inr]
      rw [← ConcreteCategory.comp_apply, coprod.inr_desc]
      rfl
  have hs (z : ↑(P.obj₂ ⨿ P.obj₃)) :
      P.rawCoconeMap s (pre z) = (coprod.desc s.inl s.inr) z := by
    obtain ⟨x, rfl⟩ | ⟨x, rfl⟩ := coprod_cases P.obj₂ P.obj₃ z
    · dsimp only [pre]
      rw [TopCat.coprodHomeomorphSum_inl]
      rw [← ConcreteCategory.comp_apply, coprod.inl_desc]
      rfl
    · dsimp only [pre]
      rw [TopCat.coprodHomeomorphSum_inr]
      rw [← ConcreteCategory.comp_apply, coprod.inr_desc]
      rfl
  intro x y hxy
  rw [← hs, ← hs]
  apply P.rawCoconeMap_eq_of_eqvGen s
  · apply P.eqvGen_of_fiber
    have hsub : P.U.restrictPreimage P.rawQuotientMap (pre x) =
        P.U.restrictPreimage P.rawQuotientMap (pre y) := by
      rw [hq, hq]
      exact hxy
    exact congrArg Subtype.val hsub

/--
If the chosen apex subset is open, the square on its four preimage subspaces
is a topological pushout.
-/
theorem isPushout (P : RestrictedPushout.{u}) (hU : IsOpen P.U) :
    IsPushout P.tU P.lU P.rU P.bU := by
  let c : PushoutCocone P.tU P.lU := PushoutCocone.mk P.rU P.bU P.w
  have hc := TopCat.pushoutCoconeIsColimitOfIsQuotientMap c
    (restrictedCoproduct_isQuotientMap P hU)
    (fun s => restrictedCocone_factors P s)
  have hs := IsPushout.of_isColimit hc
  change IsPushout P.tU P.lU P.rU P.bU at hs
  exact hs

end RestrictedPushout

end TopCat
