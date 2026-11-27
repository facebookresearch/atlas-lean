/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.QuotientHomotopy

/-!
# Quotient descriptions of topological pushouts

The canonical map from the binary coproduct of the two legs of a topological
pushout to its apex is a quotient map. Conversely, a pushout cocone is colimiting
when its coproduct map is quotient and every competing cocone map is constant
on its fibers.

The binary coproduct identifies with the topological disjoint sum. Homotopies
on the two summands assemble on that sum, and homotopies agreeing throughout
the common source descend to the pushout with the specified endpoint maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat Topology

universe u

namespace TopCat

/--
For a topological span, the map from the binary coproduct of its two target
objects to their pushout is a quotient map.
-/
theorem pushoutCoproductMap_isQuotientMap
    {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : X ⟶ Z) :
    IsQuotientMap (coprod.desc (pushout.inl f g) (pushout.inr f g)) := by
  let q : Y ⨿ Z ⟶ pushout f g :=
    coprod.desc (pushout.inl f g) (pushout.inr f g)
  let c := pushout.cocone f g
  have hleft : (coprod.inl : Y ⟶ Y ⨿ Z) ≫ q = pushout.inl f g :=
    coprod.inl_desc _ _
  have hright : (coprod.inr : Z ⟶ Y ⨿ Z) ≫ q = pushout.inr f g :=
    coprod.inr_desc _ _
  have hzero : c.ι.app WalkingSpan.zero = f ≫ pushout.inl f g := by
    exact (c.ι.naturality WalkingSpan.Hom.fst).symm
  refine ⟨?_, ?_⟩
  · apply IsCoinducing.of_isOpen_preimage_iff_isOpen
    intro s
    constructor
    · intro hs
      have hsleft : IsOpen ((pushout.inl f g).hom ⁻¹' s) := by
        rw [← hleft]
        exact hs.preimage (coprod.inl : Y ⟶ Y ⨿ Z).hom.continuous
      have hsright : IsOpen ((pushout.inr f g).hom ⁻¹' s) := by
        rw [← hright]
        exact hs.preimage (coprod.inr : Z ⟶ Y ⨿ Z).hom.continuous
      rw [isOpen_iff_of_isColimit c (pushout.isColimit f g)]
      intro j
      cases j with
      | none =>
        rw [hzero]
        exact hsleft.preimage f.hom.continuous
      | some j =>
        cases j with
        | left => exact hsleft
        | right => exact hsright
    · intro hs
      exact hs.preimage q.hom.continuous
  · intro p
    let hc := isColimitOfPreserves (forget TopCat) (pushout.isColimit f g)
    obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit hc p
    cases j with
    | none =>
      change X at x
      change c.ι.app WalkingSpan.zero x = p at hx
      rw [hzero] at hx
      refine ⟨(coprod.inl : Y ⟶ Y ⨿ Z) (f x), ?_⟩
      change q.hom ((coprod.inl : Y ⟶ Y ⨿ Z).hom (f.hom x)) = p
      rw [← ConcreteCategory.comp_apply, hleft]
      exact hx
    | some j =>
      cases j with
      | left =>
        change Y at x
        change (pushout.inl f g).hom x = p at hx
        refine ⟨(coprod.inl : Y ⟶ Y ⨿ Z) x, ?_⟩
        change q.hom ((coprod.inl : Y ⟶ Y ⨿ Z).hom x) = p
        rw [← ConcreteCategory.comp_apply, hleft]
        exact hx
      | right =>
        change Z at x
        change (pushout.inr f g).hom x = p at hx
        refine ⟨(coprod.inr : Z ⟶ Y ⨿ Z) x, ?_⟩
        change q.hom ((coprod.inr : Z ⟶ Y ⨿ Z).hom x) = p
        rw [← ConcreteCategory.comp_apply, hright]
        exact hx

/--
A pushout cocone is colimiting if its coproduct map is quotient and every
competing cocone map factors through that map on underlying functions.
-/
noncomputable def pushoutCoconeIsColimitOfIsQuotientMap
    {X Y Z : TopCat.{u}} {f : X ⟶ Y} {g : X ⟶ Z}
    (t : PushoutCocone f g)
    (hq : IsQuotientMap (coprod.desc t.inl t.inr))
    (hFactors : ∀ (s : PushoutCocone f g),
      Function.FactorsThrough (coprod.desc s.inl s.inr) (coprod.desc t.inl t.inr)) :
    IsColimit t := by
  let q := coprod.desc t.inl t.inr
  haveI hEpi : Epi q := (epi_iff_surjective q).mpr hq.surjective
  apply PushoutCocone.isColimitAux' t
  intro s
  let q_s := coprod.desc s.inl s.inr
  let lC : C(t.pt, s.pt) := hq.lift q_s.hom (hFactors s)
  have hLiftComp : lC.comp q.hom = q_s.hom := hq.lift_comp _ _
  let l : t.pt ⟶ s.pt := ofHom lC
  have hComp : q ≫ l = q_s := by
    apply hom_ext
    exact hLiftComp
  have h_inl : t.inl ≫ l = s.inl := by
    calc t.inl ≫ l = coprod.inl ≫ q ≫ l := (coprod.inl_desc_assoc t.inl t.inr l).symm
      _ = coprod.inl ≫ q_s := by rw [hComp]
      _ = s.inl := coprod.inl_desc s.inl s.inr
  have h_inr : t.inr ≫ l = s.inr := by
    calc t.inr ≫ l = coprod.inr ≫ q ≫ l := (coprod.inr_desc_assoc t.inl t.inr l).symm
      _ = coprod.inr ≫ q_s := by rw [hComp]
      _ = s.inr := coprod.inr_desc s.inl s.inr
  refine ⟨l, h_inl, h_inr, ?_⟩
  intro m hm_inl hm_inr
  have hqm : q ≫ m = q_s := by
    apply coprod.hom_ext
    · calc coprod.inl ≫ (q ≫ m) = t.inl ≫ m := coprod.inl_desc_assoc t.inl t.inr m
        _ = s.inl := hm_inl
        _ = coprod.inl ≫ q_s := (coprod.inl_desc s.inl s.inr).symm
    · calc coprod.inr ≫ (q ≫ m) = t.inr ≫ m := coprod.inr_desc_assoc t.inl t.inr m
        _ = s.inr := hm_inr
        _ = coprod.inr ≫ q_s := (coprod.inr_desc s.inl s.inr).symm
  have heq : q ≫ m = q ≫ l := by rw [hqm, hComp]
  exact (cancel_epi q).mp heq

/--
The topological-category isomorphism between the binary coproduct and the
corresponding disjoint sum of its underlying spaces.
-/
noncomputable def coprodIsoSum (X Y : TopCat.{u}) :
    X ⨿ Y ≅ TopCat.of (X ⊕ Y) :=
  (coprodIsCoprod X Y).coconePointUniqueUpToIso
    (TopCat.binaryCofanIsColimit X Y)

/--
The homeomorphism from a categorical binary coproduct to its topological
disjoint-sum model.
-/
noncomputable def coprodHomeomorphSum (X Y : TopCat.{u}) :
    (↑(X ⨿ Y) : Type u) ≃ₜ ↑(TopCat.of (X ⊕ Y)) :=
  TopCat.homeoOfIso (coprodIsoSum X Y)

/--
The coproduct homeomorphism sends a point from the left inclusion to its
left-tagged disjoint-sum point.
-/
@[simp]
theorem coprodHomeomorphSum_inl (X Y : TopCat.{u}) (x : X) :
    coprodHomeomorphSum X Y ((coprod.inl : X ⟶ X ⨿ Y) x) =
      (Sum.inl x : X ⊕ Y) := by
  have h_comm : (coprod.inl : X ⟶ X ⨿ Y) ≫ (coprodIsoSum X Y).hom =
      (TopCat.binaryCofan X Y).inl :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (coprodIsCoprod X Y) (TopCat.binaryCofanIsColimit X Y)
      (Discrete.mk WalkingPair.left)
  exact ConcreteCategory.congr_hom h_comm x

/--
The coproduct homeomorphism sends a point from the right inclusion to its
right-tagged disjoint-sum point.
-/
@[simp]
theorem coprodHomeomorphSum_inr (X Y : TopCat.{u}) (y : Y) :
    coprodHomeomorphSum X Y ((coprod.inr : Y ⟶ X ⨿ Y) y) =
      (Sum.inr y : X ⊕ Y) := by
  have h_comm : (coprod.inr : Y ⟶ X ⨿ Y) ≫ (coprodIsoSum X Y).hom =
      (TopCat.binaryCofan X Y).inr :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (coprodIsCoprod X Y) (TopCat.binaryCofanIsColimit X Y)
      (Discrete.mk WalkingPair.right)
  exact ConcreteCategory.congr_hom h_comm y

namespace Homotopy

/--
Two homotopies from the separate coproduct objects into a common target
assemble to a homotopy between the corresponding coproduct maps.
-/
noncomputable def coprodDesc
    {Y Z W : TopCat.{u}} {y₀ y₁ : Y ⟶ W} {z₀ z₁ : Z ⟶ W}
    (HY : TopCat.Homotopy y₀ y₁) (HZ : TopCat.Homotopy z₀ z₁) :
    TopCat.Homotopy (coprod.desc y₀ z₀) (coprod.desc y₁ z₁) := by
  let e : (unitInterval × ↑(Y ⨿ Z)) ≃ₜ
      (unitInterval × Y) ⊕ (unitInterval × Z) :=
    ((Homeomorph.refl unitInterval).prodCongr (TopCat.coprodHomeomorphSum Y Z)).trans
      Homeomorph.prodSumDistrib
  have e_inl (t : unitInterval) (y : Y) :
      e (t, (coprod.inl : Y ⟶ Y ⨿ Z) y) = Sum.inl (t, y) := by
    change Homeomorph.prodSumDistrib
      (t, TopCat.coprodHomeomorphSum Y Z ((coprod.inl : Y ⟶ Y ⨿ Z) y)) =
        Sum.inl (t, y)
    rw [TopCat.coprodHomeomorphSum_inl]
    rfl
  have e_inr (t : unitInterval) (z : Z) :
      e (t, (coprod.inr : Z ⟶ Y ⨿ Z) z) = Sum.inr (t, z) := by
    change Homeomorph.prodSumDistrib
      (t, TopCat.coprodHomeomorphSum Y Z ((coprod.inr : Z ⟶ Y ⨿ Z) z)) =
        Sum.inr (t, z)
    rw [TopCat.coprodHomeomorphSum_inr]
    rfl
  let sumElimMap : C((unitInterval × Y) ⊕ (unitInterval × Z), W) :=
    { toFun := Sum.elim HY HZ
      continuous_toFun := Continuous.sumElim HY.continuous HZ.continuous }
  let raw : C(unitInterval × ↑(Y ⨿ Z), W) :=
    sumElimMap.comp ⟨e, e.continuous⟩
  let slice (t : unitInterval) : Y ⨿ Z ⟶ W :=
    TopCat.ofHom
      { toFun := fun p => raw (t, p)
        continuous_toFun := raw.continuous.comp
          (continuous_const.prodMk continuous_id) }
  refine
    { toFun := raw
      continuous_toFun := raw.continuous
      map_zero_left := ?_
      map_one_left := ?_ }
  · intro p
    have hs : slice 0 = coprod.desc y₀ z₀ := by
      apply coprod.hom_ext
      · apply TopCat.ext
        intro y
        rw [TopCat.comp_app]
        change raw (0, (coprod.inl : Y ⟶ Y ⨿ Z) y) =
          (coprod.desc y₀ z₀) ((coprod.inl : Y ⟶ Y ⨿ Z) y)
        rw [show raw (0, (coprod.inl : Y ⟶ Y ⨿ Z) y) = HY (0, y) by
          simp [raw, sumElimMap, e_inl]]
        rw [ContinuousMap.Homotopy.apply_zero]
        rw [← ConcreteCategory.comp_apply, coprod.inl_desc]
      · apply TopCat.ext
        intro z
        rw [TopCat.comp_app]
        change raw (0, (coprod.inr : Z ⟶ Y ⨿ Z) z) =
          (coprod.desc y₀ z₀) ((coprod.inr : Z ⟶ Y ⨿ Z) z)
        rw [show raw (0, (coprod.inr : Z ⟶ Y ⨿ Z) z) = HZ (0, z) by
          simp [raw, sumElimMap, e_inr]]
        rw [ContinuousMap.Homotopy.apply_zero]
        rw [← ConcreteCategory.comp_apply, coprod.inr_desc]
    exact ConcreteCategory.congr_hom hs p
  · intro p
    have hs : slice 1 = coprod.desc y₁ z₁ := by
      apply coprod.hom_ext
      · apply TopCat.ext
        intro y
        rw [TopCat.comp_app]
        change raw (1, (coprod.inl : Y ⟶ Y ⨿ Z) y) =
          (coprod.desc y₁ z₁) ((coprod.inl : Y ⟶ Y ⨿ Z) y)
        rw [show raw (1, (coprod.inl : Y ⟶ Y ⨿ Z) y) = HY (1, y) by
          simp [raw, sumElimMap, e_inl]]
        rw [ContinuousMap.Homotopy.apply_one]
        rw [← ConcreteCategory.comp_apply, coprod.inl_desc]
      · apply TopCat.ext
        intro z
        rw [TopCat.comp_app]
        change raw (1, (coprod.inr : Z ⟶ Y ⨿ Z) z) =
          (coprod.desc y₁ z₁) ((coprod.inr : Z ⟶ Y ⨿ Z) z)
        rw [show raw (1, (coprod.inr : Z ⟶ Y ⨿ Z) z) = HZ (1, z) by
          simp [raw, sumElimMap, e_inr]]
        rw [ContinuousMap.Homotopy.apply_one]
        rw [← ConcreteCategory.comp_apply, coprod.inr_desc]
    exact ConcreteCategory.congr_hom hs p

/--
On a point of the left summand, the assembled coproduct homotopy equals
the supplied left homotopy at the same interval parameter.
-/
@[simp]
theorem coprodDesc_apply_inl
    {Y Z W : TopCat.{u}} {y₀ y₁ : Y ⟶ W} {z₀ z₁ : Z ⟶ W}
    (HY : TopCat.Homotopy y₀ y₁) (HZ : TopCat.Homotopy z₀ z₁)
    (t : unitInterval) (y : Y) :
    coprodDesc HY HZ (t, (coprod.inl : Y ⟶ Y ⨿ Z) y) = HY (t, y) := by
  unfold coprodDesc
  change Sum.elim HY HZ
    (Homeomorph.prodSumDistrib
      (t, TopCat.coprodHomeomorphSum Y Z ((coprod.inl : Y ⟶ Y ⨿ Z) y))) = HY (t, y)
  rw [TopCat.coprodHomeomorphSum_inl]
  rfl

/--
On a point of the right summand, the assembled coproduct homotopy equals
the supplied right homotopy at the same interval parameter.
-/
@[simp]
theorem coprodDesc_apply_inr
    {Y Z W : TopCat.{u}} {y₀ y₁ : Y ⟶ W} {z₀ z₁ : Z ⟶ W}
    (HY : TopCat.Homotopy y₀ y₁) (HZ : TopCat.Homotopy z₀ z₁)
    (t : unitInterval) (z : Z) :
    coprodDesc HY HZ (t, (coprod.inr : Z ⟶ Y ⨿ Z) z) = HZ (t, z) := by
  unfold coprodDesc
  change Sum.elim HY HZ
    (Homeomorph.prodSumDistrib
      (t, TopCat.coprodHomeomorphSum Y Z ((coprod.inr : Z ⟶ Y ⨿ Z) z))) = HZ (t, z)
  rw [TopCat.coprodHomeomorphSum_inr]
  rfl

/--
Homotopies on the two span targets descend to the pushout when their endpoint
maps commute on the common source and the homotopies agree there at every
time and point.
-/
noncomputable def pushoutDesc
    {X Y Z W : TopCat.{u}} {f : X ⟶ Y} {g : X ⟶ Z}
    {y₀ y₁ : Y ⟶ W} {z₀ z₁ : Z ⟶ W}
    (HY : TopCat.Homotopy y₀ y₁) (HZ : TopCat.Homotopy z₀ z₁)
    (h₀ : f ≫ y₀ = g ≫ z₀) (h₁ : f ≫ y₁ = g ≫ z₁)
    (h : ∀ (t : unitInterval) (x : X), HY (t, f x) = HZ (t, g x)) :
    TopCat.Homotopy (pushout.desc y₀ z₀ h₀) (pushout.desc y₁ z₁ h₁) := by
  let q : Y ⨿ Z ⟶ pushout f g :=
    coprod.desc (pushout.inl f g) (pushout.inr f g)
  let H := coprodDesc HY HZ
  let y_t (t : unitInterval) : Y ⟶ W :=
    TopCat.ofHom
      { toFun := fun y => HY (t, y)
        continuous_toFun := HY.continuous.comp
          (continuous_const.prodMk continuous_id) }
  let z_t (t : unitInterval) : Z ⟶ W :=
    TopCat.ofHom
      { toFun := fun z => HZ (t, z)
        continuous_toFun := HZ.continuous.comp
          (continuous_const.prodMk continuous_id) }
  have h_t (t : unitInterval) : f ≫ y_t t = g ≫ z_t t := by
    apply TopCat.ext
    intro x
    exact h t x
  let d (t : unitInterval) : pushout f g ⟶ W :=
    pushout.desc (y_t t) (z_t t) (h_t t)
  have hqd (t : unitInterval) :
      q ≫ d t = TopCat.ofHom
        { toFun := fun p => H (t, p)
          continuous_toFun := H.continuous.comp
            (continuous_const.prodMk continuous_id) } := by
    apply coprod.hom_ext
    · rw [← Category.assoc, coprod.inl_desc, pushout.inl_desc]
      apply TopCat.ext
      intro y
      change HY (t, y) = H (t, (coprod.inl : Y ⟶ Y ⨿ Z) y)
      rw [coprodDesc_apply_inl]
    · rw [← Category.assoc, coprod.inr_desc, pushout.inr_desc]
      apply TopCat.ext
      intro z
      change HZ (t, z) = H (t, (coprod.inr : Z ⟶ Y ⨿ Z) z)
      rw [coprodDesc_apply_inr]
  have hq₀ : q ≫ pushout.desc y₀ z₀ h₀ = coprod.desc y₀ z₀ := by
    apply coprod.hom_ext
    · rw [← Category.assoc, coprod.inl_desc, pushout.inl_desc, coprod.inl_desc]
    · rw [← Category.assoc, coprod.inr_desc, pushout.inr_desc, coprod.inr_desc]
  have hq₁ : q ≫ pushout.desc y₁ z₁ h₁ = coprod.desc y₁ z₁ := by
    apply coprod.hom_ext
    · rw [← Category.assoc, coprod.inl_desc, pushout.inl_desc, coprod.inl_desc]
    · rw [← Category.assoc, coprod.inr_desc, pushout.inr_desc, coprod.inr_desc]
  refine TopCat.Homotopy.ofQuotientMap q
    (TopCat.pushoutCoproductMap_isQuotientMap f g) H.toContinuousMap ?_ ?_ ?_
  · intro p
    exact H.map_zero_left p |>.trans (ConcreteCategory.congr_hom hq₀ p).symm
  · intro p
    exact H.map_one_left p |>.trans (ConcreteCategory.congr_hom hq₁ p).symm
  · intro t a b hab
    have hab' := congrArg (d t).hom hab
    have ha := ConcreteCategory.congr_hom (hqd t) a
    have hb := ConcreteCategory.congr_hom (hqd t) b
    exact ha.symm.trans (hab'.trans hb)

set_option backward.isDefEq.respectTransparency false in
/--
On the left pushout inclusion, the descended homotopy is the supplied left
homotopy at the same interval parameter.
-/
@[simp]
theorem pushoutDesc_apply_inl
    {X Y Z W : TopCat.{u}} {f : X ⟶ Y} {g : X ⟶ Z}
    {y₀ y₁ : Y ⟶ W} {z₀ z₁ : Z ⟶ W}
    (HY : TopCat.Homotopy y₀ y₁) (HZ : TopCat.Homotopy z₀ z₁)
    (h₀ : f ≫ y₀ = g ≫ z₀) (h₁ : f ≫ y₁ = g ≫ z₁)
    (h : ∀ (t : unitInterval) (x : X), HY (t, f x) = HZ (t, g x))
    (t : unitInterval) (y : Y) :
    pushoutDesc HY HZ h₀ h₁ h (t, pushout.inl f g y) = HY (t, y) := by
  let q : Y ⨿ Z ⟶ pushout f g :=
    coprod.desc (pushout.inl f g) (pushout.inr f g)
  have hq : q ((coprod.inl : Y ⟶ Y ⨿ Z) y) = pushout.inl f g y := by
    change (coprod.inl ≫ q) y = pushout.inl f g y
    rw [coprod.inl_desc]
  rw [← hq]
  unfold pushoutDesc
  rw [TopCat.Homotopy.ofQuotientMap_apply]
  exact coprodDesc_apply_inl HY HZ t y

set_option backward.isDefEq.respectTransparency false in
/--
On the right pushout inclusion, the descended homotopy is the supplied right
homotopy at the same interval parameter.
-/
@[simp]
theorem pushoutDesc_apply_inr
    {X Y Z W : TopCat.{u}} {f : X ⟶ Y} {g : X ⟶ Z}
    {y₀ y₁ : Y ⟶ W} {z₀ z₁ : Z ⟶ W}
    (HY : TopCat.Homotopy y₀ y₁) (HZ : TopCat.Homotopy z₀ z₁)
    (h₀ : f ≫ y₀ = g ≫ z₀) (h₁ : f ≫ y₁ = g ≫ z₁)
    (h : ∀ (t : unitInterval) (x : X), HY (t, f x) = HZ (t, g x))
    (t : unitInterval) (z : Z) :
    pushoutDesc HY HZ h₀ h₁ h (t, pushout.inr f g z) = HZ (t, z) := by
  let q : Y ⨿ Z ⟶ pushout f g :=
    coprod.desc (pushout.inl f g) (pushout.inr f g)
  have hq : q ((coprod.inr : Z ⟶ Y ⨿ Z) z) = pushout.inr f g z := by
    change (coprod.inr ≫ q) z = pushout.inr f g z
    rw [coprod.inr_desc]
  rw [← hq]
  unfold pushoutDesc
  rw [TopCat.Homotopy.ofQuotientMap_apply]
  exact coprodDesc_apply_inr HY HZ t z

end Homotopy

end TopCat
