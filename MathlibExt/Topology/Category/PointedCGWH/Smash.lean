/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.Basic
public import MathlibExt.Topology.Category.CGWH.Products
public import MathlibExt.Topology.Category.CGWH.Colimits
public import MathlibExt.Topology.Category.CGWH.CartesianClosed
public import MathlibExt.CategoryTheory.Monoidal.Pointed.Smash

/-!
# Wedge and smash products of pointed CGWH spaces

The generic pointed wedge and smash factories specialize at the native CGWH
point.  The native wedge is a closed subspace of the selected product, and
the smash quotient identifies exactly the wedge to the basepoint.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory Topology

namespace PointedCGWH

/-- The wedge bifunctor on pointed CGWH spaces. -/
noncomputable abbrev wedge :
    PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} :=
  CategoryTheory.Pointed.wedge CGWH.point

private def pointElement : CGWH.point.{u, v} := by
  change PUnit.{v + 1}
  exact PUnit.unit

private theorem pointElement_ext (p q : CGWH.point.{u, v}) : p = q := by
  change PUnit.{v + 1} at p q
  cases p
  cases q
  rfl

private theorem rawPoint_ext
    (p q : CGWH.cgwhToTop.obj CGWH.point.{u, v}) : p = q := by
  change PUnit.{v + 1} at p q
  cases p
  cases q
  rfl

private theorem pointMap_isClosedEmbedding (X : PointedCGWH.{u, v}) :
    IsClosedEmbedding
      (ConcreteCategory.hom (CGWH.cgwhToTop.map X.hom)) := by
  change IsClosedEmbedding (ConcreteCategory.hom X.hom)
  let r : X.right ⟶ CGWH.point.{u, v} :=
    CGWH.point_isTerminal.from X.right
  have hleft : Function.LeftInverse
      (ConcreteCategory.hom r) (ConcreteCategory.hom X.hom) := by
    intro p
    exact ConcreteCategory.congr_hom
      (CGWH.point_isTerminal.hom_ext (X.hom ≫ r) (𝟙 _)) p
  have hemb : IsEmbedding (ConcreteCategory.hom X.hom) :=
    hleft.isEmbedding (ConcreteCategory.hom r).continuous
      (ConcreteCategory.hom X.hom).continuous
  refine ⟨hemb, ?_⟩
  rw [show Set.range (ConcreteCategory.hom X.hom) =
      {X.hom pointElement.{u, v}} by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      rw [Set.mem_singleton_iff]
      exact congrArg (fun q => X.hom q)
        (pointElement_ext.{u, v} p pointElement)
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      exact ⟨pointElement.{u, v}, hx.symm⟩]
  exact isClosed_singleton

private theorem nativeProduct_point_ext
    {X Y : CGWH.{u, v}} {p q : (X ⨯ Y : CGWH.{u, v})}
    (hfst : (Limits.prod.fst : X ⨯ Y ⟶ X) p =
      (Limits.prod.fst : X ⨯ Y ⟶ X) q)
    (hsnd : (Limits.prod.snd : X ⨯ Y ⟶ Y) p =
      (Limits.prod.snd : X ⨯ Y ⟶ Y) q) : p = q := by
  apply (CGWH.prodComparisonToTop_bijective X Y).1
  apply Prod.ext
  · have hp := ConcreteCategory.congr_hom
      (CGWH.prodComparisonToTop_fst X Y) p
    have hq := ConcreteCategory.congr_hom
      (CGWH.prodComparisonToTop_fst X Y) q
    exact hp.trans (hfst.trans hq.symm)
  · have hp := ConcreteCategory.congr_hom
      (CGWH.prodComparisonToTop_snd X Y) p
    have hq := ConcreteCategory.congr_hom
      (CGWH.prodComparisonToTop_snd X Y) q
    exact hp.trans (hsnd.trans hq.symm)

private theorem leftAxis_isClosedEmbedding (X Y : PointedCGWH.{u, v}) :
    IsClosedEmbedding (ConcreteCategory.hom
      (CGWH.cgwhToTop.map
        (CartesianMonoidalCategory.lift (𝟙 X.right)
          (CGWH.point_isTerminal.from X.right ≫ Y.hom)))) := by
  change IsClosedEmbedding (ConcreteCategory.hom
    (CartesianMonoidalCategory.lift (𝟙 X.right)
      (CGWH.point_isTerminal.from X.right ≫ Y.hom)))
  let a : X.right ⟶ X.right ⨯ Y.right :=
    CartesianMonoidalCategory.lift (𝟙 X.right)
      (CGWH.point_isTerminal.from X.right ≫ Y.hom)
  have hleft : Function.LeftInverse
      (ConcreteCategory.hom (Limits.prod.fst : X.right ⨯ Y.right ⟶ X.right))
      (ConcreteCategory.hom a) := by
    intro x
    exact ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.lift_fst (𝟙 X.right)
        (CGWH.point_isTerminal.from X.right ≫ Y.hom)) x
  have hemb : IsEmbedding (ConcreteCategory.hom a) :=
    hleft.isEmbedding
      (ConcreteCategory.hom (Limits.prod.fst : X.right ⨯ Y.right ⟶ X.right)).continuous
      (ConcreteCategory.hom a).continuous
  refine ⟨hemb, ?_⟩
  change IsClosed (Set.range (ConcreteCategory.hom a))
  rw [show Set.range (ConcreteCategory.hom a) =
      (ConcreteCategory.hom (Limits.prod.snd : X.right ⨯ Y.right ⟶ Y.right)) ⁻¹'
        {Y.hom pointElement.{u, v}} by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      change (Limits.prod.snd : X.right ⨯ Y.right ⟶ Y.right) (a x) = _
      have h := ConcreteCategory.congr_hom
        (CartesianMonoidalCategory.lift_snd (𝟙 X.right)
          (CGWH.point_isTerminal.from X.right ≫ Y.hom)) x
      exact h.trans (congrArg (fun q => Y.hom q)
        (pointElement_ext.{u, v} _ pointElement))
    · intro hz
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hz
      refine ⟨(Limits.prod.fst : X.right ⨯ Y.right ⟶ X.right) z, ?_⟩
      apply nativeProduct_point_ext
      · exact ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.lift_fst (𝟙 X.right)
            (CGWH.point_isTerminal.from X.right ≫ Y.hom)) _
      · have h := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.lift_snd (𝟙 X.right)
            (CGWH.point_isTerminal.from X.right ≫ Y.hom))
          ((Limits.prod.fst : X.right ⨯ Y.right ⟶ X.right) z)
        exact h.trans ((congrArg (fun q => Y.hom q)
          (pointElement_ext.{u, v} _ pointElement)).trans hz.symm)]
  exact isClosed_singleton.preimage
    (ConcreteCategory.hom
      (Limits.prod.snd : X.right ⨯ Y.right ⟶ Y.right)).continuous

private theorem rightAxis_isClosedEmbedding (X Y : PointedCGWH.{u, v}) :
    IsClosedEmbedding (ConcreteCategory.hom
      (CGWH.cgwhToTop.map
        (CartesianMonoidalCategory.lift
          (CGWH.point_isTerminal.from Y.right ≫ X.hom) (𝟙 Y.right)))) := by
  change IsClosedEmbedding (ConcreteCategory.hom
    (CartesianMonoidalCategory.lift
      (CGWH.point_isTerminal.from Y.right ≫ X.hom) (𝟙 Y.right)))
  let a : Y.right ⟶ X.right ⨯ Y.right :=
    CartesianMonoidalCategory.lift
      (CGWH.point_isTerminal.from Y.right ≫ X.hom) (𝟙 Y.right)
  have hleft : Function.LeftInverse
      (ConcreteCategory.hom (Limits.prod.snd : X.right ⨯ Y.right ⟶ Y.right))
      (ConcreteCategory.hom a) := by
    intro y
    exact ConcreteCategory.congr_hom
      (CartesianMonoidalCategory.lift_snd
        (CGWH.point_isTerminal.from Y.right ≫ X.hom) (𝟙 Y.right)) y
  have hemb : IsEmbedding (ConcreteCategory.hom a) :=
    hleft.isEmbedding
      (ConcreteCategory.hom (Limits.prod.snd : X.right ⨯ Y.right ⟶ Y.right)).continuous
      (ConcreteCategory.hom a).continuous
  refine ⟨hemb, ?_⟩
  change IsClosed (Set.range (ConcreteCategory.hom a))
  rw [show Set.range (ConcreteCategory.hom a) =
      (ConcreteCategory.hom (Limits.prod.fst : X.right ⨯ Y.right ⟶ X.right)) ⁻¹'
        {X.hom pointElement.{u, v}} by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      change (Limits.prod.fst : X.right ⨯ Y.right ⟶ X.right) (a y) = _
      have h := ConcreteCategory.congr_hom
        (CartesianMonoidalCategory.lift_fst
          (CGWH.point_isTerminal.from Y.right ≫ X.hom) (𝟙 Y.right)) y
      exact h.trans (congrArg (fun q => X.hom q)
        (pointElement_ext.{u, v} _ pointElement))
    · intro hz
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hz
      refine ⟨(Limits.prod.snd : X.right ⨯ Y.right ⟶ Y.right) z, ?_⟩
      apply nativeProduct_point_ext
      · have h := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.lift_fst
            (CGWH.point_isTerminal.from Y.right ≫ X.hom) (𝟙 Y.right))
          ((Limits.prod.snd : X.right ⨯ Y.right ⟶ Y.right) z)
        exact h.trans ((congrArg (fun q => X.hom q)
          (pointElement_ext.{u, v} _ pointElement)).trans hz.symm)
      · exact ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.lift_snd
            (CGWH.point_isTerminal.from Y.right ≫ X.hom) (𝟙 Y.right)) _]
  exact isClosed_singleton.preimage
    (ConcreteCategory.hom
      (Limits.prod.fst : X.right ⨯ Y.right ⟶ X.right)).continuous

private noncomputable def nativeWedgeToProduct
    (X Y : PointedCGWH.{u, v}) :
    pushout X.hom Y.hom ⟶ X.right ⊗ Y.right :=
  pushout.desc
    (CartesianMonoidalCategory.lift (𝟙 X.right)
      (CGWH.point_isTerminal.from X.right ≫ Y.hom))
    (CartesianMonoidalCategory.lift
      (CGWH.point_isTerminal.from Y.right ≫ X.hom) (𝟙 Y.right))
    (by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc]
        rw [CartesianMonoidalCategory.lift_fst,
          CartesianMonoidalCategory.lift_fst, Category.comp_id]
        rw [← Category.assoc,
          CGWH.point_isTerminal.hom_ext
            (Y.hom ≫ CGWH.point_isTerminal.from Y.right) (𝟙 _)]
        simp
      · simp only [Category.assoc]
        rw [CartesianMonoidalCategory.lift_snd,
          CartesianMonoidalCategory.lift_snd, Category.comp_id]
        rw [← Category.assoc,
          CGWH.point_isTerminal.hom_ext
            (X.hom ≫ CGWH.point_isTerminal.from X.right) (𝟙 _)]
        simp)

private noncomputable def rawWedgeToProduct
    (X Y : PointedCGWH.{u, v}) :
    pushout (CGWH.cgwhToTop.map X.hom) (CGWH.cgwhToTop.map Y.hom) ⟶
      CGWH.cgwhToTop.obj (X.right ⊗ Y.right) :=
  (CGWH.pushoutClosedComparisonIso X.hom Y.hom
      (pointMap_isClosedEmbedding X)).hom ≫
    CGWH.cgwhToTop.map (nativeWedgeToProduct X Y)

private theorem rawWedgeToProduct_inl (X Y : PointedCGWH.{u, v}) :
    pushout.inl (CGWH.cgwhToTop.map X.hom) (CGWH.cgwhToTop.map Y.hom) ≫
        rawWedgeToProduct X Y =
      CGWH.cgwhToTop.map
        (CartesianMonoidalCategory.lift (𝟙 X.right)
          (CGWH.point_isTerminal.from X.right ≫ Y.hom)) := by
  unfold rawWedgeToProduct
  rw [← Category.assoc,
    CGWH.pushoutClosedComparisonIso_hom_inl X.hom Y.hom]
  rw [← CGWH.cgwhToTop.map_comp]
  dsimp only [nativeWedgeToProduct]
  rw [pushout.inl_desc]

private theorem rawWedgeToProduct_inr (X Y : PointedCGWH.{u, v}) :
    pushout.inr (CGWH.cgwhToTop.map X.hom) (CGWH.cgwhToTop.map Y.hom) ≫
        rawWedgeToProduct X Y =
      CGWH.cgwhToTop.map
        (CartesianMonoidalCategory.lift
          (CGWH.point_isTerminal.from Y.right ≫ X.hom) (𝟙 Y.right)) := by
  unfold rawWedgeToProduct
  rw [← Category.assoc,
    CGWH.pushoutClosedComparisonIso_hom_inr X.hom Y.hom]
  rw [← CGWH.cgwhToTop.map_comp]
  dsimp only [nativeWedgeToProduct]
  rw [pushout.inr_desc]

private theorem rawWedgeToProduct_injective
    (X Y : PointedCGWH.{u, v}) :
    Function.Injective (ConcreteCategory.hom (rawWedgeToProduct X Y)) := by
  let iX := CGWH.cgwhToTop.map X.hom
  let iY := CGWH.cgwhToTop.map Y.hom
  let l : CGWH.cgwhToTop.obj X.right ⟶
      CGWH.cgwhToTop.obj (X.right ⊗ Y.right) :=
    CGWH.cgwhToTop.map
      (CartesianMonoidalCategory.lift (𝟙 X.right)
        (CGWH.point_isTerminal.from X.right ≫ Y.hom))
  let r : CGWH.cgwhToTop.obj Y.right ⟶
      CGWH.cgwhToTop.obj (X.right ⊗ Y.right) :=
    CGWH.cgwhToTop.map
      (CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from Y.right ≫ X.hom) (𝟙 Y.right))
  have hl : pushout.inl iX iY ≫ rawWedgeToProduct X Y = l :=
    rawWedgeToProduct_inl X Y
  have hr : pushout.inr iX iY ≫ rawWedgeToProduct X Y = r :=
    rawWedgeToProduct_inr X Y
  let sq : IsPushout iX iY (pushout.inl iX iY) (pushout.inr iX iY) :=
    IsPushout.of_hasPushout iX iY
  have sqType : IsPushout ((forget TopCat).map iX) ((forget TopCat).map iY)
      ((forget TopCat).map (pushout.inl iX iY))
      ((forget TopCat).map (pushout.inr iX iY)) :=
    sq.map (forget TopCat)
  intro z z' hzz
  rcases CategoryTheory.Limits.Types.eq_or_eq_of_isPushout sqType z with
    ⟨x, rfl⟩ | ⟨y, rfl⟩
  · rcases CategoryTheory.Limits.Types.eq_or_eq_of_isPushout sqType z' with
      ⟨x', rfl⟩ | ⟨y, rfl⟩
    · change X.right at x x'
      have haxes : l x = l x' := by
        exact (ConcreteCategory.congr_hom hl x).symm.trans
          (hzz.trans (ConcreteCategory.congr_hom hl x'))
      change (CartesianMonoidalCategory.lift (𝟙 X.right)
          (CGWH.point_isTerminal.from X.right ≫ Y.hom)) x =
        (CartesianMonoidalCategory.lift (𝟙 X.right)
          (CGWH.point_isTerminal.from X.right ≫ Y.hom)) x' at haxes
      have hfst := congrArg
        (ConcreteCategory.hom
          (CartesianMonoidalCategory.fst X.right Y.right)) haxes
      have hxx : x = x' := by
        simpa only [← ConcreteCategory.comp_apply,
          CartesianMonoidalCategory.lift_fst,
          ConcreteCategory.id_apply] using hfst
      subst x'
      rfl
    · change X.right at x
      change Y.right at y
      have haxes : l x = r y := by
        exact (ConcreteCategory.congr_hom hl x).symm.trans
          (hzz.trans (ConcreteCategory.congr_hom hr y))
      change (CartesianMonoidalCategory.lift (𝟙 X.right)
          (CGWH.point_isTerminal.from X.right ≫ Y.hom)) x =
        (CartesianMonoidalCategory.lift
          (CGWH.point_isTerminal.from Y.right ≫ X.hom) (𝟙 Y.right)) y at haxes
      have hfst := congrArg
        (ConcreteCategory.hom
          (CartesianMonoidalCategory.fst X.right Y.right)) haxes
      have hsnd := congrArg
        (ConcreteCategory.hom
          (CartesianMonoidalCategory.snd X.right Y.right)) haxes
      let s : CGWH.point.{u, v} := CGWH.point_isTerminal.from Y.right y
      have hx : x = X.hom s := by
        simpa only [s, ← ConcreteCategory.comp_apply,
          CartesianMonoidalCategory.lift_fst, ConcreteCategory.id_apply]
          using hfst
      have hy : Y.hom s = y := by
        have hbase : Y.hom (CGWH.point_isTerminal.from X.right x) = y := by
          simpa only [← ConcreteCategory.comp_apply,
            CartesianMonoidalCategory.lift_snd, ConcreteCategory.id_apply]
            using hsnd
        exact (congrArg (fun q => Y.hom q)
          (pointElement_ext.{u, v} _ s)).symm.trans hbase
      calc
        (ConcreteCategory.hom ((forget TopCat).map (pushout.inl iX iY))) x =
            (ConcreteCategory.hom ((forget TopCat).map (pushout.inl iX iY)))
              (X.hom s) := congrArg _ hx
        _ = (ConcreteCategory.hom ((forget TopCat).map (pushout.inr iX iY)))
              (Y.hom s) := ConcreteCategory.congr_hom pushout.condition s
        _ = (ConcreteCategory.hom ((forget TopCat).map (pushout.inr iX iY))) y :=
          congrArg _ hy
  · rcases CategoryTheory.Limits.Types.eq_or_eq_of_isPushout sqType z' with
      ⟨x, rfl⟩ | ⟨y', rfl⟩
    · change Y.right at y
      change X.right at x
      have haxes : r y = l x := by
        exact (ConcreteCategory.congr_hom hr y).symm.trans
          (hzz.trans (ConcreteCategory.congr_hom hl x))
      change (CartesianMonoidalCategory.lift
          (CGWH.point_isTerminal.from Y.right ≫ X.hom) (𝟙 Y.right)) y =
        (CartesianMonoidalCategory.lift (𝟙 X.right)
          (CGWH.point_isTerminal.from X.right ≫ Y.hom)) x at haxes
      have hfst := congrArg
        (ConcreteCategory.hom
          (CartesianMonoidalCategory.fst X.right Y.right)) haxes
      have hsnd := congrArg
        (ConcreteCategory.hom
          (CartesianMonoidalCategory.snd X.right Y.right)) haxes
      let s : CGWH.point.{u, v} := CGWH.point_isTerminal.from Y.right y
      have hx : X.hom s = x := by
        simpa only [s, ← ConcreteCategory.comp_apply,
          CartesianMonoidalCategory.lift_fst, ConcreteCategory.id_apply]
          using hfst
      have hy : y = Y.hom s := by
        have hbase : y = Y.hom (CGWH.point_isTerminal.from X.right x) := by
          simpa only [← ConcreteCategory.comp_apply,
            CartesianMonoidalCategory.lift_snd, ConcreteCategory.id_apply]
            using hsnd
        exact hbase.trans (congrArg (fun q => Y.hom q)
          (pointElement_ext.{u, v} _ s))
      calc
        (ConcreteCategory.hom ((forget TopCat).map (pushout.inr iX iY))) y =
            (ConcreteCategory.hom ((forget TopCat).map (pushout.inr iX iY)))
              (Y.hom s) := congrArg _ hy
        _ = (ConcreteCategory.hom ((forget TopCat).map (pushout.inl iX iY)))
              (X.hom s) := (ConcreteCategory.congr_hom pushout.condition s).symm
        _ = (ConcreteCategory.hom ((forget TopCat).map (pushout.inl iX iY))) x :=
          congrArg _ hx
    · change Y.right at y y'
      have haxes : r y = r y' := by
        exact (ConcreteCategory.congr_hom hr y).symm.trans
          (hzz.trans (ConcreteCategory.congr_hom hr y'))
      change (CartesianMonoidalCategory.lift
          (CGWH.point_isTerminal.from Y.right ≫ X.hom) (𝟙 Y.right)) y =
        (CartesianMonoidalCategory.lift
          (CGWH.point_isTerminal.from Y.right ≫ X.hom) (𝟙 Y.right)) y' at haxes
      have hsnd := congrArg
        (ConcreteCategory.hom
          (CartesianMonoidalCategory.snd X.right Y.right)) haxes
      have hyy : y = y' := by
        simpa only [← ConcreteCategory.comp_apply,
          CartesianMonoidalCategory.lift_snd,
          ConcreteCategory.id_apply] using hsnd
      subst y'
      rfl

private theorem rawWedgeToProduct_isClosedEmbedding
    (X Y : PointedCGWH.{u, v}) :
    IsClosedEmbedding
      (ConcreteCategory.hom (rawWedgeToProduct X Y)) := by
  let iX := CGWH.cgwhToTop.map X.hom
  let iY := CGWH.cgwhToTop.map Y.hom
  let inl := pushout.inl iX iY
  let inr := pushout.inr iX iY
  let l : CGWH.cgwhToTop.obj X.right ⟶
      CGWH.cgwhToTop.obj (X.right ⊗ Y.right) :=
    CGWH.cgwhToTop.map
      (CartesianMonoidalCategory.lift (𝟙 X.right)
        (CGWH.point_isTerminal.from X.right ≫ Y.hom))
  let r : CGWH.cgwhToTop.obj Y.right ⟶
      CGWH.cgwhToTop.obj (X.right ⊗ Y.right) :=
    CGWH.cgwhToTop.map
      (CartesianMonoidalCategory.lift
        (CGWH.point_isTerminal.from Y.right ≫ X.hom) (𝟙 Y.right))
  have hl : inl ≫ rawWedgeToProduct X Y = l :=
    rawWedgeToProduct_inl X Y
  have hr : inr ≫ rawWedgeToProduct X Y = r :=
    rawWedgeToProduct_inr X Y
  let sq : IsPushout iX iY inl inr := IsPushout.of_hasPushout iX iY
  have sqType : IsPushout ((forget TopCat).map iX) ((forget TopCat).map iY)
      ((forget TopCat).map inl) ((forget TopCat).map inr) :=
    sq.map (forget TopCat)
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap
    (ConcreteCategory.hom (rawWedgeToProduct X Y)).continuous
    (rawWedgeToProduct_injective X Y) ?_
  intro S hS
  have hpreL : IsClosed ((ConcreteCategory.hom inl) ⁻¹' S) :=
    hS.preimage (ConcreteCategory.hom inl).continuous
  have hpreR : IsClosed ((ConcreteCategory.hom inr) ⁻¹' S) :=
    hS.preimage (ConcreteCategory.hom inr).continuous
  rw [show (ConcreteCategory.hom (rawWedgeToProduct X Y)) '' S =
      (ConcreteCategory.hom l) '' ((ConcreteCategory.hom inl) ⁻¹' S) ∪
        (ConcreteCategory.hom r) '' ((ConcreteCategory.hom inr) ⁻¹' S) by
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      rcases CategoryTheory.Limits.Types.eq_or_eq_of_isPushout sqType q with
        ⟨x, hx⟩ | ⟨y, hy⟩
      · subst q
        left
        exact ⟨x, hq, (ConcreteCategory.congr_hom hl x).symm⟩
      · subst q
        right
        exact ⟨y, hq, (ConcreteCategory.congr_hom hr y).symm⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
      · refine ⟨inl x, hx, ?_⟩
        exact ConcreteCategory.congr_hom hl x
      · refine ⟨inr y, hy, ?_⟩
        exact ConcreteCategory.congr_hom hr y]
  exact (leftAxis_isClosedEmbedding X Y).isClosedMap _ hpreL |>.union
    ((rightAxis_isClosedEmbedding X Y).isClosedMap _ hpreR)

/-- The native wedge embeds as the closed union of the two basepoint axes in
the selected native product. -/
theorem wedgeToProduct_isClosedEmbedding
    (X Y : PointedCGWH.{u, v}) :
    IsClosedEmbedding (ConcreteCategory.hom
      (CategoryTheory.Pointed.smashPresentation
        CGWH.point CGWH.point_isTerminal X Y).1.right) := by
  change IsClosedEmbedding
    (ConcreteCategory.hom (nativeWedgeToProduct X Y))
  let e := CGWH.pushoutClosedComparisonIso X.hom Y.hom
    (pointMap_isClosedEmbedding X)
  have hcomp := (rawWedgeToProduct_isClosedEmbedding X Y).comp
    (TopCat.homeoOfIso e.symm).isClosedEmbedding
  change IsClosedEmbedding (ConcreteCategory.hom
    (e.inv ≫ rawWedgeToProduct X Y)) at hcomp
  have hmap : e.inv ≫ rawWedgeToProduct X Y =
      CGWH.cgwhToTop.map (nativeWedgeToProduct X Y) := by
    dsimp only [e, rawWedgeToProduct]
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [hmap] at hcomp
  exact hcomp

/-- The smash-product bifunctor on pointed CGWH spaces. -/
noncomputable abbrev smash :
    PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} := by
  letI : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  letI : SymmetricCategory CGWH.{u, v} := inferInstance
  exact CategoryTheory.Pointed.smash CGWH.point CGWH.point_isTerminal

private theorem pushout_inl_eq_inl_iff_of_constant
    {S X Y Q : Type v} {f : S ⟶ X} {g : S ⟶ Y}
    {i : X ⟶ Q} {j : Y ⟶ Q}
    (sq : IsPushout f g i j) (hf : Function.Injective f)
    (hg : ∀ a b, g a = g b) (x y : X) :
    i x = i y ↔ x = y ∨
      (x ∈ Set.range f ∧ y ∈ Set.range f) := by
  let _ : Mono f := (CategoryTheory.mono_iff_injective f).2 hf
  let d : PushoutCocone f g :=
    CategoryTheory.Limits.Types.Pushout.cocone f g
  let e : Q ≅ d.pt := sq.isColimit.coconePointUniqueUpToIso
    (CategoryTheory.Limits.Types.Pushout.isColimitCocone f g)
  have he : i ≫ e.hom = d.inl :=
    IsColimit.comp_coconePointUniqueUpToIso_hom sq.isColimit
      (CategoryTheory.Limits.Types.Pushout.isColimitCocone f g)
      WalkingSpan.left
  have he' : d.inl ≫ e.inv = i := by
    rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have htransport : i x = i y ↔
      CategoryTheory.Limits.Types.Pushout.inl f g x =
        CategoryTheory.Limits.Types.Pushout.inl f g y := by
    constructor
    · intro h
      have h' := congrArg (ConcreteCategory.hom e.hom) h
      have hx := ConcreteCategory.congr_hom he x
      have hy := ConcreteCategory.congr_hom he y
      change e.hom (i x) =
        CategoryTheory.Limits.Types.Pushout.inl f g x at hx
      change e.hom (i y) =
        CategoryTheory.Limits.Types.Pushout.inl f g y at hy
      exact hx.symm.trans (h'.trans hy)
    · intro h
      have h' := congrArg (ConcreteCategory.hom e.inv) h
      have hx := ConcreteCategory.congr_hom he' x
      have hy := ConcreteCategory.congr_hom he' y
      change e.inv (CategoryTheory.Limits.Types.Pushout.inl f g x) = i x at hx
      change e.inv (CategoryTheory.Limits.Types.Pushout.inl f g y) = i y at hy
      exact hx.symm.trans (h'.trans hy)
  rw [htransport]
  change (Quot.mk _ (Sum.inl x) :
      CategoryTheory.Limits.Types.Pushout f g) =
    Quot.mk _ (Sum.inl y) ↔ _
  rw [CategoryTheory.Limits.Types.Pushout.quot_mk_eq_iff]
  rw [CategoryTheory.Limits.Types.Pushout.inl_rel'_inl_iff]
  constructor
  · rintro (hxy | ⟨a, b, _, hxa, hyb⟩)
    · exact Or.inl hxy
    · exact Or.inr ⟨⟨a, hxa.symm⟩, ⟨b, hyb.symm⟩⟩
  · rintro (rfl | ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨a, b, hg a b, rfl, rfl⟩

/-- The native smash quotient identifies precisely equal product points or
two points lying in the wedge. -/
theorem smashQuotient_eq_iff (X Y : PointedCGWH.{u, v})
    (x y : (Under.mk
      (CartesianMonoidalCategory.lift X.hom Y.hom) :
        PointedCGWH.{u, v}).right) :
    (CategoryTheory.Pointed.smashPresentation
        CGWH.point CGWH.point_isTerminal X Y).2.1.inl x =
      (CategoryTheory.Pointed.smashPresentation
        CGWH.point CGWH.point_isTerminal X Y).2.1.inl y ↔
        x = y ∨
          (x ∈ Set.range (ConcreteCategory.hom
              ((forget TopCat).map (CGWH.cgwhToTop.map
                (CategoryTheory.Pointed.smashPresentation
                  CGWH.point CGWH.point_isTerminal X Y).1.right))) ∧
            y ∈ Set.range (ConcreteCategory.hom
              ((forget TopCat).map (CGWH.cgwhToTop.map
                (CategoryTheory.Pointed.smashPresentation
                  CGWH.point CGWH.point_isTerminal X Y).1.right)))) := by
  let p := CategoryTheory.Pointed.smashPresentation
    CGWH.point CGWH.point_isTerminal X Y
  let A : CGWH.{u, v} := (Under.mk
    (CartesianMonoidalCategory.lift X.hom Y.hom) :
      PointedCGWH.{u, v}).right
  let w := p.1.right
  let c := CGWH.point_isTerminal.from (((wedge).obj X).obj Y).right
  have hw : IsClosedEmbedding (ConcreteCategory.hom
      (CGWH.cgwhToTop.map w)) := by
    change IsClosedEmbedding (ConcreteCategory.hom w)
    exact wedgeToProduct_isClosedEmbedding X Y
  let e := CGWH.pushoutClosedComparisonIso w c hw
  let rawInl := pushout.inl (CGWH.cgwhToTop.map w)
    (CGWH.cgwhToTop.map c)
  have he : rawInl ≫ e.hom =
      CGWH.cgwhToTop.map p.2.1.inl := by
    exact CGWH.pushoutClosedComparisonIso_hom_inl w c hw
  let sq : IsPushout (CGWH.cgwhToTop.map w) (CGWH.cgwhToTop.map c)
      rawInl (pushout.inr (CGWH.cgwhToTop.map w)
        (CGWH.cgwhToTop.map c)) :=
    IsPushout.of_hasPushout _ _
  have hkernel (a b : A) : p.2.1.inl a = p.2.1.inl b ↔
      a = b ∨
        (a ∈ Set.range (ConcreteCategory.hom
            ((forget TopCat).map (CGWH.cgwhToTop.map w))) ∧
          b ∈ Set.range (ConcreteCategory.hom
            ((forget TopCat).map (CGWH.cgwhToTop.map w)))) := by
    have htransport : p.2.1.inl a = p.2.1.inl b ↔
        rawInl a = rawInl b := by
      constructor
      · intro h
        have ha := ConcreteCategory.congr_hom he a
        have hb := ConcreteCategory.congr_hom he b
        exact (TopCat.homeoOfIso e).injective
          (ha.trans (h.trans hb.symm))
      · intro h
        have h' := congrArg (ConcreteCategory.hom e.hom) h
        have ha := ConcreteCategory.congr_hom he a
        have hb := ConcreteCategory.congr_hom he b
        exact ha.symm.trans (h'.trans hb)
    rw [htransport]
    have hraw := pushout_inl_eq_inl_iff_of_constant
      (sq.map (forget TopCat)) hw.injective
      (fun z z' => rawPoint_ext.{u, v} _ _) a b
    change rawInl a = rawInl b ↔ _ at hraw
    convert hraw using 1
    all_goals rfl
  let q : A ⟶ p.2.1.pt := p.2.1.inl
  let B : CGWH.{u, v} := p.2.1.pt
  let A' := CGWH.cgwhToCompactlyGenerated.obj A
  let B' := CGWH.cgwhToCompactlyGenerated.obj B
  let q' : A' ⟶ B' := CGWH.cgwhToCompactlyGenerated.map q
  let R : Setoid A' := Setoid.ker (ConcreteCategory.hom q')
  have hclosed : CGWH.closedEquivalenceRelation
      A' R := by
    let q2 : A' ⊗ A' ⟶ B' ⊗ B' := q' ⊗ₘ q'
    let diagonal : Set ↥((CGWH.cgwhToCompactlyGenerated.obj B ⊗
        CGWH.cgwhToCompactlyGenerated.obj B).toTop) :=
      {z | (ConcreteCategory.hom (CartesianMonoidalCategory.fst
          (CGWH.cgwhToCompactlyGenerated.obj B)
          (CGWH.cgwhToCompactlyGenerated.obj B))) z =
        (ConcreteCategory.hom (CartesianMonoidalCategory.snd
          (CGWH.cgwhToCompactlyGenerated.obj B)
          (CGWH.cgwhToCompactlyGenerated.obj B))) z}
    have hdiag : IsClosed diagonal :=
      (CompactlyGenerated.uWeakHausdorffSpace_iff_isClosed_nativeDiagonal
        (CGWH.cgwhToCompactlyGenerated.obj B)).mp B.is_weakHausdorff
    unfold CGWH.closedEquivalenceRelation
    rw [show {z : ↥((CGWH.cgwhToCompactlyGenerated.obj A ⊗
          CGWH.cgwhToCompactlyGenerated.obj A).toTop) |
        R ((ConcreteCategory.hom (CartesianMonoidalCategory.fst
            (CGWH.cgwhToCompactlyGenerated.obj A)
            (CGWH.cgwhToCompactlyGenerated.obj A))) z)
          ((ConcreteCategory.hom (CartesianMonoidalCategory.snd
            (CGWH.cgwhToCompactlyGenerated.obj A)
            (CGWH.cgwhToCompactlyGenerated.obj A))) z)} =
        (ConcreteCategory.hom q2) ⁻¹' diagonal by
      ext z
      change q' (CartesianMonoidalCategory.fst A' A' z) =
          q' (CartesianMonoidalCategory.snd A' A' z) ↔
        CartesianMonoidalCategory.fst B' B' (q2 z) =
          CartesianMonoidalCategory.snd B' B' (q2 z)
      rw [show CartesianMonoidalCategory.fst B' B' (q2 z) =
          q' (CartesianMonoidalCategory.fst A' A' z) by
        exact ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.tensorHom_fst q' q') z]
      rw [show CartesianMonoidalCategory.snd B' B' (q2 z) =
          q' (CartesianMonoidalCategory.snd A' A' z) by
        exact ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.tensorHom_snd q' q') z]]
    exact hdiag.preimage
      (ConcreteCategory.hom q2).continuous
  let R0 : Setoid A := Setoid.ker (ConcreteCategory.hom q)
  have hclosed0 : CGWH.closedEquivalenceRelation
      (CGWH.cgwhToCompactlyGenerated.obj A) R0 := by
    change CGWH.closedEquivalenceRelation A' R
    exact hclosed
  have hpackage :
      (∀ a b : A, p.2.1.inl a = p.2.1.inl b ↔
        a = b ∨
          (a ∈ Set.range (ConcreteCategory.hom
              ((forget TopCat).map (CGWH.cgwhToTop.map w))) ∧
            b ∈ Set.range (ConcreteCategory.hom
              ((forget TopCat).map (CGWH.cgwhToTop.map w))))) ∧
        CGWH.closedEquivalenceRelation
          (CGWH.cgwhToCompactlyGenerated.obj A) R0 ∧
        UWeakHausdorffSpace.{u} (Quotient R0) ∧
        IsHomeomorph
          (ConcreteCategory.hom (CGWH.quotientComparisonFromTop A R0)) := by
    refine ⟨hkernel, hclosed0, ?_, ?_⟩
    · exact (CGWH.quotient_isWeakHausdorff_iff_isClosed
        (CGWH.cgwhToCompactlyGenerated.obj A) R0).2 hclosed0
    · exact (CGWH.quotientComparisonFromTop_isHomeomorph_iff A R0).2 hclosed0
  convert hpackage.1 x y using 1

/-- The smash unit, the freely based native point. -/
noncomputable abbrev sphereZero : PointedCGWH.{u, v} :=
  CategoryTheory.Pointed.smashUnit CGWH.point

/-- The imported generic smash factory specialized at the native CGWH point. -/
noncomputable instance instMonoidalCategory :
    MonoidalCategory PointedCGWH.{u, v} := by
  letI : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  letI : SymmetricCategory CGWH.{u, v} := inferInstance
  exact CategoryTheory.Pointed.smashMonoidalCategory
    CGWH.point CGWH.point_isTerminal

/-- The imported generic symmetric factory specialized at the native CGWH point. -/
noncomputable instance instSymmetricCategory :
    SymmetricCategory PointedCGWH.{u, v} := by
  letI : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  letI : SymmetricCategory CGWH.{u, v} := inferInstance
  exact CategoryTheory.Pointed.smashSymmetricCategory
    CGWH.point CGWH.point_isTerminal

end PointedCGWH
