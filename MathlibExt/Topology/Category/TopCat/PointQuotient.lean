/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.Topology.Category.PointedTopCat
public import MathlibExt.Topology.Category.TopCat.PushoutOpenComplement
public import MathlibExt.Topology.Category.TopCat.QuotientPushout

/-!
# Point quotients of arrows of topological spaces

This file constructs the pushout that collapses the source of an arbitrary
arrow of topological spaces to a distinguished point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopCat

/-- The quotient of the target of an arrow by collapsing its source to a point. -/
noncomputable abbrev pointQuotient (f : Arrow TopCat.{u}) : TopCat.{u} :=
  pushout f.hom (isTerminalPUnit.from f.left)

/-- The map of point quotients induced by a commutative square. -/
noncomputable def pointQuotientMap {f g : Arrow TopCat.{u}} (sq : f ⟶ g) :
    pointQuotient f ⟶ pointQuotient g :=
  pushout.map f.hom (isTerminalPUnit.from f.left)
    g.hom (isTerminalPUnit.from g.left)
    sq.right (𝟙 _) sq.left sq.w.symm (by simp)

@[reassoc (attr := simp)]
lemma pointQuotientMap_inl {f g : Arrow TopCat.{u}} (sq : f ⟶ g) :
    pushout.inl f.hom (isTerminalPUnit.from f.left) ≫ pointQuotientMap sq =
      sq.right ≫ pushout.inl g.hom (isTerminalPUnit.from g.left) := by
  exact pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma pointQuotientMap_inr {f g : Arrow TopCat.{u}} (sq : f ⟶ g) :
    pushout.inr f.hom (isTerminalPUnit.from f.left) ≫ pointQuotientMap sq =
      pushout.inr g.hom (isTerminalPUnit.from g.left) := by
  change _ = (𝟙 _) ≫ _
  exact pushout.inr_desc _ _ _

@[simp]
lemma pointQuotientMap_id (f : Arrow TopCat.{u}) :
    pointQuotientMap (𝟙 f) = 𝟙 (pointQuotient f) := by
  apply pushout.hom_ext
  · simp only [pointQuotientMap_inl, Category.comp_id]
    change 𝟙 f.right ≫ _ = _
    simp
  · simp only [pointQuotientMap_inr, Category.comp_id]

@[simp, reassoc]
lemma pointQuotientMap_comp {f g h : Arrow TopCat.{u}}
    (sq₁ : f ⟶ g) (sq₂ : g ⟶ h) :
    pointQuotientMap (sq₁ ≫ sq₂) =
      pointQuotientMap sq₁ ≫ pointQuotientMap sq₂ := by
  apply pushout.hom_ext
  · simp only [pointQuotientMap_inl, pointQuotientMap_inl_assoc]
    change (sq₁.right ≫ sq₂.right) ≫ _ = _
    simp
  · simp only [pointQuotientMap_inr, pointQuotientMap_inr_assoc]

/-- The distinguished point in the point quotient. -/
noncomputable def pointQuotientPoint (f : Arrow TopCat.{u}) :
    TopCat.of PUnit ⟶ pointQuotient f :=
  pushout.inr _ _

@[reassoc (attr := simp)]
lemma pointQuotientPoint_naturality {f g : Arrow TopCat.{u}} (sq : f ⟶ g) :
    pointQuotientPoint f ≫ pointQuotientMap sq = pointQuotientPoint g := by
  simp [pointQuotientPoint]

/-- The pointed point quotient, strictly functorial in arbitrary arrows. -/
noncomputable def pointQuotientFunctor : Arrow TopCat.{u} ⥤ PointedTopCat.{u} where
  obj f := Under.mk (pointQuotientPoint f)
  map sq := Under.homMk (pointQuotientMap sq) (pointQuotientPoint_naturality sq)
  map_id f := by ext; simp
  map_comp sq₁ sq₂ := by ext; simp

@[simp]
lemma pointQuotientFunctor_obj_right (f : Arrow TopCat.{u}) :
    (pointQuotientFunctor.obj f).right = pointQuotient f := rfl

@[simp]
lemma pointQuotientFunctor_obj_hom (f : Arrow TopCat.{u}) :
    (pointQuotientFunctor.obj f).hom = pointQuotientPoint f := rfl

@[simp]
lemma pointQuotientFunctor_map_right {f g : Arrow TopCat.{u}} (sq : f ⟶ g) :
    (pointQuotientFunctor.map sq).right = pointQuotientMap sq := rfl

/-- The projection from an arrow's target to its point quotient. -/
noncomputable def pointQuotientProjection :
    Arrow.rightFunc ⟶ pointQuotientFunctor ⋙ Under.forget (TopCat.of PUnit) where
  app f := pushout.inl f.hom (isTerminalPUnit.from f.left)
  naturality _ _ sq := (pointQuotientMap_inl sq).symm

@[simp]
lemma pointQuotientProjection_app (f : Arrow TopCat.{u}) :
    pointQuotientProjection.app f =
      pushout.inl f.hom (isTerminalPUnit.from f.left) := rfl

@[reassoc (attr := simp)]
lemma pointQuotient_condition (f : Arrow TopCat.{u}) :
    f.hom ≫ pointQuotientProjection.app f =
      isTerminalPUnit.from f.left ≫ pointQuotientPoint f := by
  exact pushout.condition

set_option backward.isDefEq.respectTransparency false in
/-- If the collapsed source is nonempty, the ambient projection onto the point
quotient is a quotient map. -/
theorem pointQuotientProjection_isQuotientMap
    (f : Arrow TopCat.{u}) [Nonempty f.left] :
    Topology.IsQuotientMap (pointQuotientProjection.app f).hom := by
  let x : f.left := Classical.choice inferInstance
  let q : f.right ⟶ pointQuotient f :=
    pushout.inl f.hom (isTerminalPUnit.from f.left)
  change Topology.IsQuotientMap q.hom
  let pointRepresentative : TopCat.of PUnit ⟶ f.right :=
    TopCat.const (f.hom x)
  let r : f.right ⨿ TopCat.of PUnit ⟶ f.right :=
    coprod.desc (𝟙 _) pointRepresentative
  have hpoint : pointRepresentative ≫ q =
      pointQuotientPoint f := by
    apply ConcreteCategory.hom_ext
    intro p
    cases p
    change (f.hom ≫ q) x =
      pointQuotientPoint f PUnit.unit
    dsimp only [q, pointQuotientPoint]
    rw [pushout.condition]
    rfl
  have hr : r ≫ q = coprod.desc q (pointQuotientPoint f) := by
    apply coprod.hom_ext
    · simp only [r, coprod.inl_desc_assoc, Category.id_comp, coprod.inl_desc]
    · simp only [r, coprod.inr_desc_assoc, hpoint, coprod.inr_desc]
  apply Topology.IsQuotientMap.of_comp
    r.hom.continuous q.hom.continuous
  change Topology.IsQuotientMap (r ≫ q).hom
  rw [hr]
  exact pushoutCoproductMap_isQuotientMap
    f.hom (isTerminalPUnit.from f.left)

set_option backward.isDefEq.respectTransparency false

lemma pointQuotientProjection_preimage_singleton
    (f : Arrow TopCat.{u}) :
    (pointQuotientProjection.app f).hom ⁻¹'
        {pointQuotientPoint f PUnit.unit} =
      Set.range f.hom := by
  ext x
  constructor
  · intro hx
    change (pointQuotientProjection.app f).hom x =
      pointQuotientPoint f PUnit.unit at hx
    by_contra hxrange
    let h :=
      (IsPushout.of_hasPushout f.hom
        (isTerminalPUnit.from f.left)).flip
    let hType := h.map (forget TopCat)
    have hne :=
      Types.pushoutCocone_inl_ne_inr_of_not_mem_range_of_isColimit
        hType.isColimit (z := PUnit.unit) (x := x) hxrange
    apply hne
    exact hx.symm
  · rintro ⟨a, rfl⟩
    change (f.hom ≫ pointQuotientProjection.app f) a =
      pointQuotientPoint f PUnit.unit
    rw [pointQuotient_condition]
    rfl

/-- Over any open subset avoiding the distinguished point, the point-quotient
projection is a homeomorphism. -/
theorem pointQuotientProjection_isHomeomorph_restrictPreimage
    (f : Arrow TopCat.{u}) {U : Set (pointQuotient f)} (hU : IsOpen U)
    (hpoint : pointQuotientPoint f PUnit.unit ∉ U) :
    IsHomeomorph (U.restrictPreimage (pointQuotientProjection.app f)) := by
  apply isHomeomorph_restrictPreimage_inr_of_isPushout
    (IsPushout.of_hasPushout f.hom (isTerminalPUnit.from f.left)).flip hU
  · ext p
    constructor
    · intro hp
      rcases p with ⟨⟩
      exact (hpoint hp).elim
    · intro hp
      exact hp.elim
  · intro x hxU hxrange
    have hxpoint :
        (pointQuotientProjection.app f).hom x =
          pointQuotientPoint f PUnit.unit := by
      have hxmem : x ∈
          (pointQuotientProjection.app f).hom ⁻¹'
            {pointQuotientPoint f PUnit.unit} := by
        rw [pointQuotientProjection_preimage_singleton]
        exact hxrange
      exact hxmem
    exact hpoint (hxpoint ▸ hxU)

/-- If the distinguished point is closed, the point-quotient projection is a
homeomorphism over its complement. -/
theorem pointQuotientProjection_isHomeomorph_compl_of_isClosed_point
    (f : Arrow TopCat.{u})
    (hpoint : IsClosed ({pointQuotientPoint f PUnit.unit} :
      Set (pointQuotient f))) :
    IsHomeomorph
      (({pointQuotientPoint f PUnit.unit} : Set (pointQuotient f))ᶜ
        |>.restrictPreimage (pointQuotientProjection.app f)) := by
  apply pointQuotientProjection_isHomeomorph_restrictPreimage f
    hpoint.isOpen_compl
  simp

/-- A closed collapsed range makes the distinguished point closed whenever the
source is nonempty. -/
theorem pointQuotientPoint_isClosed_of_isClosed_range
    (f : Arrow TopCat.{u}) [Nonempty f.left]
    (hf : IsClosed (Set.range f.hom)) :
    IsClosed ({pointQuotientPoint f PUnit.unit} : Set (pointQuotient f)) := by
  apply ((pointQuotientProjection_isQuotientMap f).isCoinducing.isClosed_preimage).mp
  change IsClosed
    ((pointQuotientProjection.app f).hom ⁻¹'
      {pointQuotientPoint f PUnit.unit})
  rw [pointQuotientProjection_preimage_singleton]
  exact hf

/-- For a nonempty arrow with closed range, the point-quotient projection is a
homeomorphism away from the distinguished point. -/
theorem pointQuotientProjection_isHomeomorph_compl_of_isClosed_range
    (f : Arrow TopCat.{u}) [Nonempty f.left]
    (hf : IsClosed (Set.range f.hom)) :
    IsHomeomorph
      (({pointQuotientPoint f PUnit.unit} : Set (pointQuotient f))ᶜ
        |>.restrictPreimage (pointQuotientProjection.app f)) :=
  pointQuotientProjection_isHomeomorph_compl_of_isClosed_point f
    (pointQuotientPoint_isClosed_of_isClosed_range f hf)

end TopCat
