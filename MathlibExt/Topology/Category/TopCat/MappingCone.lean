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
public import MathlibExt.Topology.Category.TopCat.QuotientPushout
public import MathlibExt.Topology.Category.TopCat.OrderedTwoSetCover
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Topological cones and mapping cones

This file gives strict functorial models of the topological cone and the
pointed mapping cone of an arbitrary map. It also records the canonical
nullhomotopy of the source map inside the mapping cone and its naturality.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace TopCat

/-- The topological cone on `X`, with the endpoint `1` collapsed. -/
noncomputable abbrev cone (X : TopCat.{u}) : TopCat.{u} :=
  pushout (TopCat.ι₁ : X ⟶ X ⊗ TopCat.I)
    (TopCat.isTerminalPUnit.from X)

/-- The map on cones induced by a continuous map. -/
noncomputable def coneMap {X Y : TopCat.{u}} (f : X ⟶ Y) : cone X ⟶ cone Y :=
  pushout.map (TopCat.ι₁ : X ⟶ X ⊗ TopCat.I)
    (TopCat.isTerminalPUnit.from X)
    (TopCat.ι₁ : Y ⟶ Y ⊗ TopCat.I)
    (TopCat.isTerminalPUnit.from Y)
    (f ▷ TopCat.I) (𝟙 _) f (by simp) (by simp)

@[reassoc (attr := simp)]
lemma coneMap_inl {X Y : TopCat.{u}} (f : X ⟶ Y) :
    pushout.inl (TopCat.ι₁ : X ⟶ X ⊗ TopCat.I)
        (TopCat.isTerminalPUnit.from X) ≫ coneMap f =
      (f ▷ TopCat.I) ≫
        pushout.inl (TopCat.ι₁ : Y ⟶ Y ⊗ TopCat.I)
          (TopCat.isTerminalPUnit.from Y) := by
  exact pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma coneMap_inr {X Y : TopCat.{u}} (f : X ⟶ Y) :
    pushout.inr (TopCat.ι₁ : X ⟶ X ⊗ TopCat.I)
        (TopCat.isTerminalPUnit.from X) ≫ coneMap f =
      pushout.inr (TopCat.ι₁ : Y ⟶ Y ⊗ TopCat.I)
        (TopCat.isTerminalPUnit.from Y) := by
  exact pushout.inr_desc _ _ _

@[simp]
lemma coneMap_id (X : TopCat.{u}) : coneMap (𝟙 X) = 𝟙 (cone X) := by
  apply pushout.hom_ext
  · simp
  · simp

@[simp, reassoc]
lemma coneMap_comp {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    coneMap (f ≫ g) = coneMap f ≫ coneMap g := by
  apply pushout.hom_ext
  · simp
  · simp

/-- The topological cone is strictly functorial. -/
noncomputable def coneFunctor : TopCat.{u} ⥤ TopCat.{u} where
  obj := cone
  map := coneMap
  map_id := coneMap_id
  map_comp := coneMap_comp

@[simp]
lemma coneFunctor_obj (X : TopCat.{u}) : coneFunctor.obj X = cone X := rfl

@[simp]
lemma coneFunctor_map {X Y : TopCat.{u}} (f : X ⟶ Y) :
    coneFunctor.map f = coneMap f := rfl

/-- Inclusion of the base into its cone. -/
noncomputable def coneBase (X : TopCat.{u}) : X ⟶ cone X :=
  TopCat.ι₀ ≫ pushout.inl _ _

@[reassoc (attr := simp)]
lemma coneBase_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) :
    coneBase X ≫ coneMap f = f ≫ coneBase Y := by
  simp [coneBase]

/-- The cone-base inclusions form a natural transformation. -/
noncomputable def coneBaseNatTrans :
    Functor.id TopCat.{u} ⟶ coneFunctor :=
  { app := coneBase
    naturality := fun _ _ f ↦ (coneBase_naturality f).symm }

@[simp]
lemma coneBaseNatTrans_app (X : TopCat.{u}) :
    coneBaseNatTrans.app X = coneBase X := rfl

/-- The inclusion of a space as the base of its topological cone is an embedding. -/
theorem coneBase_isEmbedding (X : TopCat.{u}) :
    Topology.IsEmbedding (coneBase X) := by
  classical
  have zero_ne_one_I : (0 : I.{u}) ≠ 1 := by
    intro h
    exact zero_ne_one (congrArg (fun t : I.{u} ↦ (I.homeomorph t : ℝ)) h)
  have isOpen_ne_one_I : IsOpen ({t : I.{u} | t ≠ 1}) := by
    have h : IsOpen ({t : unitInterval | t ≠ 1}) :=
      isClosed_singleton.isOpen_compl
    convert h.preimage I.homeomorph.continuous using 1
    ext t
    constructor
    · intro ht heq
      apply ht
      apply I.homeomorph.injective
      simpa using heq
    · intro ht heq
      apply ht
      simp [heq]
  refine ⟨⟨?inducing⟩, ?injective⟩
  · refine (coneBase X).hom.continuous.le_induced.antisymm ?_
    intro s hs
    let cylinderPredicate : X ⊗ I ⟶ TopCat.of (ULift.{u} Prop) :=
      TopCat.ofHom ⟨fun p ↦ ULift.up.{u, 0} (p.1 ∈ s ∧ p.2 ≠ 1),
        (show Continuous (ULift.up : Prop → ULift.{u, 0} Prop) from
          continuous_uliftUp).comp (continuous_Prop.mpr
          (hs.prod isOpen_ne_one_I))⟩
    let pointPredicate : TopCat.of PUnit ⟶ TopCat.of (ULift.{u} Prop) :=
      TopCat.ofHom ⟨fun _ ↦ ULift.up.{u, 0} False, continuous_const⟩
    have hcompat : ι₁ ≫ cylinderPredicate =
        isTerminalPUnit.from X ≫ pointPredicate := by
      apply ConcreteCategory.hom_ext
      intro x
      change ULift.up.{u, 0} (x ∈ s ∧ (1 : I) ≠ 1) = ULift.up.{u, 0} False
      simp
    let predicate : cone X ⟶ TopCat.of (ULift.{u} Prop) :=
      pushout.desc cylinderPredicate pointPredicate hcompat
    refine ⟨{x | (predicate x).down},
      continuous_Prop.mp ((show Continuous (ULift.down : ULift.{u, 0} Prop → Prop) from
        continuous_uliftDown).comp predicate.hom.continuous), ?_⟩
    ext x
    change (predicate ((pushout.inl ι₁ (isTerminalPUnit.from X)) (ι₀ x))).down ↔ x ∈ s
    rw [← ConcreteCategory.comp_apply, pushout.inl_desc]
    change (ULift.up.{u, 0} (x ∈ s ∧ (0 : I) ≠ 1)).down ↔ x ∈ s
    simp [zero_ne_one_I]
  · let _ : TopologicalSpace (Option X) := ⊤
    let cylinderLabel : X ⊗ I ⟶ TopCat.of (Option X) :=
      TopCat.ofHom ⟨fun p ↦ if p.2 = 1 then none else some p.1,
        continuous_of_indiscreteTopology⟩
    let pointLabel : TopCat.of PUnit ⟶ TopCat.of (Option X) :=
      TopCat.ofHom ⟨fun _ ↦ none, continuous_of_indiscreteTopology⟩
    have hcompat : ι₁ ≫ cylinderLabel =
        isTerminalPUnit.from X ≫ pointLabel := by
      apply ConcreteCategory.hom_ext
      intro x
      change (if (1 : I) = 1 then none else some x) = none
      simp
    let label : cone X ⟶ TopCat.of (Option X) :=
      pushout.desc cylinderLabel pointLabel hcompat
    intro x y hxy
    have hx : label (coneBase X x) = some x := by
      change label ((pushout.inl ι₁ (isTerminalPUnit.from X)) (ι₀ x)) = some x
      rw [← ConcreteCategory.comp_apply, pushout.inl_desc]
      change (if (0 : I) = 1 then none else some x) = some x
      simp [zero_ne_one_I]
    have hy : label (coneBase X y) = some y := by
      change label ((pushout.inl ι₁ (isTerminalPUnit.from X)) (ι₀ y)) = some y
      rw [← ConcreteCategory.comp_apply, pushout.inl_desc]
      change (if (0 : I) = 1 then none else some y) = some y
      simp [zero_ne_one_I]
    exact Option.some.inj (hx.symm.trans ((congrArg (fun z ↦ label z) hxy).trans hy))

/-- The apex of the topological cone. -/
noncomputable def conePoint (X : TopCat.{u}) : TopCat.of PUnit ⟶ cone X :=
  pushout.inr _ _

@[reassoc (attr := simp)]
lemma conePoint_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) :
    conePoint X ≫ coneMap f = conePoint Y := by
  simp [conePoint]

/-- If `X` is empty, every point of its cone is the cone point. -/
theorem cone_eq_conePoint_of_isEmpty (X : TopCat.{u}) [IsEmpty X]
    (z : cone X) : z = conePoint X PUnit.unit := by
  let f : X ⟶ X ⊗ TopCat.I := TopCat.ι₁
  let g : X ⟶ TopCat.of PUnit := TopCat.isTerminalPUnit.from X
  let q : (X ⊗ TopCat.I) ⨿ TopCat.of PUnit ⟶ cone X :=
    coprod.desc (pushout.inl f g) (pushout.inr f g)
  obtain ⟨p, hp⟩ := (pushoutCoproductMap_isQuotientMap f g).surjective z
  let hc := isColimitOfPreserves (forget TopCat)
    (coprodIsCoprod (X ⊗ TopCat.I) (TopCat.of PUnit))
  obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit hc p
  cases j with
  | mk j =>
    cases j with
    | left =>
      exact isEmptyElim x.1
    | right =>
      cases x with
      | unit =>
        change (coprod.inr : TopCat.of PUnit ⟶ (X ⊗ TopCat.I) ⨿ TopCat.of PUnit)
            PUnit.unit = p at hx
        rw [← hp, ← hx]
        change (coprod.inr ≫ q) PUnit.unit = conePoint X PUnit.unit
        rw [coprod.inr_desc]
        rfl

/-- The cylinder maps canonically to the cone. -/
noncomputable def coneCylinder (X : TopCat.{u}) : X ⊗ TopCat.I ⟶ cone X :=
  pushout.inl _ _

@[reassoc (attr := simp)]
lemma coneCylinder_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) :
    coneCylinder X ≫ coneMap f = (f ▷ TopCat.I) ≫ coneCylinder Y :=
  coneMap_inl f

@[reassoc (attr := simp)]
lemma ι₀_coneCylinder (X : TopCat.{u}) :
    TopCat.ι₀ ≫ coneCylinder X = coneBase X := rfl

@[reassoc (attr := simp)]
lemma ι₁_coneCylinder (X : TopCat.{u}) :
    TopCat.ι₁ ≫ coneCylinder X =
      TopCat.isTerminalPUnit.from X ≫ conePoint X :=
  pushout.condition

/-- A cylinder point at interval coordinate `1` is the cone point. -/
theorem coneCylinder_eq_conePoint_of_snd_eq_one (X : TopCat.{u})
    (p : ↑(X ⊗ TopCat.I)) (hp : p.2 = 1) :
    coneCylinder X p = conePoint X PUnit.unit := by
  change coneCylinder X (p.1, p.2) = _
  rw [hp]
  change (TopCat.ι₁ ≫ coneCylinder X) p.1 = _
  rw [ι₁_coneCylinder]
  rfl

/-- For a nonempty space, the cylinder presentation maps quotiently onto its cone. -/
theorem coneCylinder_isQuotientMap (X : TopCat.{u}) [Nonempty X] :
    Topology.IsQuotientMap (coneCylinder X).hom := by
  let x : X := Classical.choice inferInstance
  let apexRepresentative : TopCat.of PUnit ⟶ X ⊗ TopCat.I :=
    TopCat.const (x, (1 : TopCat.I))
  let r : (X ⊗ TopCat.I) ⨿ TopCat.of PUnit ⟶ X ⊗ TopCat.I :=
    coprod.desc (𝟙 _) apexRepresentative
  have hapex : apexRepresentative ≫ coneCylinder X = conePoint X := by
    apply ConcreteCategory.hom_ext
    intro p
    cases p
    change coneCylinder X (x, (1 : TopCat.I)) = conePoint X PUnit.unit
    change (TopCat.ι₁ ≫ coneCylinder X) x = _
    rw [ι₁_coneCylinder]
    rfl
  have hr : r ≫ coneCylinder X =
      coprod.desc (coneCylinder X) (conePoint X) := by
    apply coprod.hom_ext
    · simp only [r, coprod.inl_desc_assoc, Category.id_comp, coprod.inl_desc]
    · simp only [r, coprod.inr_desc_assoc, hapex, coprod.inr_desc]
  apply Topology.IsQuotientMap.of_comp
    r.hom.continuous (coneCylinder X).hom.continuous
  change Topology.IsQuotientMap (r ≫ coneCylinder X).hom
  rw [hr]
  exact pushoutCoproductMap_isQuotientMap
    (TopCat.ι₁ : X ⟶ X ⊗ TopCat.I) (isTerminalPUnit.from X)

/-- Radially contract a nonempty cone to its apex. -/
noncomputable def coneContractingHomotopy (X : TopCat.{u}) [Nonempty X] :
    TopCat.Homotopy (𝟙 (cone X))
      (isTerminalPUnit.from (cone X) ≫ conePoint X) := by
  let cylinderRadialMap (t : unitInterval) : X ⊗ TopCat.I ⟶ cone X :=
    TopCat.ofHom
      ⟨fun p => coneCylinder X
          (p.1, TopCat.I.homeomorph.symm
            (Set.Icc.convexComb (TopCat.I.homeomorph p.2) (1 : unitInterval) t)),
        by
          apply (coneCylinder X).hom.continuous.comp
          fun_prop⟩
  let radialMap (t : unitInterval) : cone X ⟶ cone X :=
    pushout.desc (cylinderRadialMap t) (conePoint X) (by
      apply ConcreteCategory.hom_ext
      intro x
      change coneCylinder X
          (x, TopCat.I.homeomorph.symm
            (Set.Icc.convexComb (TopCat.I.homeomorph (1 : TopCat.I.{u}))
              (1 : unitInterval) t)) =
        conePoint X PUnit.unit
      rw [TopCat.I.homeomorph_one, Set.Icc.convexComb_eq]
      change (TopCat.ι₁ ≫ coneCylinder X) x = _
      rw [ι₁_coneCylinder]
      rfl)
  have cylinder_radialMap (t : unitInterval) :
      coneCylinder X ≫ radialMap t = cylinderRadialMap t :=
    pushout.inl_desc _ _ _
  let raw : C(unitInterval × ↑(X ⊗ TopCat.I), cone X) :=
    { toFun := fun p => cylinderRadialMap p.1 p.2
      continuous_toFun := by
        change Continuous fun p : unitInterval × (X × TopCat.I) =>
          coneCylinder X
            (p.2.1, TopCat.I.homeomorph.symm
              (Set.Icc.convexComb (TopCat.I.homeomorph p.2.2)
                (1 : unitInterval) p.1))
        apply (coneCylinder X).hom.continuous.comp
        fun_prop }
  have hzero (p : ↑(X ⊗ TopCat.I)) :
      raw (0, p) = coneCylinder X p := by
    change coneCylinder X
        (p.1, TopCat.I.homeomorph.symm
          (Set.Icc.convexComb (TopCat.I.homeomorph p.2)
            (1 : unitInterval) 0)) =
      coneCylinder X p
    rw [Set.Icc.convexComb_zero]
    simp
    cases p
    rfl
  have hone (p : ↑(X ⊗ TopCat.I)) :
      raw (1, p) = conePoint X PUnit.unit := by
    change coneCylinder X
        (p.1, TopCat.I.homeomorph.symm
          (Set.Icc.convexComb (TopCat.I.homeomorph p.2)
            (1 : unitInterval) 1)) =
      conePoint X PUnit.unit
    rw [Set.Icc.convexComb_one]
    change (TopCat.ι₁ ≫ coneCylinder X) p.1 = _
    rw [ι₁_coneCylinder]
    rfl
  have hfactors (t : unitInterval) :
      Function.FactorsThrough (fun p => raw (t, p)) (coneCylinder X).hom := by
    intro a b hab
    have h := congrArg (radialMap t).hom hab
    change cylinderRadialMap t a = cylinderRadialMap t b
    have ha := ConcreteCategory.congr_hom (cylinder_radialMap t) a
    have hb := ConcreteCategory.congr_hom (cylinder_radialMap t) b
    exact ha.symm.trans (h.trans hb)
  exact TopCat.Homotopy.ofQuotientMap
    (coneCylinder X) (coneCylinder_isQuotientMap X) raw
    (by simpa using hzero) (by simpa using hone) hfactors

/-- Evaluation of the radial contraction on a cylinder representative. -/
private theorem coneContractingHomotopy_apply_coneCylinder
    (X : TopCat.{u}) [Nonempty X] (t : unitInterval)
    (p : ↑(X ⊗ TopCat.I)) :
    coneContractingHomotopy X (t, coneCylinder X p) =
      coneCylinder X
        (p.1, TopCat.I.homeomorph.symm
          (Set.Icc.convexComb (TopCat.I.homeomorph p.2)
            (1 : unitInterval) t)) := by
  unfold coneContractingHomotopy
  apply TopCat.Homotopy.ofQuotientMap_apply

/-- The radial contraction fixes the cone apex. -/
@[simp]
theorem coneContractingHomotopy_apply_conePoint
    (X : TopCat.{u}) [Nonempty X] (t : unitInterval) (p : PUnit) :
    coneContractingHomotopy X (t, conePoint X p) = conePoint X p := by
  cases p
  let x : X := Classical.choice inferInstance
  have hx : coneCylinder X (TopCat.ι₁ x) = conePoint X PUnit.unit := by
    change (TopCat.ι₁ ≫ coneCylinder X) x = _
    rw [ι₁_coneCylinder]
    rfl
  rw [← hx]
  change coneContractingHomotopy X (t, coneCylinder X (TopCat.ι₁ x)) =
    coneCylinder X (TopCat.ι₁ x)
  rw [coneContractingHomotopy_apply_coneCylinder]
  rw [TopCat.ι₁_apply]
  rw [TopCat.I.homeomorph_one, Set.Icc.convexComb_eq]
  rfl

private theorem coneContractingHomotopy_naturality
    {X Y : TopCat.{u}} [Nonempty X] [Nonempty Y] (f : X ⟶ Y)
    (t : unitInterval) (z : cone X) :
    coneMap f (coneContractingHomotopy X (t, z)) =
      coneContractingHomotopy Y (t, coneMap f z) := by
  obtain ⟨p, rfl⟩ := (coneCylinder_isQuotientMap X).surjective z
  rw [coneContractingHomotopy_apply_coneCylinder]
  have hcone (q : ↑(X ⊗ TopCat.I)) :
      coneMap f (coneCylinder X q) =
        coneCylinder Y ((f ▷ TopCat.I) q) := by
    change (coneCylinder X ≫ coneMap f) q =
      ((f ▷ TopCat.I) ≫ coneCylinder Y) q
    exact ConcreteCategory.congr_hom (coneCylinder_naturality f) q
  rw [hcone p, coneContractingHomotopy_apply_coneCylinder]
  exact hcone
    (p.1, TopCat.I.homeomorph.symm
      (Set.Icc.convexComb (TopCat.I.homeomorph p.2) (1 : unitInterval) t))

/-- The radial cone contraction is natural with respect to maps of nonempty spaces. -/
theorem coneContractingHomotopy_h_naturality
    {X Y : TopCat.{u}} [Nonempty X] [Nonempty Y] (f : X ⟶ Y) :
    (coneContractingHomotopy X).h ≫ coneMap f =
      (coneMap f ▷ TopCat.I) ≫ (coneContractingHomotopy Y).h := by
  apply ConcreteCategory.hom_ext
  intro p
  exact coneContractingHomotopy_naturality f
    (TopCat.I.homeomorph p.2) p.1

/-- Height on the cone: the cylinder coordinate, with the apex at one. -/
noncomputable def coneHeight (X : TopCat.{u}) : cone X ⟶ I :=
  pushout.desc (CartesianMonoidalCategory.snd X I) (TopCat.const 1) (by
    apply TopCat.hom_ext
    ext x
    rfl)

@[reassoc (attr := simp)]
lemma coneCylinder_coneHeight (X : TopCat.{u}) :
    coneCylinder X ≫ coneHeight X = CartesianMonoidalCategory.snd X I := by
  exact pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma conePoint_coneHeight (X : TopCat.{u}) :
    conePoint X ≫ coneHeight X = TopCat.const 1 := by
  exact pushout.inr_desc _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- In a nonempty cone, height one consists exactly of the cone point. -/
theorem coneHeight_eq_one_iff (X : TopCat.{u}) [Nonempty X]
    (z : cone X) :
    coneHeight X z = 1 ↔ z = conePoint X PUnit.unit := by
  constructor
  · intro hz
    obtain ⟨p, hp⟩ := (coneCylinder_isQuotientMap X).surjective z
    rw [← hp] at hz ⊢
    have ht : p.2 = 1 := by
      rw [← ConcreteCategory.comp_apply, coneCylinder_coneHeight X] at hz
      exact hz
    exact coneCylinder_eq_conePoint_of_snd_eq_one X p ht
  · intro hz
    subst hz
    exact ConcreteCategory.congr_hom (conePoint_coneHeight X) PUnit.unit

@[reassoc (attr := simp)]
lemma coneBase_coneHeight (X : TopCat.{u}) :
    coneBase X ≫ coneHeight X = TopCat.const 0 := by
  simp only [coneBase, coneHeight, Category.assoc,
    pushout.inl_desc, TopCat.ι₀_snd]

@[reassoc]
lemma coneMap_coneHeight {X Y : TopCat.{u}} (f : X ⟶ Y) :
    coneMap f ≫ coneHeight Y = coneHeight X := by
  apply pushout.hom_ext
  · rw [← Category.assoc, coneMap_inl]
    change (f ▷ I) ≫ (coneCylinder Y ≫ coneHeight Y) =
      coneCylinder X ≫ coneHeight X
    rw [coneCylinder_coneHeight, coneCylinder_coneHeight]
    rfl
  · rw [← Category.assoc, coneMap_inr]
    change conePoint Y ≫ coneHeight Y = conePoint X ≫ coneHeight X
    rw [conePoint_coneHeight, conePoint_coneHeight]

set_option backward.isDefEq.respectTransparency false in
/-- The radial cone contraction moves height by convex interpolation toward the apex. -/
theorem coneContractingHomotopy_coneHeight (X : TopCat.{u}) [Nonempty X]
    (t : unitInterval) (z : cone X) :
    coneHeight X (coneContractingHomotopy X (t, z)) =
      I.homeomorph.symm
        (Set.Icc.convexComb (I.homeomorph (coneHeight X z))
          (1 : unitInterval) t) := by
  obtain ⟨p, rfl⟩ := (coneCylinder_isQuotientMap X).surjective z
  unfold coneContractingHomotopy
  rw [TopCat.Homotopy.ofQuotientMap_apply]
  change coneHeight X
      (coneCylinder X
        (p.1, I.homeomorph.symm
          (Set.Icc.convexComb (I.homeomorph p.2) (1 : unitInterval) t))) =
    I.homeomorph.symm
      (Set.Icc.convexComb
        (I.homeomorph (coneHeight X (coneCylinder X p)))
        (1 : unitInterval) t)
  rw [← ConcreteCategory.comp_apply, coneCylinder_coneHeight]
  rw [← ConcreteCategory.comp_apply, coneCylinder_coneHeight]
  rfl

/-- Reparameterize the interval coordinate of a cone by a map fixing the apex. -/
noncomputable def coneReparam (X : TopCat.{u}) (φ : I.{u} ⟶ I)
    (hφ : φ 1 = 1) : cone X ⟶ cone X :=
  pushout.desc ((X ◁ φ) ≫ coneCylinder X) (conePoint X) (by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change coneCylinder X (x, φ 1) = conePoint X PUnit.unit
    rw [hφ]
    change (ι₁ ≫ coneCylinder X) x = _
    rw [ι₁_coneCylinder]
    rfl)

@[reassoc (attr := simp)]
lemma coneCylinder_coneReparam (X : TopCat.{u}) (φ : I.{u} ⟶ I)
    (hφ : φ 1 = 1) :
    coneCylinder X ≫ coneReparam X φ hφ = (X ◁ φ) ≫ coneCylinder X := by
  exact pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma conePoint_coneReparam (X : TopCat.{u}) (φ : I.{u} ⟶ I)
    (hφ : φ 1 = 1) :
    conePoint X ≫ coneReparam X φ hφ = conePoint X := by
  exact pushout.inr_desc _ _ _

@[reassoc]
lemma coneBase_coneReparam (X : TopCat.{u}) (φ : I.{u} ⟶ I)
    (hφ₀ : φ 0 = 0) (hφ₁ : φ 1 = 1) :
    coneBase X ≫ coneReparam X φ hφ₁ = coneBase X := by
  change (ι₀ ≫ coneCylinder X) ≫ coneReparam X φ hφ₁ = coneBase X
  rw [Category.assoc, coneCylinder_coneReparam]
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  change coneCylinder X (x, φ 0) = coneBase X x
  rw [hφ₀]
  change (ι₀ ≫ coneCylinder X) x = _
  rw [ι₀_coneCylinder]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma coneReparam_coneHeight (X : TopCat.{u}) (φ : I.{u} ⟶ I)
    (hφ : φ 1 = 1) :
    coneReparam X φ hφ ≫ coneHeight X = coneHeight X ≫ φ := by
  apply pushout.hom_ext
  · change (coneCylinder X ≫ coneReparam X φ hφ) ≫ coneHeight X =
      coneCylinder X ≫ coneHeight X ≫ φ
    rw [coneCylinder_coneReparam]
    rw [Category.assoc, coneCylinder_coneHeight]
    rw [← Category.assoc, coneCylinder_coneHeight]
    exact CartesianMonoidalCategory.whiskerLeft_snd X φ
  · change (conePoint X ≫ coneReparam X φ hφ) ≫ coneHeight X =
      conePoint X ≫ coneHeight X ≫ φ
    rw [conePoint_coneReparam]
    rw [conePoint_coneHeight]
    rw [← Category.assoc, conePoint_coneHeight]
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    cases x
    exact hφ.symm

@[reassoc]
lemma coneReparam_naturality {X Y : TopCat.{u}} (f : X ⟶ Y)
    (φ : I.{u} ⟶ I) (hφ : φ 1 = 1) :
    coneReparam X φ hφ ≫ coneMap f = coneMap f ≫ coneReparam Y φ hφ := by
  apply pushout.hom_ext
  · change (coneCylinder X ≫ coneReparam X φ hφ) ≫ coneMap f =
      coneCylinder X ≫ coneMap f ≫ coneReparam Y φ hφ
    calc
      (coneCylinder X ≫ coneReparam X φ hφ) ≫ coneMap f =
          ((X ◁ φ) ≫ coneCylinder X) ≫ coneMap f := by
            rw [coneCylinder_coneReparam]
      _ = (X ◁ φ) ≫ ((f ▷ I) ≫ coneCylinder Y) := by
            rw [Category.assoc, coneCylinder_naturality]
      _ = (f ▷ I) ≫ ((Y ◁ φ) ≫ coneCylinder Y) := by
            apply TopCat.hom_ext
            ext p
            rfl
      _ = (f ▷ I) ≫ (coneCylinder Y ≫ coneReparam Y φ hφ) := by
            rw [coneCylinder_coneReparam]
      _ = ((f ▷ I) ≫ coneCylinder Y) ≫ coneReparam Y φ hφ := by
            rw [Category.assoc]
      _ = (coneCylinder X ≫ coneMap f) ≫ coneReparam Y φ hφ := by
            rw [coneCylinder_naturality]
  · change (conePoint X ≫ coneReparam X φ hφ) ≫ coneMap f =
      conePoint X ≫ coneMap f ≫ coneReparam Y φ hφ
    calc
      (conePoint X ≫ coneReparam X φ hφ) ≫ coneMap f =
          conePoint X ≫ coneMap f := by rw [conePoint_coneReparam]
      _ = conePoint Y := conePoint_naturality f
      _ = conePoint Y ≫ coneReparam Y φ hφ :=
        (conePoint_coneReparam Y φ hφ).symm
      _ = (conePoint X ≫ coneMap f) ≫ coneReparam Y φ hφ := by
        rw [conePoint_naturality]

set_option backward.isDefEq.respectTransparency false in
/-- A homotopy of interval reparameterizations descends to a homotopy of cones. -/
noncomputable def coneReparamHomotopy (X : TopCat.{u}) [Nonempty X]
    {φ ψ : I.{u} ⟶ I} (K : TopCat.Homotopy φ ψ)
    (hφ : φ 1 = 1) (hψ : ψ 1 = 1)
    (hK : ∀ t : unitInterval, K (t, (1 : I)) = 1) :
    TopCat.Homotopy (coneReparam X φ hφ) (coneReparam X ψ hψ) := by
  let raw : C(unitInterval × ↑(X ⊗ I), cone X) :=
    { toFun := fun p => coneCylinder X (p.2.1, K (p.1, p.2.2))
      continuous_toFun := by
        change Continuous fun p : unitInterval × (X × I) =>
          coneCylinder X (p.2.1, K (p.1, p.2.2))
        apply (coneCylinder X).hom.continuous.comp
        fun_prop }
  refine TopCat.Homotopy.ofQuotientMap
    (coneCylinder X) (coneCylinder_isQuotientMap X) raw ?_ ?_ ?_
  · rintro ⟨x, s⟩
    let p : ↑(X ⊗ I) := (x, s)
    let p₀ : ↑(X ⊗ I) := (x, K (0, s))
    let pφ : ↑(X ⊗ I) := (x, φ s)
    have hp : p₀ = pφ := by
      apply Prod.ext
      · rfl
      · exact K.map_zero_left s
    change coneCylinder X p₀ = coneReparam X φ hφ (coneCylinder X p)
    rw [hp]
    exact (ConcreteCategory.congr_hom (coneCylinder_coneReparam X φ hφ) p).symm
  · rintro ⟨x, s⟩
    let p : ↑(X ⊗ I) := (x, s)
    let p₁ : ↑(X ⊗ I) := (x, K (1, s))
    let pψ : ↑(X ⊗ I) := (x, ψ s)
    have hp : p₁ = pψ := by
      apply Prod.ext
      · rfl
      · exact K.map_one_left s
    change coneCylinder X p₁ = coneReparam X ψ hψ (coneCylinder X p)
    rw [hp]
    exact (ConcreteCategory.congr_hom (coneCylinder_coneReparam X ψ hψ) p).symm
  · intro t p q hpq
    let κ : I.{u} ⟶ I :=
      TopCat.ofHom
        { toFun := fun s => K (t, s)
          continuous_toFun := K.continuous.comp (continuous_const.prodMk continuous_id) }
    have hκ : κ 1 = 1 := hK t
    have h := congrArg (coneReparam X κ hκ).hom hpq
    have hp := ConcreteCategory.congr_hom (coneCylinder_coneReparam X κ hκ) p
    have hq := ConcreteCategory.congr_hom (coneCylinder_coneReparam X κ hκ) q
    exact hp.symm.trans (h.trans hq)

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of the descended reparameterization homotopy on a cone-cylinder point. -/
theorem coneReparamHomotopy_apply_coneCylinder (X : TopCat.{u}) [Nonempty X]
    {φ ψ : I.{u} ⟶ I} (K : TopCat.Homotopy φ ψ)
    (hφ : φ 1 = 1) (hψ : ψ 1 = 1)
    (hK : ∀ t : unitInterval, K (t, (1 : I)) = 1)
    (t : unitInterval) (p : ↑(X ⊗ I)) :
    coneReparamHomotopy X K hφ hψ hK (t, coneCylinder X p) =
      coneCylinder X (p.1, K (t, p.2)) := by
  unfold coneReparamHomotopy
  apply TopCat.Homotopy.ofQuotientMap_apply

set_option backward.isDefEq.respectTransparency false in
/-- A cone reparameterization homotopy fixing `0` fixes the cone base. -/
theorem coneReparamHomotopy_apply_coneBase (X : TopCat.{u}) [Nonempty X]
    {φ ψ : I.{u} ⟶ I} (K : TopCat.Homotopy φ ψ)
    (hφ : φ 1 = 1) (hψ : ψ 1 = 1)
    (hK₀ : ∀ t : unitInterval, K (t, (0 : I)) = 0)
    (hK₁ : ∀ t : unitInterval, K (t, (1 : I)) = 1)
    (t : unitInterval) (x : X) :
    coneReparamHomotopy X K hφ hψ hK₁ (t, coneBase X x) = coneBase X x := by
  let p : ↑(X ⊗ I) := (x, (0 : I))
  change coneReparamHomotopy X K hφ hψ hK₁
      (t, coneCylinder X p) = coneBase X x
  rw [coneReparamHomotopy_apply_coneCylinder]
  change coneCylinder X (x, K (t, (0 : I))) = coneBase X x
  rw [hK₀]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A cone reparameterization homotopy fixes the cone apex. -/
theorem coneReparamHomotopy_apply_conePoint (X : TopCat.{u}) [Nonempty X]
    {φ ψ : I.{u} ⟶ I} (K : TopCat.Homotopy φ ψ)
    (hφ : φ 1 = 1) (hψ : ψ 1 = 1)
    (hK : ∀ t : unitInterval, K (t, (1 : I)) = 1)
    (t : unitInterval) (p : PUnit) :
    coneReparamHomotopy X K hφ hψ hK (t, conePoint X p) = conePoint X p := by
  cases p
  let x : X := Classical.choice inferInstance
  let q : ↑(X ⊗ I) := (x, (1 : I))
  have hx : coneCylinder X q = conePoint X PUnit.unit := by
    change (TopCat.ι₁ ≫ coneCylinder X) x = _
    rw [ι₁_coneCylinder]
    rfl
  rw [← hx, coneReparamHomotopy_apply_coneCylinder]
  change coneCylinder X (x, K (t, (1 : I))) = coneCylinder X q
  rw [hK]

/-- The underlying topological mapping cone of an arbitrary map. -/
noncomputable abbrev mappingCone (f : Arrow TopCat.{u}) : TopCat.{u} :=
  pushout f.hom (coneBase f.left)

/-- The map of mapping cones induced by a commutative square. -/
noncomputable def mappingConeMap {f g : Arrow TopCat.{u}} (sq : f ⟶ g) :
    mappingCone f ⟶ mappingCone g :=
  pushout.map f.hom (coneBase f.left)
    g.hom (coneBase g.left)
    sq.right (coneMap sq.left) sq.left sq.w.symm
    (coneBase_naturality sq.left)

@[reassoc (attr := simp)]
lemma mappingConeMap_inl {f g : Arrow TopCat.{u}} (sq : f ⟶ g) :
    pushout.inl f.hom (coneBase f.left) ≫ mappingConeMap sq =
      sq.right ≫ pushout.inl g.hom (coneBase g.left) := by
  exact pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma mappingConeMap_inr {f g : Arrow TopCat.{u}} (sq : f ⟶ g) :
    pushout.inr f.hom (coneBase f.left) ≫ mappingConeMap sq =
      coneMap sq.left ≫ pushout.inr g.hom (coneBase g.left) := by
  exact pushout.inr_desc _ _ _

@[simp]
lemma mappingConeMap_id (f : Arrow TopCat.{u}) :
    mappingConeMap (𝟙 f) = 𝟙 (mappingCone f) := by
  apply pushout.hom_ext
  · simp only [mappingConeMap_inl, Category.comp_id]
    change 𝟙 f.right ≫ _ = _
    simp
  · simp only [mappingConeMap_inr, Category.comp_id]
    change coneMap (𝟙 f.left) ≫ _ = _
    simp

@[simp, reassoc]
lemma mappingConeMap_comp {f g h : Arrow TopCat.{u}}
    (sq₁ : f ⟶ g) (sq₂ : g ⟶ h) :
    mappingConeMap (sq₁ ≫ sq₂) =
      mappingConeMap sq₁ ≫ mappingConeMap sq₂ := by
  apply pushout.hom_ext
  · simp only [mappingConeMap_inl, mappingConeMap_inl_assoc]
    change (sq₁.right ≫ sq₂.right) ≫ _ = _
    simp
  · simp only [mappingConeMap_inr, mappingConeMap_inr_assoc]
    change coneMap (sq₁.left ≫ sq₂.left) ≫ _ = _
    simp

/-- The apex gives an arbitrary mapping cone its canonical basepoint. -/
noncomputable def mappingConePoint (f : Arrow TopCat.{u}) :
    TopCat.of PUnit ⟶ mappingCone f :=
  conePoint f.left ≫ pushout.inr _ _

@[reassoc (attr := simp)]
lemma mappingConePoint_naturality {f g : Arrow TopCat.{u}} (sq : f ⟶ g) :
    mappingConePoint f ≫ mappingConeMap sq = mappingConePoint g := by
  simp [mappingConePoint]

/-- The cone cylinder inside an arbitrary mapping cone. -/
noncomputable def mappingConeCylinder (f : Arrow TopCat.{u}) :
    f.left ⊗ TopCat.I ⟶ mappingCone f :=
  coneCylinder f.left ≫ pushout.inr _ _

@[reassoc (attr := simp)]
lemma mappingConeCylinder_naturality {f g : Arrow TopCat.{u}} (sq : f ⟶ g) :
    mappingConeCylinder f ≫ mappingConeMap sq =
      (sq.left ▷ TopCat.I) ≫ mappingConeCylinder g := by
  simp [mappingConeCylinder]

@[reassoc (attr := simp)]
lemma ι₀_mappingConeCylinder (f : Arrow TopCat.{u}) :
    TopCat.ι₀ ≫ mappingConeCylinder f =
      f.hom ≫ pushout.inl f.hom (coneBase f.left) := by
  rw [mappingConeCylinder, ← Category.assoc, TopCat.ι₀_coneCylinder]
  exact pushout.condition.symm

@[reassoc (attr := simp)]
lemma ι₁_mappingConeCylinder (f : Arrow TopCat.{u}) :
    TopCat.ι₁ ≫ mappingConeCylinder f =
      TopCat.isTerminalPUnit.from f.left ≫ mappingConePoint f := by
  simp [mappingConeCylinder, mappingConePoint]

/-- The canonical nullhomotopy of the source map inside an arbitrary mapping cone. -/
noncomputable def mappingConeNullHomotopy (f : Arrow TopCat.{u}) :
    TopCat.Homotopy
      (f.hom ≫ pushout.inl f.hom (coneBase f.left))
      (TopCat.isTerminalPUnit.from f.left ≫ mappingConePoint f) where
  toFun p := mappingConeCylinder f (p.2, TopCat.I.homeomorph.symm p.1)
  continuous_toFun :=
    (mappingConeCylinder f).hom.continuous.comp
      (continuous_snd.prodMk (TopCat.I.homeomorph.symm.continuous.comp continuous_fst))
  map_zero_left x := by
    change (TopCat.ι₀ ≫ mappingConeCylinder f) x = _
    rw [ι₀_mappingConeCylinder]
  map_one_left x := by
    change (TopCat.ι₁ ≫ mappingConeCylinder f) x = _
    rw [ι₁_mappingConeCylinder]

@[simp]
lemma mappingConeNullHomotopy_h (f : Arrow TopCat.{u}) :
    (mappingConeNullHomotopy f).h = mappingConeCylinder f := by
  ext p
  change mappingConeCylinder f
      (p.1, TopCat.I.homeomorph.symm (TopCat.I.homeomorph p.2)) = _
  rw [TopCat.I.homeomorph.symm_apply_apply]
  cases p
  rfl

/-- The canonical nullhomotopy is strictly natural as a cylinder map. -/
theorem mappingConeNullHomotopy_h_naturality {f g : Arrow TopCat.{u}} (sq : f ⟶ g) :
    (mappingConeNullHomotopy f).h ≫ mappingConeMap sq =
      (sq.left ▷ TopCat.I) ≫ (mappingConeNullHomotopy g).h := by
  simpa only [mappingConeNullHomotopy_h] using mappingConeCylinder_naturality sq

/-- The pointed topological mapping cone, strictly functorial in arbitrary maps. -/
noncomputable def mappingConeFunctor : Arrow TopCat.{u} ⥤ PointedTopCat.{u} where
  obj f := Under.mk (mappingConePoint f)
  map sq := Under.homMk (mappingConeMap sq) (mappingConePoint_naturality sq)
  map_id f := by ext; simp
  map_comp sq₁ sq₂ := by ext; simp

@[simp]
lemma mappingConeFunctor_obj_right (f : Arrow TopCat.{u}) :
    (mappingConeFunctor.obj f).right = mappingCone f := rfl

@[simp]
lemma mappingConeFunctor_obj_hom (f : Arrow TopCat.{u}) :
    (mappingConeFunctor.obj f).hom = mappingConePoint f := rfl

@[simp]
lemma mappingConeFunctor_map_right {f g : Arrow TopCat.{u}} (sq : f ⟶ g) :
    (mappingConeFunctor.map sq).right = mappingConeMap sq := rfl

/-- Inclusion of the target into the underlying mapping cone. -/
noncomputable def mappingConeInclusion :
    Arrow.rightFunc ⟶ mappingConeFunctor ⋙ Under.forget (TopCat.of PUnit) where
  app f := pushout.inl f.hom (coneBase f.left)
  naturality _ _ sq := (mappingConeMap_inl sq).symm

@[simp]
lemma mappingConeInclusion_app (f : Arrow TopCat.{u}) :
    mappingConeInclusion.app f = pushout.inl f.hom (coneBase f.left) := rfl

/-- Height on an arbitrary mapping cone: zero on the target and cone height on the cone summand. -/
noncomputable def mappingConeHeight (f : Arrow TopCat.{u}) : mappingCone f ⟶ I :=
  pushout.desc (TopCat.const 0) (coneHeight f.left) (by
    rw [coneBase_coneHeight]
    apply TopCat.hom_ext
    ext x
    rfl)

@[reassoc (attr := simp)]
lemma mappingConeInclusion_mappingConeHeight (f : Arrow TopCat.{u}) :
    mappingConeInclusion.app f ≫ mappingConeHeight f = TopCat.const 0 := by
  exact pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma mappingConeCylinder_mappingConeHeight (f : Arrow TopCat.{u}) :
    mappingConeCylinder f ≫ mappingConeHeight f =
      CartesianMonoidalCategory.snd f.left TopCat.I := by
  simp only [mappingConeCylinder, mappingConeHeight, Category.assoc,
    pushout.inr_desc, coneCylinder_coneHeight]

@[reassoc (attr := simp)]
lemma mappingConePoint_mappingConeHeight (f : Arrow TopCat.{u}) :
    mappingConePoint f ≫ mappingConeHeight f = TopCat.const 1 := by
  simp only [mappingConePoint, mappingConeHeight, Category.assoc,
    pushout.inr_desc, conePoint_coneHeight]

@[reassoc]
lemma mappingConeMap_mappingConeHeight {f g : Arrow TopCat.{u}} (sq : f ⟶ g) :
    mappingConeMap sq ≫ mappingConeHeight g = mappingConeHeight f := by
  apply pushout.hom_ext
  · rw [← Category.assoc, mappingConeMap_inl]
    simp only [mappingConeHeight, Category.assoc, pushout.inl_desc]
    apply TopCat.hom_ext
    ext x
    rfl
  · rw [← Category.assoc, mappingConeMap_inr]
    simp only [mappingConeHeight, Category.assoc, pushout.inr_desc,
      coneMap_coneHeight]

/-- The lower open height neighborhood in an arbitrary mapping cone. -/
noncomputable def mappingConeLowerSet (f : Arrow TopCat.{u}) : Set (mappingCone f) :=
  {z | ((I.homeomorph (mappingConeHeight f z) : unitInterval) : ℝ) < 2 / 3}

/-- The upper open height neighborhood in an arbitrary mapping cone. -/
noncomputable def mappingConeUpperSet (f : Arrow TopCat.{u}) : Set (mappingCone f) :=
  {z | (1 : ℝ) / 3 < ((I.homeomorph (mappingConeHeight f z) : unitInterval) : ℝ)}

/-- The natural two-set height cover of an arbitrary mapping cone. -/
noncomputable def mappingConeHeightCoverFunctor :
    Arrow TopCat.{u} ⥤ AlgebraicTopology.OrderedTwoSetCover.{u} where
  obj f :=
    { X := mappingCone f
      left := mappingConeUpperSet f
      right := mappingConeLowerSet f
      interior_cover := by
        have hLower : IsOpen (mappingConeLowerSet f) :=
          isOpen_Iio.preimage
            (continuous_subtype_val.comp
              (I.homeomorph.continuous.comp (mappingConeHeight f).hom.continuous))
        have hUpper : IsOpen (mappingConeUpperSet f) :=
          isOpen_Ioi.preimage
            (continuous_subtype_val.comp
              (I.homeomorph.continuous.comp (mappingConeHeight f).hom.continuous))
        rw [hUpper.interior_eq, hLower.interior_eq]
        intro z _
        by_cases hz :
            ((I.homeomorph (mappingConeHeight f z) : unitInterval) : ℝ) < 2 / 3
        · exact Set.mem_union_right _ hz
        · exact Set.mem_union_left _
            (lt_of_lt_of_le (by norm_num) (le_of_not_gt hz)) }
  map sq :=
    { f := mappingConeMap sq
      left_maps := by
        intro z hz
        change (1 : ℝ) / 3 < ((I.homeomorph
          (mappingConeHeight _ (mappingConeMap sq z)) : unitInterval) : ℝ)
        have h := ConcreteCategory.congr_hom (mappingConeMap_mappingConeHeight sq) z
        change mappingConeHeight _ (mappingConeMap sq z) = mappingConeHeight _ z at h
        rw [h]
        exact hz
      right_maps := by
        intro z hz
        change ((I.homeomorph
          (mappingConeHeight _ (mappingConeMap sq z)) : unitInterval) : ℝ) < 2 / 3
        have h := ConcreteCategory.congr_hom (mappingConeMap_mappingConeHeight sq) z
        change mappingConeHeight _ (mappingConeMap sq z) = mappingConeHeight _ z at h
        rw [h]
        exact hz }
  map_id f := by
    apply AlgebraicTopology.OrderedTwoSetCover.Hom.ext
    exact mappingConeMap_id f
  map_comp sq₁ sq₂ := by
    apply AlgebraicTopology.OrderedTwoSetCover.Hom.ext
    exact mappingConeMap_comp sq₁ sq₂

/-- Reparameterize the cone coordinate inside a mapping cone by a map fixing both endpoints. -/
noncomputable def mappingConeReparam (f : Arrow TopCat.{u}) (φ : I.{u} ⟶ I)
    (hφ₀ : φ 0 = 0) (hφ₁ : φ 1 = 1) : mappingCone f ⟶ mappingCone f :=
  pushout.desc (mappingConeInclusion.app f)
    (coneReparam f.left φ hφ₁ ≫ pushout.inr f.hom (coneBase f.left)) (by
    change f.hom ≫ pushout.inl f.hom (coneBase f.left) =
      coneBase f.left ≫ coneReparam f.left φ hφ₁ ≫
        pushout.inr f.hom (coneBase f.left)
    rw [← Category.assoc, coneBase_coneReparam]
    · exact (pushout.condition :
        f.hom ≫ pushout.inl f.hom (coneBase f.left) =
          coneBase f.left ≫ pushout.inr f.hom (coneBase f.left))
    · exact hφ₀)

@[reassoc (attr := simp)]
lemma mappingConeInl_mappingConeReparam (f : Arrow TopCat.{u})
    (φ : I.{u} ⟶ I) (hφ₀ : φ 0 = 0) (hφ₁ : φ 1 = 1) :
    pushout.inl f.hom (coneBase f.left) ≫ mappingConeReparam f φ hφ₀ hφ₁ =
      pushout.inl f.hom (coneBase f.left) := by
  unfold mappingConeReparam
  exact pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
lemma mappingConeInr_mappingConeReparam (f : Arrow TopCat.{u})
    (φ : I.{u} ⟶ I) (hφ₀ : φ 0 = 0) (hφ₁ : φ 1 = 1) :
    pushout.inr f.hom (coneBase f.left) ≫ mappingConeReparam f φ hφ₀ hφ₁ =
      coneReparam f.left φ hφ₁ ≫ pushout.inr f.hom (coneBase f.left) := by
  unfold mappingConeReparam
  exact pushout.inr_desc _ _ _

@[reassoc (attr := simp)]
lemma mappingConeCylinder_mappingConeReparam (f : Arrow TopCat.{u})
    (φ : I.{u} ⟶ I) (hφ₀ : φ 0 = 0) (hφ₁ : φ 1 = 1) :
    mappingConeCylinder f ≫ mappingConeReparam f φ hφ₀ hφ₁ =
      (f.left ◁ φ) ≫ mappingConeCylinder f := by
  change coneCylinder f.left ≫
      (pushout.inr f.hom (coneBase f.left) ≫ mappingConeReparam f φ hφ₀ hφ₁) =
    ((f.left ◁ φ) ≫ coneCylinder f.left) ≫
      pushout.inr f.hom (coneBase f.left)
  rw [mappingConeInr_mappingConeReparam]
  rw [← Category.assoc, coneCylinder_coneReparam]

@[reassoc (attr := simp)]
lemma mappingConePoint_mappingConeReparam (f : Arrow TopCat.{u})
    (φ : I.{u} ⟶ I) (hφ₀ : φ 0 = 0) (hφ₁ : φ 1 = 1) :
    mappingConePoint f ≫ mappingConeReparam f φ hφ₀ hφ₁ = mappingConePoint f := by
  change conePoint f.left ≫
      (pushout.inr f.hom (coneBase f.left) ≫ mappingConeReparam f φ hφ₀ hφ₁) =
    conePoint f.left ≫ pushout.inr f.hom (coneBase f.left)
  rw [mappingConeInr_mappingConeReparam]
  rw [← Category.assoc, conePoint_coneReparam]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma mappingConeReparam_mappingConeHeight (f : Arrow TopCat.{u})
    (φ : I.{u} ⟶ I) (hφ₀ : φ 0 = 0) (hφ₁ : φ 1 = 1) :
    mappingConeReparam f φ hφ₀ hφ₁ ≫ mappingConeHeight f =
      mappingConeHeight f ≫ φ := by
  apply pushout.hom_ext
  · change (pushout.inl f.hom (coneBase f.left) ≫
        mappingConeReparam f φ hφ₀ hφ₁) ≫ mappingConeHeight f =
      pushout.inl f.hom (coneBase f.left) ≫ mappingConeHeight f ≫ φ
    rw [mappingConeInl_mappingConeReparam]
    unfold mappingConeHeight
    rw [pushout.inl_desc]
    rw [← Category.assoc, pushout.inl_desc]
    apply TopCat.hom_ext
    ext x
    simpa [TopCat.const] using
      congrArg (fun t : I => (I.homeomorph t : ℝ)) hφ₀.symm
  · change (pushout.inr f.hom (coneBase f.left) ≫
        mappingConeReparam f φ hφ₀ hφ₁) ≫ mappingConeHeight f =
      pushout.inr f.hom (coneBase f.left) ≫ mappingConeHeight f ≫ φ
    rw [mappingConeInr_mappingConeReparam]
    unfold mappingConeHeight
    rw [Category.assoc, pushout.inr_desc]
    rw [← Category.assoc, pushout.inr_desc]
    exact coneReparam_coneHeight f.left φ hφ₁

@[reassoc]
lemma mappingConeReparam_naturality {f g : Arrow TopCat.{u}} (sq : f ⟶ g)
    (φ : I.{u} ⟶ I) (hφ₀ : φ 0 = 0) (hφ₁ : φ 1 = 1) :
    mappingConeReparam f φ hφ₀ hφ₁ ≫ mappingConeMap sq =
      mappingConeMap sq ≫ mappingConeReparam g φ hφ₀ hφ₁ := by
  apply pushout.hom_ext
  · change (pushout.inl f.hom (coneBase f.left) ≫
        mappingConeReparam f φ hφ₀ hφ₁) ≫ mappingConeMap sq =
      pushout.inl f.hom (coneBase f.left) ≫ mappingConeMap sq ≫
        mappingConeReparam g φ hφ₀ hφ₁
    calc
      (pushout.inl f.hom (coneBase f.left) ≫ mappingConeReparam f φ hφ₀ hφ₁) ≫
          mappingConeMap sq =
        pushout.inl f.hom (coneBase f.left) ≫ mappingConeMap sq := by
          rw [mappingConeInl_mappingConeReparam]
      _ = sq.right ≫ pushout.inl g.hom (coneBase g.left) := mappingConeMap_inl sq
      _ = sq.right ≫
          (pushout.inl g.hom (coneBase g.left) ≫
            mappingConeReparam g φ hφ₀ hφ₁) := by
            rw [mappingConeInl_mappingConeReparam]
      _ = (pushout.inl f.hom (coneBase f.left) ≫ mappingConeMap sq) ≫
          mappingConeReparam g φ hφ₀ hφ₁ := by
            rw [← Category.assoc, mappingConeMap_inl]
  · change (pushout.inr f.hom (coneBase f.left) ≫
        mappingConeReparam f φ hφ₀ hφ₁) ≫ mappingConeMap sq =
      pushout.inr f.hom (coneBase f.left) ≫ mappingConeMap sq ≫
        mappingConeReparam g φ hφ₀ hφ₁
    calc
      (pushout.inr f.hom (coneBase f.left) ≫
          mappingConeReparam f φ hφ₀ hφ₁) ≫ mappingConeMap sq =
        (coneReparam f.left φ hφ₁ ≫
          pushout.inr f.hom (coneBase f.left)) ≫ mappingConeMap sq := by
            rw [mappingConeInr_mappingConeReparam]
      _ = coneReparam f.left φ hφ₁ ≫
          (coneMap sq.left ≫ pushout.inr g.hom (coneBase g.left)) := by
            rw [Category.assoc, mappingConeMap_inr]
      _ = (coneMap sq.left ≫ coneReparam g.left φ hφ₁) ≫
          pushout.inr g.hom (coneBase g.left) := by
            rw [← Category.assoc, coneReparam_naturality]
      _ = coneMap sq.left ≫
          (pushout.inr g.hom (coneBase g.left) ≫
            mappingConeReparam g φ hφ₀ hφ₁) := by
            rw [mappingConeInr_mappingConeReparam]
            exact Category.assoc _ _ _
      _ = (pushout.inr f.hom (coneBase f.left) ≫ mappingConeMap sq) ≫
          mappingConeReparam g φ hφ₀ hφ₁ := by
            rw [← Category.assoc, mappingConeMap_inr]

set_option backward.isDefEq.respectTransparency false in
/-- A homotopy of endpoint-preserving interval reparameterizations induces a homotopy
of arbitrary mapping-cone reparameterizations. -/
noncomputable def mappingConeReparamHomotopy (f : Arrow TopCat.{u}) [Nonempty f.left]
    {φ ψ : I.{u} ⟶ I} (K : TopCat.Homotopy φ ψ)
    (hφ₀ : φ 0 = 0) (hφ₁ : φ 1 = 1)
    (hψ₀ : ψ 0 = 0) (hψ₁ : ψ 1 = 1)
    (hK₀ : ∀ t : unitInterval, K (t, (0 : I)) = 0)
    (hK₁ : ∀ t : unitInterval, K (t, (1 : I)) = 1) :
    TopCat.Homotopy
      (mappingConeReparam f φ hφ₀ hφ₁)
      (mappingConeReparam f ψ hψ₀ hψ₁) := by
  let j : cone f.left ⟶ mappingCone f :=
    pushout.inr f.hom (coneBase f.left)
  let i : f.right ⟶ mappingCone f :=
    pushout.inl f.hom (coneBase f.left)
  let HY : TopCat.Homotopy i i :=
    TopCat.Homotopy.refl _
  let HC := coneReparamHomotopy f.left K hφ₁ hψ₁ hK₁
  let HZ : TopCat.Homotopy
      (coneReparam f.left φ hφ₁ ≫ j)
      (coneReparam f.left ψ hψ₁ ≫ j) :=
    (TopCat.Homotopy.refl j).comp HC
  have h₀ : f.hom ≫ i =
      coneBase f.left ≫ (coneReparam f.left φ hφ₁ ≫ j) := by
    rw [← Category.assoc, coneBase_coneReparam f.left φ hφ₀ hφ₁]
    exact pushout.condition
  have h₁ : f.hom ≫ i =
      coneBase f.left ≫ (coneReparam f.left ψ hψ₁ ≫ j) := by
    rw [← Category.assoc, coneBase_coneReparam f.left ψ hψ₀ hψ₁]
    exact pushout.condition
  have hcompat (t : unitInterval) (x : f.left) :
      HY (t, f.hom x) = HZ (t, coneBase f.left x) := by
    change i (f.hom x) =
      j (coneReparamHomotopy f.left K hφ₁ hψ₁ hK₁ (t, coneBase f.left x))
    rw [coneReparamHomotopy_apply_coneBase f.left K hφ₁ hψ₁ hK₀ hK₁]
    change (f.hom ≫ pushout.inl f.hom (coneBase f.left)) x =
      (coneBase f.left ≫ pushout.inr f.hom (coneBase f.left)) x
    exact ConcreteCategory.congr_hom pushout.condition x
  change TopCat.Homotopy
    (pushout.desc i (coneReparam f.left φ hφ₁ ≫ j) h₀)
    (pushout.desc i (coneReparam f.left ψ hψ₁ ≫ j) h₁)
  exact TopCat.Homotopy.pushoutDesc HY HZ h₀ h₁ hcompat

set_option backward.isDefEq.respectTransparency false in
/-- In a mapping cone with nonempty source, height one consists exactly of the apex. -/
theorem mappingConeHeight_eq_one_iff (f : Arrow TopCat.{u}) [Nonempty f.left]
    (z : mappingCone f) :
    mappingConeHeight f z = 1 ↔ z = mappingConePoint f PUnit.unit := by
  constructor
  · intro hz
    obtain hz' | hz' := Types.eq_or_eq_of_isPushout
      ((IsPushout.of_hasPushout f.hom (coneBase f.left)).map (forget TopCat)) z
    · obtain ⟨y, rfl⟩ := hz'
      change (pushout.inl f.hom (coneBase f.left) ≫ mappingConeHeight f) y = 1 at hz
      rw [mappingConeHeight, pushout.inl_desc] at hz
      have h : (0 : I.{u}) = 1 := hz
      exact (zero_ne_one
        (congrArg (fun t : I.{u} ↦ (I.homeomorph t : ℝ)) h)).elim
    · obtain ⟨c, rfl⟩ := hz'
      have hc : coneHeight f.left c = 1 := by
        change (pushout.inr f.hom (coneBase f.left) ≫ mappingConeHeight f) c = 1 at hz
        rw [mappingConeHeight, pushout.inr_desc] at hz
        exact hz
      rw [coneHeight_eq_one_iff] at hc
      subst c
      rfl
  · intro hz
    subst z
    exact ConcreteCategory.congr_hom
      (mappingConePoint_mappingConeHeight f) PUnit.unit

/-- Reparameterizing a mapping cone by the identity interval map is the identity. -/
theorem mappingConeReparam_id (f : Arrow TopCat.{u}) [Nonempty f.left] :
    mappingConeReparam f (𝟙 I) (by rfl) (by rfl) =
      𝟙 (mappingCone f) := by
  let h₀ : ((𝟙 I.{u} : I ⟶ I) 0) = 0 := rfl
  let h₁ : ((𝟙 I.{u} : I ⟶ I) 1) = 1 := rfl
  change mappingConeReparam f (𝟙 I) h₀ h₁ = 𝟙 (mappingCone f)
  apply pushout.hom_ext
  · rw [mappingConeInl_mappingConeReparam]
    simp
  · rw [mappingConeInr_mappingConeReparam]
    simp only [Category.comp_id]
    apply ConcreteCategory.hom_ext
    intro c
    obtain ⟨p, rfl⟩ := (coneCylinder_isQuotientMap f.left).surjective c
    change (coneReparam f.left (𝟙 I) h₁ ≫
      pushout.inr f.hom (coneBase f.left)) (coneCylinder f.left p) =
        pushout.inr f.hom (coneBase f.left) (coneCylinder f.left p)
    rw [← ConcreteCategory.comp_apply, ← Category.assoc,
      coneCylinder_coneReparam]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of a mapping-cone reparameterization homotopy on the target summand. -/
theorem mappingConeReparamHomotopy_apply_inl
    (f : Arrow TopCat.{u}) [Nonempty f.left]
    {φ ψ : I.{u} ⟶ I} (K : TopCat.Homotopy φ ψ)
    (hφ₀ : φ 0 = 0) (hφ₁ : φ 1 = 1)
    (hψ₀ : ψ 0 = 0) (hψ₁ : ψ 1 = 1)
    (hK₀ : ∀ t : unitInterval, K (t, (0 : I)) = 0)
    (hK₁ : ∀ t : unitInterval, K (t, (1 : I)) = 1)
    (t : unitInterval) (y : f.right) :
    mappingConeReparamHomotopy f K hφ₀ hφ₁ hψ₀ hψ₁ hK₀ hK₁
        (t, pushout.inl f.hom (coneBase f.left) y) =
      pushout.inl f.hom (coneBase f.left) y := by
  simp [mappingConeReparamHomotopy, mappingConeReparam]

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of a mapping-cone reparameterization homotopy on the cone summand. -/
theorem mappingConeReparamHomotopy_apply_inr
    (f : Arrow TopCat.{u}) [Nonempty f.left]
    {φ ψ : I.{u} ⟶ I} (K : TopCat.Homotopy φ ψ)
    (hφ₀ : φ 0 = 0) (hφ₁ : φ 1 = 1)
    (hψ₀ : ψ 0 = 0) (hψ₁ : ψ 1 = 1)
    (hK₀ : ∀ t : unitInterval, K (t, (0 : I)) = 0)
    (hK₁ : ∀ t : unitInterval, K (t, (1 : I)) = 1)
    (t : unitInterval) (c : cone f.left) :
    mappingConeReparamHomotopy f K hφ₀ hφ₁ hψ₀ hψ₁ hK₀ hK₁
        (t, pushout.inr f.hom (coneBase f.left) c) =
      pushout.inr f.hom (coneBase f.left)
        (coneReparamHomotopy f.left K hφ₁ hψ₁ hK₁ (t, c)) := by
  simp [mappingConeReparamHomotopy, mappingConeReparam]


/-! ## Foundational cone lemmas -/

/-- The endpoints of the interval object are distinct. -/
theorem zero_ne_one_I : (0 : TopCat.I.{u}) ≠ 1 := by
  intro h
  exact zero_ne_one
    (congrArg (fun t : TopCat.I.{u} => (TopCat.I.homeomorph t : ℝ)) h)

/-- Height of a cylinder point is its interval coordinate. -/
theorem coneHeight_coneCylinder_apply (X : TopCat.{u})
    (p : ↑(X ⊗ TopCat.I)) :
    TopCat.coneHeight X (TopCat.coneCylinder X p) = p.2 :=
  ConcreteCategory.congr_hom (TopCat.coneCylinder_coneHeight X) p

/-- Height of the cone apex is one. -/
theorem coneHeight_conePoint_apply (X : TopCat.{u}) :
    TopCat.coneHeight X (TopCat.conePoint X PUnit.unit) = 1 :=
  ConcreteCategory.congr_hom (TopCat.conePoint_coneHeight X) PUnit.unit

/-- Height of a base point is zero. -/
theorem coneHeight_coneBase_apply (X : TopCat.{u}) (x : X) :
    TopCat.coneHeight X (TopCat.coneBase X x) = 0 :=
  ConcreteCategory.congr_hom (TopCat.coneBase_coneHeight X) x

/-- Height is preserved by cone maps, pointwise. -/
theorem coneHeight_coneMap_apply {X Y : TopCat.{u}} (f : X ⟶ Y)
    (c : TopCat.cone X) :
    TopCat.coneHeight Y (TopCat.coneMap f c) = TopCat.coneHeight X c :=
  ConcreteCategory.congr_hom (TopCat.coneMap_coneHeight f) c

/-- Two cylinder points identified in the cone agree, or are both at the apex. -/
theorem coneCylinder_eq_or (X : TopCat.{u}) (p q : ↑(X ⊗ TopCat.I))
    (h : TopCat.coneCylinder X p = TopCat.coneCylinder X q) :
    p = q ∨ (p.2 = 1 ∧ q.2 = 1) := by
  classical
  have hH : p.2 = q.2 := by
    have hHp := coneHeight_coneCylinder_apply X p
    have hHq := coneHeight_coneCylinder_apply X q
    rw [h] at hHp
    rw [← hHp, hHq]
  by_cases hp : p.2 = 1
  · exact Or.inr ⟨hp, by rw [← hH]; exact hp⟩
  · have hq : q.2 ≠ 1 := fun hqq => hp (hH.trans hqq)
    let _ : TopologicalSpace (Option X) := ⊤
    let cylinderLabel : X ⊗ TopCat.I ⟶ TopCat.of (Option X) :=
      TopCat.ofHom ⟨fun r ↦ if r.2 = 1 then none else some r.1,
        continuous_of_indiscreteTopology⟩
    let pointLabel : TopCat.of PUnit ⟶ TopCat.of (Option X) :=
      TopCat.ofHom ⟨fun _ ↦ none, continuous_of_indiscreteTopology⟩
    have hcompat : TopCat.ι₁ ≫ cylinderLabel =
        TopCat.isTerminalPUnit.from X ≫ pointLabel := by
      apply ConcreteCategory.hom_ext
      intro x
      change (if (1 : TopCat.I) = 1 then none else some x) = none
      simp
    let label : TopCat.cone X ⟶ TopCat.of (Option X) :=
      pushout.desc cylinderLabel pointLabel hcompat
    have hlab : ∀ r : ↑(X ⊗ TopCat.I),
        label (TopCat.coneCylinder X r) =
          if r.2 = 1 then none else some r.1 := by
      intro r
      change label ((pushout.inl TopCat.ι₁
        (TopCat.isTerminalPUnit.from X)) r) = _
      rw [← ConcreteCategory.comp_apply, pushout.inl_desc]
      rfl
    have hL := congrArg (fun z ↦ label z) h
    rw [hlab p, hlab q] at hL
    simp only [hp, hq, ite_false] at hL
    have h1 : p.1 = q.1 := Option.some.inj hL
    exact Or.inl (Prod.ext h1 hH)

/-- Height zero consists exactly of base points. -/
theorem coneHeight_eq_zero_exists_base (X : TopCat.{u})
    (c : TopCat.cone X) (hc : TopCat.coneHeight X c = 0) :
    ∃ x, TopCat.coneBase X x = c := by
  by_cases hX : Nonempty X
  · have _ := hX
    obtain ⟨p, rfl⟩ := (TopCat.coneCylinder_isQuotientMap X).surjective c
    obtain ⟨x, t⟩ := p
    have ht : t = (0 : TopCat.I) := by
      have h2 := coneHeight_coneCylinder_apply X (x, t)
      have hc' : TopCat.coneHeight X (TopCat.coneCylinder X (x, t)) = 0 := hc
      rw [h2] at hc'
      exact hc'
    subst ht
    exact ⟨x, rfl⟩
  · have : IsEmpty X := not_nonempty_iff.mp hX
    have hc0 : c = TopCat.conePoint X PUnit.unit :=
      TopCat.cone_eq_conePoint_of_isEmpty X c
    rw [hc0, coneHeight_conePoint_apply] at hc
    exact absurd hc.symm zero_ne_one_I

/-- A cone map of an injective map is injective. -/
theorem injective_coneMap {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : Function.Injective f) :
    Function.Injective (TopCat.coneMap f) := by
  intro c1 c2 h
  by_cases hX : Nonempty X
  · have _ := hX
    obtain ⟨p1, rfl⟩ := (TopCat.coneCylinder_isQuotientMap X).surjective c1
    obtain ⟨p2, rfl⟩ := (TopCat.coneCylinder_isQuotientMap X).surjective c2
    have e1 : TopCat.coneMap f (TopCat.coneCylinder X p1) =
        TopCat.coneCylinder Y ((f ▷ TopCat.I) p1) :=
      ConcreteCategory.congr_hom (TopCat.coneCylinder_naturality f) p1
    have e2 : TopCat.coneMap f (TopCat.coneCylinder X p2) =
        TopCat.coneCylinder Y ((f ▷ TopCat.I) p2) :=
      ConcreteCategory.congr_hom (TopCat.coneCylinder_naturality f) p2
    rw [e1, e2] at h
    obtain hEq | ⟨h1, h2⟩ := coneCylinder_eq_or Y _ _ h
    · have hfst : p1.1 = p2.1 := hf (congrArg Prod.fst hEq)
      have hsnd : p1.2 = p2.2 :=
        congrArg (fun p : ↥(Y ⊗ TopCat.I) ↦ p.2) hEq
      rw [Prod.ext hfst hsnd]
    · have q1 : p1.2 = (1 : TopCat.I) := h1
      have q2 : p2.2 = (1 : TopCat.I) := h2
      rw [TopCat.coneCylinder_eq_conePoint_of_snd_eq_one X p1 q1,
        TopCat.coneCylinder_eq_conePoint_of_snd_eq_one X p2 q2]
  · have : IsEmpty X := not_nonempty_iff.mp hX
    rw [TopCat.cone_eq_conePoint_of_isEmpty X c1,
      TopCat.cone_eq_conePoint_of_isEmpty X c2]

/-! ## The cone base inclusion is a closed map -/

/-- Singletons in the interval object are closed. -/
theorem isClosed_singleton_I (t : TopCat.I.{u}) :
    IsClosed ({t} : Set TopCat.I.{u}) := by
  have h : IsClosed (TopCat.I.homeomorph ⁻¹' {TopCat.I.homeomorph t}) :=
    isClosed_singleton.preimage TopCat.I.homeomorph.continuous
  rw [show TopCat.I.homeomorph ⁻¹' {TopCat.I.homeomorph t} = {t} from ?_] at h
  · exact h
  · ext s
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact TopCat.I.homeomorph.injective.eq_iff

/-- The cone base inclusion is a closed map. -/
theorem isClosedMap_coneBase (X : TopCat.{u}) :
    IsClosedMap (TopCat.coneBase X) := by
  intro F hF
  have hColim := pushout.isColimit (TopCat.ι₁ : X ⟶ X ⊗ TopCat.I)
    (TopCat.isTerminalPUnit.from X)
  refine (TopCat.isClosed_iff_of_isColimit _ hColim _).mpr ?_
  intro j
  cases j with
  | none =>
    have hzero : (pushout.cocone (TopCat.ι₁ : X ⟶ X ⊗ TopCat.I)
        (TopCat.isTerminalPUnit.from X)).ι.app WalkingSpan.zero =
        TopCat.ι₁ ≫ pushout.inl TopCat.ι₁
          (TopCat.isTerminalPUnit.from X) :=
      ((pushout.cocone (TopCat.ι₁ : X ⟶ X ⊗ TopCat.I)
        (TopCat.isTerminalPUnit.from X)).ι.naturality
        WalkingSpan.Hom.fst).symm
    rw [hzero]
    have hEq : ((TopCat.ι₁ ≫ pushout.inl TopCat.ι₁
        (TopCat.isTerminalPUnit.from X)) ⁻¹' (TopCat.coneBase X '' F)) = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false,
        iff_false]
      rintro ⟨y, hyF, hy⟩
      have hy' : TopCat.coneCylinder X (x, (1 : TopCat.I)) =
          TopCat.coneCylinder X (y, (0 : TopCat.I)) := hy.symm
      obtain hEq | ⟨h1, h2⟩ := coneCylinder_eq_or X _ _ hy'
      · have hs : (1 : TopCat.I) = 0 :=
          congrArg (fun p : ↥(X ⊗ TopCat.I) ↦ p.2) hEq
        exact absurd hs.symm zero_ne_one_I
      · exact absurd h2 zero_ne_one_I
    rw [hEq]
    exact isClosed_empty
  | some j =>
    cases j with
    | left =>
      change IsClosed ((pushout.inl TopCat.ι₁
        (TopCat.isTerminalPUnit.from X)) ⁻¹' (TopCat.coneBase X '' F))
      have hEq : ((pushout.inl TopCat.ι₁
          (TopCat.isTerminalPUnit.from X)) ⁻¹' (TopCat.coneBase X '' F)) =
          {p : ↥(X ⊗ TopCat.I) | p.1 ∈ F ∧ p.2 = (0 : TopCat.I)} := by
        ext p
        simp only [Set.mem_preimage, Set.mem_image, Set.mem_ofPred]
        constructor
        · rintro ⟨y, hyF, hy⟩
          obtain ⟨x, t⟩ := p
          have hy' : TopCat.coneCylinder X (x, t) =
              TopCat.coneCylinder X (y, (0 : TopCat.I)) := hy.symm
          obtain hEq | ⟨h1, h2⟩ := coneCylinder_eq_or X _ _ hy'
          · have hx : x = y :=
              congrArg (fun p : ↥(X ⊗ TopCat.I) ↦ p.1) hEq
            have ht : t = (0 : TopCat.I) :=
              congrArg (fun p : ↥(X ⊗ TopCat.I) ↦ p.2) hEq
            have hxF : (x, t).1 ∈ F := by
              change x ∈ F
              rw [hx]
              exact hyF
            have ht0 : (x, t).2 = (0 : TopCat.I) := ht
            exact ⟨hxF, ht0⟩
          · exact absurd h2 zero_ne_one_I
        · rintro ⟨hxF, ht⟩
          obtain ⟨x, t⟩ := p
          refine ⟨x, hxF, ?_⟩
          have ht' : t = (0 : TopCat.I) := ht
          rw [ht']
          rfl
      rw [hEq]
      have hf1 : Continuous (fun p : ↥(X ⊗ TopCat.I) ↦ p.1) := continuous_fst
      have hf2 : Continuous (fun p : ↥(X ⊗ TopCat.I) ↦ p.2) := continuous_snd
      have hset : {p : ↥(X ⊗ TopCat.I) | p.1 ∈ F ∧ p.2 = (0 : TopCat.I)} =
          (fun p : ↥(X ⊗ TopCat.I) ↦ p.1) ⁻¹' F ∩
            (fun p : ↥(X ⊗ TopCat.I) ↦ p.2) ⁻¹' {(0 : TopCat.I)} := by
        ext s
        exact Iff.rfl
      rw [hset]
      exact IsClosed.inter (IsClosed.preimage hf1 hF)
        (IsClosed.preimage hf2 (isClosed_singleton_I 0))
    | right =>
      change IsClosed ((pushout.inr TopCat.ι₁
        (TopCat.isTerminalPUnit.from X)) ⁻¹' (TopCat.coneBase X '' F))
      have hEq : ((pushout.inr TopCat.ι₁
          (TopCat.isTerminalPUnit.from X)) ⁻¹' (TopCat.coneBase X '' F)) = ∅ := by
        ext u
        obtain ⟨⟩ := u
        simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false,
          iff_false]
        rintro ⟨y, hyF, hy⟩
        have hh := congrArg (fun w ↦ TopCat.coneHeight X w) hy
        have hA : TopCat.coneHeight X
            ((pushout.inr TopCat.ι₁ (TopCat.isTerminalPUnit.from X))
              PUnit.unit) = 1 :=
          ConcreteCategory.congr_hom (TopCat.conePoint_coneHeight X)
            PUnit.unit
        have hB : TopCat.coneHeight X (TopCat.coneBase X y) = 0 :=
          coneHeight_coneBase_apply X y
        rw [hB, hA] at hh
        exact absurd hh zero_ne_one_I
      rw [hEq]
      exact isClosed_empty

/-! ## Cone maps of closed embeddings are closed maps -/

/-- Cone maps act on cylinder points via the product map. -/
theorem coneMap_coneCylinder_apply {X Y : TopCat.{u}} (f : X ⟶ Y)
    (p : ↥(X ⊗ TopCat.I)) :
    TopCat.coneMap f (TopCat.coneCylinder X p) =
      TopCat.coneCylinder Y ((f ▷ TopCat.I) p) :=
  ConcreteCategory.congr_hom (TopCat.coneCylinder_naturality f) p

/-- Cone maps send apex to apex, pointwise. -/
theorem coneMap_conePoint_apply {X Y : TopCat.{u}} (f : X ⟶ Y) :
    TopCat.coneMap f (TopCat.conePoint X PUnit.unit) =
      TopCat.conePoint Y PUnit.unit :=
  ConcreteCategory.congr_hom (TopCat.conePoint_naturality f) PUnit.unit

/-- The top of the cylinder maps to the apex, pointwise. -/
theorem iota_coneCylinder_apply (Y : TopCat.{u}) (y : Y) :
    (TopCat.ι₁ ≫ pushout.inl TopCat.ι₁
      (TopCat.isTerminalPUnit.from Y)) y =
      TopCat.conePoint Y PUnit.unit :=
  ConcreteCategory.congr_hom (TopCat.ι₁_coneCylinder Y) y

/-- The cone apex is a closed point. -/
theorem isClosed_singleton_conePoint (Y : TopCat.{u}) :
    IsClosed ({TopCat.conePoint Y PUnit.unit} : Set (TopCat.cone Y)) := by
  have hColim := pushout.isColimit (TopCat.ι₁ : Y ⟶ Y ⊗ TopCat.I)
    (TopCat.isTerminalPUnit.from Y)
  refine (TopCat.isClosed_iff_of_isColimit _ hColim _).mpr ?_
  intro j
  cases j with
  | none =>
    have hzero : (pushout.cocone (TopCat.ι₁ : Y ⟶ Y ⊗ TopCat.I)
        (TopCat.isTerminalPUnit.from Y)).ι.app WalkingSpan.zero =
        TopCat.ι₁ ≫ pushout.inl TopCat.ι₁
          (TopCat.isTerminalPUnit.from Y) :=
      ((pushout.cocone (TopCat.ι₁ : Y ⟶ Y ⊗ TopCat.I)
        (TopCat.isTerminalPUnit.from Y)).ι.naturality
        WalkingSpan.Hom.fst).symm
    rw [hzero]
    have hEq : ((TopCat.ι₁ ≫ pushout.inl TopCat.ι₁
        (TopCat.isTerminalPUnit.from Y)) ⁻¹'
        {TopCat.conePoint Y PUnit.unit}) = Set.univ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ,
        iff_true]
      exact iota_coneCylinder_apply Y y
    rw [hEq]
    exact isClosed_univ
  | some j =>
    cases j with
    | left =>
      change IsClosed ((pushout.inl TopCat.ι₁
        (TopCat.isTerminalPUnit.from Y)) ⁻¹'
        {TopCat.conePoint Y PUnit.unit})
      have hEq : ((pushout.inl TopCat.ι₁
          (TopCat.isTerminalPUnit.from Y)) ⁻¹'
          {TopCat.conePoint Y PUnit.unit}) =
          {q : ↥(Y ⊗ TopCat.I) | q.2 = (1 : TopCat.I)} := by
        ext q
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred]
        constructor
        · intro h
          have hC : TopCat.coneCylinder Y q =
              TopCat.conePoint Y PUnit.unit := h
          have hh := congrArg (fun w ↦ TopCat.coneHeight Y w) hC
          rw [coneHeight_coneCylinder_apply,
            coneHeight_conePoint_apply] at hh
          exact hh
        · intro h
          obtain ⟨y, t⟩ := q
          exact TopCat.coneCylinder_eq_conePoint_of_snd_eq_one Y (y, t) h
      rw [hEq]
      have hf2 : Continuous (fun q : ↥(Y ⊗ TopCat.I) ↦ q.2) :=
        continuous_snd
      have hset : {q : ↥(Y ⊗ TopCat.I) | q.2 = (1 : TopCat.I)} =
          (fun q : ↥(Y ⊗ TopCat.I) ↦ q.2) ⁻¹' {(1 : TopCat.I)} := by
        ext s
        exact Iff.rfl
      rw [hset]
      exact IsClosed.preimage hf2 (isClosed_singleton_I 1)
    | right =>
      change IsClosed ((pushout.inr TopCat.ι₁
        (TopCat.isTerminalPUnit.from Y)) ⁻¹'
        {TopCat.conePoint Y PUnit.unit})
      have hEq : ((pushout.inr TopCat.ι₁
          (TopCat.isTerminalPUnit.from Y)) ⁻¹'
          {TopCat.conePoint Y PUnit.unit}) = Set.univ := by
        ext u
        obtain ⟨⟩ := u
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ,
          iff_true]
        rfl
      rw [hEq]
      exact isClosed_univ

/-- A cone map of a closed embedding is a closed map. -/
theorem isClosedMap_coneMap {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : Topology.IsClosedEmbedding f) :
    IsClosedMap (TopCat.coneMap f) := by
  intro F hF
  by_cases hX : Nonempty X
  · have _ := hX
    have hG : IsClosed (TopCat.coneCylinder X ⁻¹' F) :=
      IsClosed.preimage (TopCat.coneCylinder X).hom.continuous hF
    have hCE : Topology.IsClosedEmbedding
        (Prod.map f (id : ↑(TopCat.I) → ↑(TopCat.I))) :=
      hf.prodMap Topology.IsClosedEmbedding.id
    have hCM : IsClosedMap (f ▷ TopCat.I) := hCE.isClosedMap
    by_cases hA : TopCat.conePoint X PUnit.unit ∈ F
    · have hColim := pushout.isColimit (TopCat.ι₁ : Y ⟶ Y ⊗ TopCat.I)
        (TopCat.isTerminalPUnit.from Y)
      refine (TopCat.isClosed_iff_of_isColimit _ hColim _).mpr ?_
      intro j
      cases j with
      | none =>
        have hzero : (pushout.cocone (TopCat.ι₁ : Y ⟶ Y ⊗ TopCat.I)
            (TopCat.isTerminalPUnit.from Y)).ι.app WalkingSpan.zero =
            TopCat.ι₁ ≫ pushout.inl TopCat.ι₁
              (TopCat.isTerminalPUnit.from Y) :=
          ((pushout.cocone (TopCat.ι₁ : Y ⟶ Y ⊗ TopCat.I)
            (TopCat.isTerminalPUnit.from Y)).ι.naturality
            WalkingSpan.Hom.fst).symm
        rw [hzero]
        have hEq : ((TopCat.ι₁ ≫ pushout.inl TopCat.ι₁
            (TopCat.isTerminalPUnit.from Y)) ⁻¹' (TopCat.coneMap f '' F)) =
            Set.univ := by
          ext y
          simp only [Set.mem_preimage, Set.mem_image, Set.mem_univ,
            iff_true]
          have eA := coneMap_conePoint_apply f
          have eI := iota_coneCylinder_apply Y y
          exact ⟨TopCat.conePoint X PUnit.unit, hA, eA.trans eI.symm⟩
        rw [hEq]
        exact isClosed_univ
      | some j =>
        cases j with
        | left =>
          change IsClosed ((pushout.inl TopCat.ι₁
            (TopCat.isTerminalPUnit.from Y)) ⁻¹' (TopCat.coneMap f '' F))
          have hEq : ((pushout.inl TopCat.ι₁
              (TopCat.isTerminalPUnit.from Y)) ⁻¹' (TopCat.coneMap f '' F)) =
              (f ▷ TopCat.I) '' (TopCat.coneCylinder X ⁻¹' F) ∪
                {q : ↥(Y ⊗ TopCat.I) | q.2 = (1 : TopCat.I)} := by
            ext q
            simp only [Set.mem_preimage, Set.mem_image, Set.mem_union,
              Set.mem_ofPred]
            constructor
            · rintro ⟨z, hzF, hz⟩
              obtain ⟨p, rfl⟩ :=
                (TopCat.coneCylinder_isQuotientMap X).surjective z
              have hzC : TopCat.coneMap f (TopCat.coneCylinder X p) =
                  TopCat.coneCylinder Y q := hz
              rw [coneMap_coneCylinder_apply] at hzC
              obtain ⟨x, s⟩ := p
              obtain hEq | ⟨h1, h2⟩ := coneCylinder_eq_or Y _ _ hzC
              · exact Or.inl ⟨(x, s), hzF, hEq⟩
              · exact Or.inr h2
            · rintro (⟨p, hpG, hpq⟩ | ht)
              · refine ⟨TopCat.coneCylinder X p, hpG, ?_⟩
                rw [coneMap_coneCylinder_apply, hpq]
                rfl
              · refine ⟨TopCat.conePoint X PUnit.unit, hA, ?_⟩
                rw [coneMap_conePoint_apply]
                exact (TopCat.coneCylinder_eq_conePoint_of_snd_eq_one Y q
                  ht).symm
          rw [hEq]
          refine IsClosed.union (hCM _ hG) ?_
          have hf2 : Continuous (fun q : ↥(Y ⊗ TopCat.I) ↦ q.2) :=
            continuous_snd
          have hset : {q : ↥(Y ⊗ TopCat.I) | q.2 = (1 : TopCat.I)} =
              (fun q : ↥(Y ⊗ TopCat.I) ↦ q.2) ⁻¹' {(1 : TopCat.I)} := by
            ext s
            exact Iff.rfl
          rw [hset]
          exact IsClosed.preimage hf2 (isClosed_singleton_I 1)
        | right =>
          change IsClosed ((pushout.inr TopCat.ι₁
            (TopCat.isTerminalPUnit.from Y)) ⁻¹' (TopCat.coneMap f '' F))
          have hEq : ((pushout.inr TopCat.ι₁
              (TopCat.isTerminalPUnit.from Y)) ⁻¹' (TopCat.coneMap f '' F)) =
              Set.univ := by
            ext u
            obtain ⟨⟩ := u
            simp only [Set.mem_preimage, Set.mem_image, Set.mem_univ,
              iff_true]
            exact ⟨TopCat.conePoint X PUnit.unit, hA,
              coneMap_conePoint_apply f⟩
          rw [hEq]
          exact isClosed_univ
    · have hColim := pushout.isColimit (TopCat.ι₁ : Y ⟶ Y ⊗ TopCat.I)
        (TopCat.isTerminalPUnit.from Y)
      refine (TopCat.isClosed_iff_of_isColimit _ hColim _).mpr ?_
      intro j
      cases j with
      | none =>
        have hzero : (pushout.cocone (TopCat.ι₁ : Y ⟶ Y ⊗ TopCat.I)
            (TopCat.isTerminalPUnit.from Y)).ι.app WalkingSpan.zero =
            TopCat.ι₁ ≫ pushout.inl TopCat.ι₁
              (TopCat.isTerminalPUnit.from Y) :=
          ((pushout.cocone (TopCat.ι₁ : Y ⟶ Y ⊗ TopCat.I)
            (TopCat.isTerminalPUnit.from Y)).ι.naturality
            WalkingSpan.Hom.fst).symm
        rw [hzero]
        have hEq : ((TopCat.ι₁ ≫ pushout.inl TopCat.ι₁
            (TopCat.isTerminalPUnit.from Y)) ⁻¹' (TopCat.coneMap f '' F)) =
            ∅ := by
          ext y
          simp only [Set.mem_preimage, Set.mem_image,
            Set.mem_empty_iff_false, iff_false]
          rintro ⟨z, hzF, hz⟩
          have hh := congrArg (fun w ↦ TopCat.coneHeight Y w) hz
          have eL : TopCat.coneHeight Y (TopCat.coneMap f z) =
              TopCat.coneHeight X z := coneHeight_coneMap_apply f z
          have eR : TopCat.coneHeight Y
              ((TopCat.ι₁ ≫ pushout.inl TopCat.ι₁
                (TopCat.isTerminalPUnit.from Y)) y) = 1 := by
            have h1 := coneHeight_conePoint_apply Y
            have h2 := iota_coneCylinder_apply Y y
            rw [h2]
            exact h1
          rw [eL, eR] at hh
          rw [TopCat.coneHeight_eq_one_iff X z] at hh
          rw [hh] at hzF
          exact absurd hzF hA
        rw [hEq]
        exact isClosed_empty
      | some j =>
        cases j with
        | left =>
          change IsClosed ((pushout.inl TopCat.ι₁
            (TopCat.isTerminalPUnit.from Y)) ⁻¹' (TopCat.coneMap f '' F))
          have hEq : ((pushout.inl TopCat.ι₁
              (TopCat.isTerminalPUnit.from Y)) ⁻¹' (TopCat.coneMap f '' F)) =
              (f ▷ TopCat.I) '' (TopCat.coneCylinder X ⁻¹' F) := by
            ext q
            simp only [Set.mem_preimage, Set.mem_image]
            constructor
            · rintro ⟨z, hzF, hz⟩
              obtain ⟨p, rfl⟩ :=
                (TopCat.coneCylinder_isQuotientMap X).surjective z
              have hzC : TopCat.coneMap f (TopCat.coneCylinder X p) =
                  TopCat.coneCylinder Y q := hz
              rw [coneMap_coneCylinder_apply] at hzC
              obtain ⟨x, s⟩ := p
              obtain hEq | ⟨h1, h2⟩ := coneCylinder_eq_or Y _ _ hzC
              · exact ⟨(x, s), hzF, hEq⟩
              · have hs : s = (1 : TopCat.I) := h1
                have eC : TopCat.coneCylinder X (x, s) =
                    TopCat.conePoint X PUnit.unit :=
                  TopCat.coneCylinder_eq_conePoint_of_snd_eq_one X (x, s) hs
                have hzF' : TopCat.coneCylinder X (x, s) ∈ F := hzF
                rw [eC] at hzF'
                exact absurd hzF' hA
            · rintro ⟨p, hpG, hpq⟩
              refine ⟨TopCat.coneCylinder X p, hpG, ?_⟩
              rw [coneMap_coneCylinder_apply, hpq]
              rfl
          rw [hEq]
          exact hCM _ hG
        | right =>
          change IsClosed ((pushout.inr TopCat.ι₁
            (TopCat.isTerminalPUnit.from Y)) ⁻¹' (TopCat.coneMap f '' F))
          have hEq : ((pushout.inr TopCat.ι₁
              (TopCat.isTerminalPUnit.from Y)) ⁻¹' (TopCat.coneMap f '' F)) =
              ∅ := by
            ext u
            obtain ⟨⟩ := u
            simp only [Set.mem_preimage, Set.mem_image,
              Set.mem_empty_iff_false, iff_false]
            rintro ⟨z, hzF, hz⟩
            have hh := congrArg (fun w ↦ TopCat.coneHeight Y w) hz
            have eL : TopCat.coneHeight Y (TopCat.coneMap f z) =
                TopCat.coneHeight X z := coneHeight_coneMap_apply f z
            have eR : TopCat.coneHeight Y
                ((pushout.inr TopCat.ι₁ (TopCat.isTerminalPUnit.from Y))
                  PUnit.unit) = 1 := coneHeight_conePoint_apply Y
            rw [eL, eR] at hh
            rw [TopCat.coneHeight_eq_one_iff X z] at hh
            rw [hh] at hzF
            exact absurd hzF hA
          rw [hEq]
          exact isClosed_empty
  · have : IsEmpty X := not_nonempty_iff.mp hX
    by_cases hA : TopCat.conePoint X PUnit.unit ∈ F
    · have hEq : TopCat.coneMap f '' F =
          {TopCat.conePoint Y PUnit.unit} := by
        ext w
        simp only [Set.mem_image, Set.mem_singleton_iff]
        constructor
        · rintro ⟨z, hzF, hz⟩
          have hz0 : z = TopCat.conePoint X PUnit.unit :=
            TopCat.cone_eq_conePoint_of_isEmpty X z
          rw [hz0, coneMap_conePoint_apply] at hz
          exact hz.symm
        · intro hw
          refine ⟨TopCat.conePoint X PUnit.unit, hA, ?_⟩
          rw [coneMap_conePoint_apply]
          exact hw.symm
      rw [hEq]
      exact isClosed_singleton_conePoint Y
    · have hEq : TopCat.coneMap f '' F = ∅ := by
        ext w
        simp only [Set.mem_image, Set.mem_empty_iff_false, iff_false]
        rintro ⟨z, hzF, hz⟩
        have hz0 : z = TopCat.conePoint X PUnit.unit :=
          TopCat.cone_eq_conePoint_of_isEmpty X z
        rw [hz0] at hzF
        exact absurd hzF hA
      rw [hEq]
      exact isClosed_empty

/-- The cone base inclusion is a closed embedding. -/
theorem isClosedEmbedding_coneBase (X : TopCat.{u}) :
    Topology.IsClosedEmbedding (TopCat.coneBase X) :=
  Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (TopCat.coneBase X).hom.continuous
    (TopCat.coneBase_isEmbedding X).injective
    (isClosedMap_coneBase X)

/-- A cone map of a closed embedding is a closed embedding. -/
theorem isClosedEmbedding_coneMap {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : Topology.IsClosedEmbedding f) :
    Topology.IsClosedEmbedding (TopCat.coneMap f) :=
  Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    (TopCat.coneMap f).hom.continuous
    (injective_coneMap hf.injective)
    (isClosedMap_coneMap hf)


end TopCat
