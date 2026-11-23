/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.Topology.Category.TopCat.MappingCone
public import MathlibExt.Topology.Category.TopCat.PushoutOpenComplement
public import MathlibExt.Topology.Homotopy.Contractible
public import MathlibExt.Topology.Category.TopPair.OrderedTwoSetCover
public import MathlibExt.Topology.Category.TopPair.Triple

/-!
# Topological suspension

This file defines the unreduced suspension as the mapping cone of the terminal
map and packages it as a pointed-space-valued functor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopCat

/-- The terminal maps `X ⟶ *`, functorially in `X`. -/
noncomputable def terminalArrowFunctor : TopCat.{u} ⥤ Arrow TopCat.{u} where
  obj X := Arrow.mk (isTerminalPUnit.from X)
  map f := Arrow.homMk f (𝟙 _) (by
    apply isTerminalPUnit.hom_ext)
  map_id X := by ext <;> simp
  map_comp f g := by ext <;> simp

@[simp]
lemma terminalArrowFunctor_obj_left (X : TopCat.{u}) :
    (terminalArrowFunctor.obj X).left = X := rfl

@[simp]
lemma terminalArrowFunctor_obj_right (X : TopCat.{u}) :
    (terminalArrowFunctor.obj X).right = TopCat.of PUnit := rfl

@[simp]
lemma terminalArrowFunctor_obj_hom (X : TopCat.{u}) :
    (terminalArrowFunctor.obj X).hom = isTerminalPUnit.from X := rfl

@[simp]
lemma terminalArrowFunctor_map_left {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (terminalArrowFunctor.map f).left = f := rfl

@[simp]
lemma terminalArrowFunctor_map_right {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (terminalArrowFunctor.map f).right = 𝟙 (TopCat.of PUnit) := rfl

/-- The unreduced suspension, as the mapping cone of `X ⟶ *`. -/
noncomputable def suspensionFunctor : TopCat.{u} ⥤ PointedTopCat.{u} :=
  terminalArrowFunctor ⋙ mappingConeFunctor

@[simp]
lemma suspensionFunctor_obj_right (X : TopCat.{u}) :
    (suspensionFunctor.obj X).right =
      pushout (isTerminalPUnit.from X) (coneBase X) := rfl

@[simp]
lemma suspensionFunctor_obj_hom (X : TopCat.{u}) :
    (suspensionFunctor.obj X).hom =
      conePoint X ≫ pushout.inr (isTerminalPUnit.from X) (coneBase X) := rfl

@[simp]
lemma suspensionFunctor_map_right {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (suspensionFunctor.map f).right =
      mappingConeMap (terminalArrowFunctor.map f) := rfl

/-- The distinguished basepoint inclusion into a cone is a homotopy equivalence. -/
noncomputable def pointedConeBasepointHomotopyEquiv (X : PointedTopCat.{u}) :
    ContinuousMap.HomotopyEquiv PUnit (cone X.right) := by
  let _ : Nonempty X.right := ⟨X.hom PUnit.unit⟩
  let b := X.hom ≫ coneBase X.right
  let q := isTerminalPUnit.from (cone X.right)
  let H := coneContractingHomotopy X.right
  have hbq : b ≫ q = 𝟙 (TopCat.of PUnit) := by
    apply isTerminalPUnit.hom_ext
  let baseToApex : TopCat.Homotopy b (conePoint X.right) := by
    let K := H.comp (TopCat.Homotopy.refl b)
    have hsource : b ≫ 𝟙 (cone X.right) = b := Category.comp_id b
    have htarget : b ≫ q ≫ conePoint X.right = conePoint X.right := by
      rw [← Category.assoc, hbq, Category.id_comp]
    exact ContinuousMap.Homotopy.cast K
      (congrArg TopCat.Hom.hom hsource)
      (congrArg TopCat.Hom.hom htarget)
  let apexToBaseConstant :
      TopCat.Homotopy (q ≫ conePoint X.right) (q ≫ b) := by
    exact (baseToApex.symm).comp (TopCat.Homotopy.refl q)
  let toBase : TopCat.Homotopy (𝟙 (cone X.right)) (q ≫ b) :=
    H.trans apexToBaseConstant
  exact
    { toFun := b.hom
      invFun := q.hom
      left_inv := by
        have h : b ≫ q = 𝟙 (TopCat.of PUnit) := by
          apply isTerminalPUnit.hom_ext
        rw [show q.hom.comp b.hom = (b ≫ q).hom by rfl, h]
        exact ⟨TopCat.Homotopy.refl (𝟙 (TopCat.of PUnit))⟩
      right_inv := ⟨toBase.symm⟩ }

@[simp]
theorem pointedConeBasepointHomotopyEquiv_toFun (X : PointedTopCat.{u}) :
    TopCat.ofHom (pointedConeBasepointHomotopyEquiv X).toFun =
      X.hom ≫ coneBase X.right := by
  unfold pointedConeBasepointHomotopyEquiv
  rfl

/-- The functorial triple `* ⟶ X ⟶ CX` associated to a pointed space. -/
noncomputable def pointedConeTripleFunctor :
    PointedTopCat.{u} ⥤ AlgebraicTopology.TopTriple.{u} where
  obj X := ⟨ComposableArrows.mk₂ X.hom (coneBase X.right),
    Topology.IsEmbedding.of_subsingleton X.hom, coneBase_isEmbedding X.right⟩
  map {X Y} f := ObjectProperty.homMk
    (ComposableArrows.homMk₂ (𝟙 _) f.right (coneMap f.right)
      (by
        change X.hom ≫ f.right = 𝟙 _ ≫ Y.hom
        simpa only [Category.id_comp] using f.w)
      (coneBase_naturality f.right))
  map_id X := by
    apply ObjectProperty.hom_ext
    apply ComposableArrows.hom_ext₂
    · rfl
    · rfl
    · exact coneMap_id X.right
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply ComposableArrows.hom_ext₂
    · change 𝟙 _ = 𝟙 _ ≫ 𝟙 _
      simp
    · change f.right ≫ g.right = f.right ≫ g.right
      rfl
    · change coneMap (f.right ≫ g.right) = coneMap f.right ≫ coneMap g.right
      exact coneMap_comp f.right g.right

@[simp]
lemma pointedConeTripleFunctor_obj_obj (X : PointedTopCat.{u}) :
    (pointedConeTripleFunctor.obj X).obj =
      ComposableArrows.mk₂ X.hom (coneBase X.right) := rfl

@[simp]
lemma pointedConeTripleFunctor_map_app_zero {X Y : PointedTopCat.{u}} (f : X ⟶ Y) :
    ComposableArrows.app' (pointedConeTripleFunctor.map f).hom 0 = 𝟙 _ := rfl

@[simp]
lemma pointedConeTripleFunctor_map_app_one {X Y : PointedTopCat.{u}} (f : X ⟶ Y) :
    ComposableArrows.app' (pointedConeTripleFunctor.map f).hom 1 = f.right := rfl

@[simp]
lemma pointedConeTripleFunctor_map_app_two {X Y : PointedTopCat.{u}} (f : X ⟶ Y) :
    ComposableArrows.app' (pointedConeTripleFunctor.map f).hom 2 = coneMap f.right := rfl

open MonoidalCategory

/-- Collapse the cone base to the pointed suspension, reversing the cone coordinate. -/
noncomputable def coneToSuspension (X : TopCat.{u}) :
    cone X ⟶ (suspensionFunctor.obj X).right :=
  pushout.desc
    ((X ◁ TopCat.I.symm) ≫ coneCylinder X ≫
      pushout.inr (isTerminalPUnit.from X) (coneBase X))
    (pushout.inl (isTerminalPUnit.from X) (coneBase X)) (by
      apply ConcreteCategory.hom_ext
      intro x
      change pushout.inr (isTerminalPUnit.from X) (coneBase X)
          (coneCylinder X (x, TopCat.I.symm (1 : TopCat.I))) =
        pushout.inl (isTerminalPUnit.from X) (coneBase X) PUnit.unit
      rw [TopCat.I.symm_one]
      change (coneBase X ≫
          pushout.inr (isTerminalPUnit.from X) (coneBase X)) x = _
      rw [← pushout.condition]
      rfl)

@[reassoc]
theorem coneCylinder_coneToSuspension (X : TopCat.{u}) :
    coneCylinder X ≫ coneToSuspension X =
      (X ◁ TopCat.I.symm) ≫ coneCylinder X ≫
        pushout.inr (isTerminalPUnit.from X) (coneBase X) :=
  pushout.inl_desc _ _ _

@[reassoc]
theorem conePoint_coneToSuspension (X : TopCat.{u}) :
    conePoint X ≫ coneToSuspension X =
      pushout.inl (isTerminalPUnit.from X) (coneBase X) :=
  pushout.inr_desc _ _ _

@[reassoc]
theorem coneBase_coneToSuspension (X : TopCat.{u}) :
    coneBase X ≫ coneToSuspension X =
      isTerminalPUnit.from X ≫ (suspensionFunctor.obj X).hom := by
  change TopCat.ι₀ ≫ coneCylinder X ≫ coneToSuspension X = _
  rw [coneCylinder_coneToSuspension]
  apply ConcreteCategory.hom_ext
  intro x
  change pushout.inr (isTerminalPUnit.from X) (coneBase X)
      (coneCylinder X (x, TopCat.I.symm (0 : TopCat.I))) =
    (isTerminalPUnit.from X ≫ conePoint X ≫
      pushout.inr (isTerminalPUnit.from X) (coneBase X)) x
  rw [TopCat.I.symm_zero]
  change (coneCylinder X) (x, (1 : TopCat.I)) |> fun z =>
      pushout.inr (isTerminalPUnit.from X) (coneBase X) z = _
  rw [show coneCylinder X (x, (1 : TopCat.I)) =
      conePoint X PUnit.unit by
    change (TopCat.ι₁ ≫ coneCylinder X) x = _
    rw [ι₁_coneCylinder]
    rfl]
  rfl

/-- The cone-to-suspension quotient maps are natural. -/
theorem coneToSuspension_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) :
    coneMap f ≫ coneToSuspension Y =
      coneToSuspension X ≫ (suspensionFunctor.map f).right := by
  apply pushout.hom_ext
  · rw [← Category.assoc, coneMap_inl]
    change (f ▷ TopCat.I) ≫ coneCylinder Y ≫ coneToSuspension Y =
      coneCylinder X ≫ coneToSuspension X ≫
        (suspensionFunctor.map f).right
    rw [coneCylinder_coneToSuspension]
    rw [coneCylinder_coneToSuspension_assoc]
    apply ConcreteCategory.hom_ext
    intro p
    rcases p with ⟨x, t⟩
    change pushout.inr (isTerminalPUnit.from Y) (coneBase Y)
        (coneCylinder Y (f x, TopCat.I.symm t)) =
      mappingConeMap (terminalArrowFunctor.map f)
        (pushout.inr (isTerminalPUnit.from X) (coneBase X)
          (coneCylinder X (x, TopCat.I.symm t)))
    have hcone := ConcreteCategory.congr_hom (coneCylinder_naturality f)
      (x, TopCat.I.symm t)
    have hinr := ConcreteCategory.congr_hom
      (mappingConeMap_inr (terminalArrowFunctor.map f))
      (coneCylinder X (x, TopCat.I.symm t))
    exact congrArg
      (fun z => pushout.inr (isTerminalPUnit.from Y) (coneBase Y) z)
      hcone.symm |>.trans hinr.symm
  · change (conePoint X ≫ coneMap f) ≫ coneToSuspension Y =
      conePoint X ≫ coneToSuspension X ≫
        (suspensionFunctor.map f).right
    rw [← Category.assoc, conePoint_naturality]
    rw [conePoint_coneToSuspension]
    change pushout.inl (isTerminalPUnit.from Y) (coneBase Y) =
      (conePoint X ≫ coneToSuspension X) ≫
        mappingConeMap (terminalArrowFunctor.map f)
    rw [conePoint_coneToSuspension]
    exact (mappingConeMap_inl (terminalArrowFunctor.map f)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The cone-to-suspension quotient reverses the cone height. -/
@[reassoc]
theorem coneToSuspension_mappingConeHeight (X : TopCat.{u}) :
    coneToSuspension X ≫ mappingConeHeight (terminalArrowFunctor.obj X) =
      coneHeight X ≫ TopCat.I.symm := by
  let q : cone X ⟶ mappingCone (terminalArrowFunctor.obj X) := coneToSuspension X
  let h : pushout (isTerminalPUnit.from X) (coneBase X) ⟶ TopCat.I :=
    mappingConeHeight (terminalArrowFunctor.obj X)
  change q ≫ h = coneHeight X ≫ TopCat.I.symm
  apply pushout.hom_ext
  · change (coneCylinder X ≫ q) ≫ h =
      (coneCylinder X ≫ coneHeight X) ≫ TopCat.I.symm
    have hq : coneCylinder X ≫ q =
        (X ◁ TopCat.I.symm) ≫ coneCylinder X ≫
          pushout.inr (isTerminalPUnit.from X) (coneBase X) :=
      coneCylinder_coneToSuspension X
    rw [hq]
    unfold h mappingConeHeight
    rw [Category.assoc, Category.assoc, pushout.inr_desc]
    simp only [terminalArrowFunctor_obj_left]
    rw [Category.assoc, coneCylinder_coneHeight]
    rw [← Category.assoc, coneCylinder_coneHeight]
    exact CartesianMonoidalCategory.whiskerLeft_snd X TopCat.I.symm
  · change (conePoint X ≫ q) ≫ h =
      (conePoint X ≫ coneHeight X) ≫ TopCat.I.symm
    have hq : conePoint X ≫ q =
        pushout.inl (isTerminalPUnit.from X) (coneBase X) :=
      conePoint_coneToSuspension X
    rw [hq]
    unfold h mappingConeHeight
    rw [pushout.inl_desc]
    simp only [terminalArrowFunctor_obj_right]
    rw [conePoint_coneHeight]
    apply TopCat.hom_ext
    ext x
    norm_num [TopCat.const]

/-- The lower open height neighborhood in a cone. -/
noncomputable def coneLowerSet (X : TopCat.{u}) : Set (cone X) :=
  {z | ((I.homeomorph (coneHeight X z) : unitInterval) : ℝ) < 2 / 3}

/-- The upper open height neighborhood in a cone. -/
noncomputable def coneUpperSet (X : TopCat.{u}) : Set (cone X) :=
  {z | (1 : ℝ) / 3 < ((I.homeomorph (coneHeight X z) : unitInterval) : ℝ)}

/-- The natural two-set height cover of a cone. -/
noncomputable def coneHeightCoverFunctor :
    TopCat.{u} ⥤ AlgebraicTopology.OrderedTwoSetCover.{u} where
  obj X :=
    { X := cone X
      left := coneLowerSet X
      right := coneUpperSet X
      interior_cover := by
        have hLower : IsOpen (coneLowerSet X) :=
          isOpen_Iio.preimage
            (continuous_subtype_val.comp
              (I.homeomorph.continuous.comp (coneHeight X).hom.continuous))
        have hUpper : IsOpen (coneUpperSet X) :=
          isOpen_Ioi.preimage
            (continuous_subtype_val.comp
              (I.homeomorph.continuous.comp (coneHeight X).hom.continuous))
        rw [hLower.interior_eq, hUpper.interior_eq]
        intro z _
        by_cases hz : ((I.homeomorph (coneHeight X z) : unitInterval) : ℝ) < 2 / 3
        · exact Set.mem_union_left _ hz
        · exact Set.mem_union_right _
            (lt_of_lt_of_le (by norm_num) (le_of_not_gt hz)) }
  map f :=
    { f := coneMap f
      left_maps := by
        intro z hz
        change ((I.homeomorph (coneHeight _ (coneMap f z)) : unitInterval) : ℝ) < 2 / 3
        have h := ConcreteCategory.congr_hom (coneMap_coneHeight f) z
        change coneHeight _ (coneMap f z) = coneHeight _ z at h
        rw [h]
        exact hz
      right_maps := by
        intro z hz
        change (1 : ℝ) / 3 <
          ((I.homeomorph (coneHeight _ (coneMap f z)) : unitInterval) : ℝ)
        have h := ConcreteCategory.congr_hom (coneMap_coneHeight f) z
        change coneHeight _ (coneMap f z) = coneHeight _ z at h
        rw [h]
        exact hz }
  map_id X := by
    apply AlgebraicTopology.OrderedTwoSetCover.Hom.ext
    change coneMap (𝟙 X) = 𝟙 _
    exact coneMap_id X
  map_comp f g := by
    apply AlgebraicTopology.OrderedTwoSetCover.Hom.ext
    change coneMap (f ≫ g) = coneMap f ≫ coneMap g
    exact coneMap_comp f g

/-- The lower open height neighborhood in a suspension. -/
noncomputable def suspensionLowerSet (X : TopCat.{u}) :
    Set ((suspensionFunctor.obj X).right) :=
  {z | ((I.homeomorph
    (mappingConeHeight (terminalArrowFunctor.obj X) z) : unitInterval) : ℝ) < 2 / 3}

/-- The upper open height neighborhood in a suspension. -/
noncomputable def suspensionUpperSet (X : TopCat.{u}) :
    Set ((suspensionFunctor.obj X).right) :=
  {z | (1 : ℝ) / 3 < ((I.homeomorph
    (mappingConeHeight (terminalArrowFunctor.obj X) z) : unitInterval) : ℝ)}

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem coneToSuspension_mem_suspensionUpper_iff
    (X : TopCat.{u}) (z : cone X) :
    coneToSuspension X z ∈ suspensionUpperSet X ↔ z ∈ coneLowerSet X := by
  have h := ConcreteCategory.congr_hom
    (coneToSuspension_mappingConeHeight X) z
  change mappingConeHeight (terminalArrowFunctor.obj X) (coneToSuspension X z) =
    I.symm (coneHeight X z) at h
  change (1 : ℝ) / 3 <
      ((I.homeomorph
        (mappingConeHeight (terminalArrowFunctor.obj X)
          (coneToSuspension X z)) : unitInterval) : ℝ) ↔
    ((I.homeomorph (coneHeight X z) : unitInterval) : ℝ) < 2 / 3
  rw [h, I.homeomorph_symm, unitInterval.coe_symm_eq]
  constructor <;> intro hz <;> linarith

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem coneToSuspension_mem_suspensionLower_iff
    (X : TopCat.{u}) (z : cone X) :
    coneToSuspension X z ∈ suspensionLowerSet X ↔ z ∈ coneUpperSet X := by
  have h := ConcreteCategory.congr_hom
    (coneToSuspension_mappingConeHeight X) z
  change mappingConeHeight (terminalArrowFunctor.obj X) (coneToSuspension X z) =
    I.symm (coneHeight X z) at h
  change ((I.homeomorph
      (mappingConeHeight (terminalArrowFunctor.obj X)
        (coneToSuspension X z)) : unitInterval) : ℝ) < 2 / 3 ↔
    (1 : ℝ) / 3 <
      ((I.homeomorph (coneHeight X z) : unitInterval) : ℝ)
  rw [h, I.homeomorph_symm, unitInterval.coe_symm_eq]
  constructor <;> intro hz <;> linarith

set_option backward.isDefEq.respectTransparency false in
/-- Away from the glued cone base, the cone summand identifies with the upper suspension
neighborhood. -/
noncomputable def coneUpperToSuspensionUpperHomeomorph (X : TopCat.{u}) :
    coneUpperSet X ≃ₜ suspensionUpperSet X := by
  let f := isTerminalPUnit.from X
  let g := coneBase X
  let i := pushout.inl f g
  let j := pushout.inr f g
  let U := suspensionUpperSet X
  have hU : IsOpen U :=
    isOpen_Ioi.preimage
      (continuous_subtype_val.comp
        (I.homeomorph.continuous.comp
          (mappingConeHeight (terminalArrowFunctor.obj X)).hom.continuous))
  have hi : i ⁻¹' U = ∅ := by
    ext p
    constructor
    · intro hp
      change (1 : ℝ) / 3 <
        ((I.homeomorph
          (mappingConeHeight (terminalArrowFunctor.obj X) (i p)) :
            unitInterval) : ℝ) at hp
      have hz := ConcreteCategory.congr_hom
        (mappingConeInclusion_mappingConeHeight
          (terminalArrowFunctor.obj X)) p
      change mappingConeHeight (terminalArrowFunctor.obj X) (i p) = 0 at hz
      rw [hz] at hp
      norm_num at hp
    · exact False.elim
  have hj : j ⁻¹' U = coneUpperSet X := by
    ext z
    change (1 : ℝ) / 3 <
        ((I.homeomorph
          (mappingConeHeight (terminalArrowFunctor.obj X) (j z)) :
            unitInterval) : ℝ) ↔
      (1 : ℝ) / 3 <
        ((I.homeomorph (coneHeight X z) : unitInterval) : ℝ)
    have hz :
        mappingConeHeight (terminalArrowFunctor.obj X) (j z) =
          coneHeight X z := by
      unfold j f g terminalArrowFunctor mappingConeHeight
      exact ConcreteCategory.congr_hom (pushout.inr_desc _ _ _) z
    rw [hz]
  have hbase : j ⁻¹' U ⊆ (Set.range g)ᶜ := by
    rw [hj]
    intro z hz hzg
    obtain ⟨x, rfl⟩ := hzg
    change (1 : ℝ) / 3 <
      ((I.homeomorph (coneHeight X (coneBase X x)) : unitInterval) : ℝ) at hz
    rw [← ConcreteCategory.comp_apply, coneBase_coneHeight] at hz
    norm_num [TopCat.const] at hz
  let h := isHomeomorph_restrictPreimage_inr_of_isPushout
    (IsPushout.of_hasPushout f g) hU hi hbase
  exact (Homeomorph.setCongr hj.symm).trans
    (h.homeomorph (U.restrictPreimage j))

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma coneUpperToSuspensionUpperHomeomorph_apply
    (X : TopCat.{u}) (z : coneUpperSet X) :
    (coneUpperToSuspensionUpperHomeomorph X z).1 =
      pushout.inr (isTerminalPUnit.from X) (coneBase X) z.1 := by
  unfold coneUpperToSuspensionUpperHomeomorph
  rfl

/-- The natural two-set height cover of a suspension, ordered with the
basepoint neighborhood first. -/
noncomputable def suspensionHeightCoverFunctor :
    TopCat.{u} ⥤ AlgebraicTopology.OrderedTwoSetCover.{u} where
  obj X :=
    { X := (suspensionFunctor.obj X).right
      left := suspensionUpperSet X
      right := suspensionLowerSet X
      interior_cover := by
        have hLower : IsOpen (suspensionLowerSet X) :=
          isOpen_Iio.preimage
            (continuous_subtype_val.comp
              (I.homeomorph.continuous.comp
                (mappingConeHeight (terminalArrowFunctor.obj X)).hom.continuous))
        have hUpper : IsOpen (suspensionUpperSet X) :=
          isOpen_Ioi.preimage
            (continuous_subtype_val.comp
              (I.homeomorph.continuous.comp
                (mappingConeHeight (terminalArrowFunctor.obj X)).hom.continuous))
        rw [hUpper.interior_eq, hLower.interior_eq]
        intro z _
        by_cases hz : ((I.homeomorph
            (mappingConeHeight (terminalArrowFunctor.obj X) z) : unitInterval) : ℝ) < 2 / 3
        · exact Set.mem_union_right _ hz
        · exact Set.mem_union_left _
            (lt_of_lt_of_le (by norm_num) (le_of_not_gt hz)) }
  map f :=
    { f := (suspensionFunctor.map f).right
      left_maps := by
        intro z hz
        change (1 : ℝ) / 3 < ((I.homeomorph
          (mappingConeHeight (terminalArrowFunctor.obj _)
            ((suspensionFunctor.map f).right z)) : unitInterval) : ℝ)
        have h := ConcreteCategory.congr_hom
          (mappingConeMap_mappingConeHeight (terminalArrowFunctor.map f)) z
        change mappingConeHeight (terminalArrowFunctor.obj _)
            ((suspensionFunctor.map f).right z) =
          mappingConeHeight (terminalArrowFunctor.obj _) z at h
        rw [h]
        exact hz
      right_maps := by
        intro z hz
        change ((I.homeomorph
          (mappingConeHeight (terminalArrowFunctor.obj _)
            ((suspensionFunctor.map f).right z)) : unitInterval) : ℝ) < 2 / 3
        have h := ConcreteCategory.congr_hom
          (mappingConeMap_mappingConeHeight (terminalArrowFunctor.map f)) z
        change mappingConeHeight (terminalArrowFunctor.obj _)
            ((suspensionFunctor.map f).right z) =
          mappingConeHeight (terminalArrowFunctor.obj _) z at h
        rw [h]
        exact hz }
  map_id X := by
    apply AlgebraicTopology.OrderedTwoSetCover.Hom.ext
    change (suspensionFunctor.map (𝟙 X)).right = 𝟙 _
    simp
  map_comp f g := by
    apply AlgebraicTopology.OrderedTwoSetCover.Hom.ext
    change (suspensionFunctor.map (f ≫ g)).right =
      (suspensionFunctor.map f).right ≫ (suspensionFunctor.map g).right
    simp

/-- The cone-to-suspension quotient is naturally a morphism between the height covers,
with the order reversed by the cone-coordinate reversal. -/
noncomputable def coneToSuspensionHeightCoverNatTrans :
    coneHeightCoverFunctor ⟶ suspensionHeightCoverFunctor where
  app X :=
    { f := coneToSuspension X
      left_maps := fun z hz =>
        (coneToSuspension_mem_suspensionUpper_iff X z).2 hz
      right_maps := fun z hz =>
        (coneToSuspension_mem_suspensionLower_iff X z).2 hz }
  naturality X Y f := by
    apply AlgebraicTopology.OrderedTwoSetCover.Hom.ext
    exact coneToSuspension_naturality f

/-- Reflection of the unreduced suspension, interchanging its two poles. -/
noncomputable def suspensionReflection (X : TopCat.{u}) :
    (suspensionFunctor.obj X).right ⟶ (suspensionFunctor.obj X).right :=
  pushout.desc (mappingConePoint (terminalArrowFunctor.obj X))
    (coneToSuspension X) (coneBase_coneToSuspension X).symm

@[reassoc (attr := simp)]
theorem mappingConeInclusion_suspensionReflection (X : TopCat.{u}) :
    pushout.inl (isTerminalPUnit.from X) (coneBase X) ≫
        suspensionReflection X =
      mappingConePoint (terminalArrowFunctor.obj X) := by
  exact pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem mappingConeInr_suspensionReflection (X : TopCat.{u}) :
    pushout.inr (isTerminalPUnit.from X) (coneBase X) ≫
        suspensionReflection X =
      coneToSuspension X := by
  exact pushout.inr_desc _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
theorem mappingConePoint_suspensionReflection (X : TopCat.{u}) :
    mappingConePoint (terminalArrowFunctor.obj X) ≫
        suspensionReflection X =
      pushout.inl (isTerminalPUnit.from X) (coneBase X) := by
  let j : cone X ⟶ mappingCone (terminalArrowFunctor.obj X) :=
    pushout.inr (isTerminalPUnit.from X) (coneBase X)
  let r : mappingCone (terminalArrowFunctor.obj X) ⟶
      mappingCone (terminalArrowFunctor.obj X) := suspensionReflection X
  change (conePoint X ≫ j) ≫ r = _
  rw [Category.assoc]
  have hj : j ≫ r = coneToSuspension X :=
    mappingConeInr_suspensionReflection X
  rw [hj]
  exact conePoint_coneToSuspension X

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem coneToSuspension_suspensionReflection (X : TopCat.{u}) :
    coneToSuspension X ≫ suspensionReflection X =
      pushout.inr (isTerminalPUnit.from X) (coneBase X) := by
  let S := mappingCone (terminalArrowFunctor.obj X)
  let q : cone X ⟶ S := coneToSuspension X
  let r : S ⟶ S := suspensionReflection X
  let j : cone X ⟶ S := pushout.inr (isTerminalPUnit.from X) (coneBase X)
  change q ≫ r = j
  apply pushout.hom_ext
  · have hq : coneCylinder X ≫ q =
        (X ◁ I.symm) ≫ coneCylinder X ≫ j :=
      coneCylinder_coneToSuspension X
    have hj : j ≫ r = q := mappingConeInr_suspensionReflection X
    change coneCylinder X ≫ (q ≫ r) = coneCylinder X ≫ j
    calc
      coneCylinder X ≫ (q ≫ r) =
          (coneCylinder X ≫ q) ≫ r := by simp only [Category.assoc]
      _ = ((X ◁ I.symm) ≫ coneCylinder X ≫ j) ≫ r := by rw [hq]
      _ = (X ◁ I.symm) ≫ coneCylinder X ≫ (j ≫ r) := by
        simp only [Category.assoc]
      _ = (X ◁ I.symm) ≫ coneCylinder X ≫ q := by rw [hj]
      _ = (X ◁ I.symm) ≫
          ((X ◁ I.symm) ≫ coneCylinder X ≫ j) := by rw [hq]
      _ = coneCylinder X ≫ j := by
        apply TopCat.hom_ext
        ext p
        rcases p with ⟨x, t⟩
        change j (coneCylinder X (x, I.symm (I.symm t))) =
          j (coneCylinder X (x, t))
        rw [show I.symm (I.symm t) = t by
          apply I.ext
          simp [I.homeomorph_symm]]
  · have hq : conePoint X ≫ q =
        pushout.inl (isTerminalPUnit.from X) (coneBase X) :=
      conePoint_coneToSuspension X
    have hi : pushout.inl (isTerminalPUnit.from X) (coneBase X) ≫ r =
        mappingConePoint (terminalArrowFunctor.obj X) :=
      mappingConeInclusion_suspensionReflection X
    change conePoint X ≫ (q ≫ r) = conePoint X ≫ j
    calc
      conePoint X ≫ (q ≫ r) = (conePoint X ≫ q) ≫ r := by
        simp only [Category.assoc]
      _ = pushout.inl (isTerminalPUnit.from X) (coneBase X) ≫ r := by rw [hq]
      _ = mappingConePoint (terminalArrowFunctor.obj X) := hi
      _ = conePoint X ≫ j := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem suspensionReflection_comp_self (X : TopCat.{u}) :
    suspensionReflection X ≫ suspensionReflection X = 𝟙 _ := by
  let S := mappingCone (terminalArrowFunctor.obj X)
  let r : S ⟶ S := suspensionReflection X
  let i : TopCat.of PUnit ⟶ S :=
    pushout.inl (isTerminalPUnit.from X) (coneBase X)
  let j : cone X ⟶ S := pushout.inr (isTerminalPUnit.from X) (coneBase X)
  change r ≫ r = 𝟙 S
  apply pushout.hom_ext
  · have hi : i ≫ r = mappingConePoint (terminalArrowFunctor.obj X) :=
      mappingConeInclusion_suspensionReflection X
    have hp : mappingConePoint (terminalArrowFunctor.obj X) ≫ r = i :=
      mappingConePoint_suspensionReflection X
    change i ≫ (r ≫ r) = i ≫ 𝟙 S
    rw [← Category.assoc, hi, hp, Category.comp_id]
  · have hj : j ≫ r = coneToSuspension X :=
      mappingConeInr_suspensionReflection X
    have hq : coneToSuspension X ≫ r = j :=
      coneToSuspension_suspensionReflection X
    change j ≫ (r ≫ r) = j ≫ 𝟙 S
    rw [← Category.assoc, hj, hq, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The cone-base quotient presentation of the suspension. -/
theorem coneToSuspension_isPushout (X : TopCat.{u}) :
    IsPushout (isTerminalPUnit.from X) (coneBase X)
      (suspensionFunctor.obj X).hom (coneToSuspension X) := by
  let rIso : (suspensionFunctor.obj X).right ≅
      (suspensionFunctor.obj X).right :=
    { hom := suspensionReflection X
      inv := suspensionReflection X
      hom_inv_id := suspensionReflection_comp_self X
      inv_hom_id := suspensionReflection_comp_self X }
  refine IsPushout.of_iso
    (IsPushout.of_hasPushout (isTerminalPUnit.from X) (coneBase X))
    (Iso.refl X) (Iso.refl (TopCat.of PUnit)) (Iso.refl (cone X)) rIso
    ?_ ?_ ?_ ?_
  · simp
  · simp
  · exact mappingConeInclusion_suspensionReflection X
  · exact mappingConeInr_suspensionReflection X

theorem suspensionReflection_involutive (X : TopCat.{u}) :
    Function.Involutive (suspensionReflection X) := by
  intro z
  have h := ConcreteCategory.congr_hom (suspensionReflection_comp_self X) z
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Suspension reflection is natural in the suspended space. -/
@[reassoc]
theorem suspensionReflection_naturality {X Y : TopCat.{u}} (f : X ⟶ Y) :
    suspensionReflection X ≫ (suspensionFunctor.map f).right =
      (suspensionFunctor.map f).right ≫ suspensionReflection Y := by
  let SX := mappingCone (terminalArrowFunctor.obj X)
  let SY := mappingCone (terminalArrowFunctor.obj Y)
  let rX : SX ⟶ SX := suspensionReflection X
  let rY : SY ⟶ SY := suspensionReflection Y
  let m : SX ⟶ SY := mappingConeMap (terminalArrowFunctor.map f)
  let iX : TopCat.of PUnit ⟶ SX :=
    pushout.inl (isTerminalPUnit.from X) (coneBase X)
  let jX : cone X ⟶ SX := pushout.inr (isTerminalPUnit.from X) (coneBase X)
  change rX ≫ m = m ≫ rY
  apply pushout.hom_ext
  · have hir : iX ≫ rX = mappingConePoint (terminalArrowFunctor.obj X) :=
      mappingConeInclusion_suspensionReflection X
    have hpm : mappingConePoint (terminalArrowFunctor.obj X) ≫ m =
        mappingConePoint (terminalArrowFunctor.obj Y) :=
      mappingConePoint_naturality (terminalArrowFunctor.map f)
    have him : iX ≫ m =
        pushout.inl (isTerminalPUnit.from Y) (coneBase Y) := by
      have h := mappingConeMap_inl (terminalArrowFunctor.map f)
      change iX ≫ m = (𝟙 (TopCat.of PUnit)) ≫
        pushout.inl (isTerminalPUnit.from Y) (coneBase Y) at h
      simpa using h
    have hirY : pushout.inl (isTerminalPUnit.from Y) (coneBase Y) ≫ rY =
        mappingConePoint (terminalArrowFunctor.obj Y) :=
      mappingConeInclusion_suspensionReflection Y
    change iX ≫ (rX ≫ m) = iX ≫ (m ≫ rY)
    rw [← Category.assoc, hir, hpm, ← Category.assoc, him, hirY]
  · have hjr : jX ≫ rX = coneToSuspension X :=
      mappingConeInr_suspensionReflection X
    have hqm : coneToSuspension X ≫ m =
        coneMap f ≫ coneToSuspension Y :=
      (coneToSuspension_naturality f).symm
    have hjm : jX ≫ m =
        coneMap f ≫ pushout.inr (isTerminalPUnit.from Y) (coneBase Y) :=
      mappingConeMap_inr (terminalArrowFunctor.map f)
    have hjrY : pushout.inr (isTerminalPUnit.from Y) (coneBase Y) ≫ rY =
        coneToSuspension Y := mappingConeInr_suspensionReflection Y
    change jX ≫ (rX ≫ m) = jX ≫ (m ≫ rY)
    rw [← Category.assoc, hjr, hqm, ← Category.assoc, hjm,
      Category.assoc, hjrY]

/-- Reflection as a natural automorphism of the underlying-space-valued suspension functor. -/
noncomputable def suspensionReflectionNatIso :
    suspensionFunctor ⋙ Under.forget (TopCat.of PUnit) ≅
      suspensionFunctor ⋙ Under.forget (TopCat.of PUnit) :=
  NatIso.ofComponents
    (fun X =>
      { hom := suspensionReflection X
        inv := suspensionReflection X
        hom_inv_id := suspensionReflection_comp_self X
        inv_hom_id := suspensionReflection_comp_self X })
    (fun f => (suspensionReflection_naturality f).symm)

@[simp]
theorem suspensionReflectionNatIso_hom_app (X : TopCat.{u}) :
    suspensionReflectionNatIso.hom.app X = suspensionReflection X := rfl

@[simp]
theorem suspensionReflectionNatIso_inv_app (X : TopCat.{u}) :
    suspensionReflectionNatIso.inv.app X = suspensionReflection X := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Suspension reflection reverses the suspension height. -/
@[reassoc]
theorem suspensionReflection_mappingConeHeight (X : TopCat.{u}) :
    suspensionReflection X ≫
        mappingConeHeight (terminalArrowFunctor.obj X) =
      mappingConeHeight (terminalArrowFunctor.obj X) ≫ I.symm := by
  let S := mappingCone (terminalArrowFunctor.obj X)
  let r : S ⟶ S := suspensionReflection X
  let h : S ⟶ I := mappingConeHeight (terminalArrowFunctor.obj X)
  let i : TopCat.of PUnit ⟶ S :=
    pushout.inl (isTerminalPUnit.from X) (coneBase X)
  let j : cone X ⟶ S := pushout.inr (isTerminalPUnit.from X) (coneBase X)
  change r ≫ h = h ≫ I.symm
  apply pushout.hom_ext
  · have hir : i ≫ r = mappingConePoint (terminalArrowFunctor.obj X) :=
      mappingConeInclusion_suspensionReflection X
    have hph : mappingConePoint (terminalArrowFunctor.obj X) ≫ h = TopCat.const 1 :=
      mappingConePoint_mappingConeHeight (terminalArrowFunctor.obj X)
    have hih : i ≫ h = TopCat.const 0 :=
      mappingConeInclusion_mappingConeHeight (terminalArrowFunctor.obj X)
    change i ≫ (r ≫ h) = i ≫ (h ≫ I.symm)
    rw [← Category.assoc, hir, hph, ← Category.assoc, hih]
    apply TopCat.hom_ext
    ext p
    norm_num [TopCat.const]
  · have hjr : j ≫ r = coneToSuspension X :=
      mappingConeInr_suspensionReflection X
    have hqh : coneToSuspension X ≫ h = coneHeight X ≫ I.symm :=
      coneToSuspension_mappingConeHeight X
    have hjh : j ≫ h = coneHeight X := by
      unfold h j mappingConeHeight
      exact pushout.inr_desc _ _ _
    change j ≫ (r ≫ h) = j ≫ (h ≫ I.symm)
    rw [← Category.assoc, hjr, hqh, ← Category.assoc, hjh]

end TopCat

namespace TopPair

open AlgebraicTopology AlgebraicTopology.OrderedTwoSetCover

/-- The cone base mapped into the lower height neighborhood. -/
noncomputable def coneBaseToLower (X : TopCat.{u}) :
    X ⟶ TopCat.of (TopCat.coneLowerSet X) :=
  TopCat.ofHom
    { toFun := fun x => ⟨TopCat.coneBase X x, by
        change ((TopCat.I.homeomorph
          (TopCat.coneHeight X (TopCat.coneBase X x)) : unitInterval) : ℝ) < 2 / 3
        rw [← ConcreteCategory.comp_apply, TopCat.coneBase_coneHeight]
        norm_num [TopCat.const]⟩
      continuous_toFun := by fun_prop }

/-- The cone/base pair includes naturally into the lower member of the cone height cover. -/
noncomputable def conePairToHeightCoverNatTrans :
    TopCat.pointedConeTripleFunctor ⋙ topTriplePair12 ⟶
      Under.forget (TopCat.of PUnit) ⋙ TopCat.coneHeightCoverFunctor ⋙
        spaceLeftPairFunctor where
  app X := TopPair.ofHom (𝟙 _) (coneBaseToLower X.right) (by
    apply TopCat.hom_ext
    ext x
    rfl)
  naturality X Y f := by
    apply MorphismProperty.Arrow.Hom.ext
    · change f.right ≫ coneBaseToLower Y.right =
        coneBaseToLower X.right ≫
          AlgebraicTopology.subspaceMap (TopCat.coneMap f.right)
            (TopCat.coneHeightCoverFunctor.map f.right).left_maps
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      apply Subtype.ext
      exact (ConcreteCategory.congr_hom (TopCat.coneBase_naturality f.right) x).symm
    · simp only [Functor.comp_obj, Functor.comp_map]
      apply TopCat.hom_ext
      ext x
      rfl

/-- The suspension basepoint mapped into the upper height neighborhood. -/
noncomputable def suspensionPointToUpper (X : TopCat.{u}) :
    TopCat.of PUnit ⟶ TopCat.of (TopCat.suspensionUpperSet X) :=
  TopCat.ofHom
    { toFun := fun x =>
      ⟨TopCat.mappingConePoint (TopCat.terminalArrowFunctor.obj X) x, by
        change (1 : ℝ) / 3 < ((TopCat.I.homeomorph
          (TopCat.mappingConeHeight (TopCat.terminalArrowFunctor.obj X)
            (TopCat.mappingConePoint (TopCat.terminalArrowFunctor.obj X) x)) :
              unitInterval) : ℝ)
        rw [← ConcreteCategory.comp_apply]
        rw [TopCat.mappingConePoint_mappingConeHeight]
        norm_num [TopCat.const]⟩
      continuous_toFun := by fun_prop }

/-- The pointed suspension pair includes naturally into the upper member of the suspension
height cover. -/
noncomputable def suspensionPairToHeightCoverNatTrans :
    Under.forget (TopCat.of PUnit) ⋙ TopCat.suspensionFunctor ⋙
        PointedTopCat.pointedPair ⟶
      Under.forget (TopCat.of PUnit) ⋙ TopCat.suspensionHeightCoverFunctor ⋙
        spaceLeftPairFunctor where
  app X := TopPair.ofHom (𝟙 _) (suspensionPointToUpper X.right) (by
    apply TopCat.hom_ext
    ext x
    rfl)
  naturality X Y f := by
    apply MorphismProperty.Arrow.Hom.ext
    · change suspensionPointToUpper Y.right =
        suspensionPointToUpper X.right ≫
          AlgebraicTopology.subspaceMap (TopCat.suspensionFunctor.map f.right).right
            (TopCat.suspensionHeightCoverFunctor.map f.right).left_maps
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro x
      apply Subtype.ext
      cases x
      exact (ConcreteCategory.congr_hom
        (TopCat.mappingConePoint_naturality (TopCat.terminalArrowFunctor.map f.right))
        PUnit.unit).symm
    · simp only [Functor.comp_obj, Functor.comp_map]
      apply TopCat.hom_ext
      ext x
      rfl

/-- The cone/base pair maps naturally to the pointed suspension pair. -/
noncomputable def conePairToSuspensionPairNatTrans :
    TopCat.pointedConeTripleFunctor ⋙ topTriplePair12 ⟶
      Under.forget (TopCat.of PUnit) ⋙ TopCat.suspensionFunctor ⋙
        PointedTopCat.pointedPair where
  app X := TopPair.ofHom (TopCat.coneToSuspension X.right)
    (TopCat.isTerminalPUnit.from X.right)
    (TopCat.coneBase_coneToSuspension X.right).symm
  naturality X Y f := by
    apply MorphismProperty.Arrow.Hom.ext
    · apply TopCat.isTerminalPUnit.hom_ext
    · exact TopCat.coneToSuspension_naturality f.right

end TopPair

namespace TopCat

open MonoidalCategory

/-- Below the cone apex, the cone-cylinder quotient restricts to a homeomorphism. -/
noncomputable def coneLowerCylinderHomeomorph (X : TopCat.{u}) [Nonempty X] :
    ((coneCylinder X).hom ⁻¹' coneLowerSet X) ≃ₜ coneLowerSet X := by
  classical
  let q := (coneLowerSet X).restrictPreimage (coneCylinder X).hom
  have hOpen : IsOpen (coneLowerSet X) :=
    isOpen_Iio.preimage
      (continuous_subtype_val.comp
        (I.homeomorph.continuous.comp (coneHeight X).hom.continuous))
  have hq : Topology.IsQuotientMap q :=
    (coneCylinder_isQuotientMap X).restrictPreimage_isOpen hOpen
  have hi : Function.Injective q := by
    intro p r hpr
    apply Subtype.ext
    have hp : (CartesianMonoidalCategory.snd X I) p.1 ≠ 1 := by
      intro hp
      have hm := p.property
      change ((I.homeomorph (coneHeight X (coneCylinder X p.1)) : unitInterval) : ℝ) <
        2 / 3 at hm
      rw [← ConcreteCategory.comp_apply, coneCylinder_coneHeight] at hm
      rw [hp] at hm
      norm_num at hm
    have hr : (CartesianMonoidalCategory.snd X I) r.1 ≠ 1 := by
      intro hr
      have hm := r.property
      change ((I.homeomorph (coneHeight X (coneCylinder X r.1)) : unitInterval) : ℝ) <
        2 / 3 at hm
      rw [← ConcreteCategory.comp_apply, coneCylinder_coneHeight] at hm
      rw [hr] at hm
      norm_num at hm
    have ht : (CartesianMonoidalCategory.snd X I) p.1 =
        (CartesianMonoidalCategory.snd X I) r.1 := by
      have hh := congrArg (fun z : coneLowerSet X => coneHeight X z.1) hpr
      change coneHeight X (coneCylinder X p.1) =
        coneHeight X (coneCylinder X r.1) at hh
      simpa only [← ConcreteCategory.comp_apply, coneCylinder_coneHeight] using hh
    let _ : TopologicalSpace (Option X) := ⊤
    let cylinderLabel : X ⊗ I ⟶ TopCat.of (Option X) :=
      TopCat.ofHom ⟨fun s =>
        if (CartesianMonoidalCategory.snd X I) s = 1 then none
        else some ((CartesianMonoidalCategory.fst X I) s),
        continuous_of_indiscreteTopology⟩
    let pointLabel : TopCat.of PUnit ⟶ TopCat.of (Option X) :=
      TopCat.ofHom ⟨fun _ => none, continuous_of_indiscreteTopology⟩
    have hcompat : ι₁ ≫ cylinderLabel = isTerminalPUnit.from X ≫ pointLabel := by
      apply ConcreteCategory.hom_ext
      intro x
      change (if (1 : I) = 1 then none else some x) = none
      simp
    let label : cone X ⟶ TopCat.of (Option X) :=
      pushout.desc cylinderLabel pointLabel hcompat
    have hl0 := congrArg (fun z : coneLowerSet X => label z.1) hpr
    change label (coneCylinder X p.1) = label (coneCylinder X r.1) at hl0
    have hl : cylinderLabel p.1 = cylinderLabel r.1 := by
      calc
        cylinderLabel p.1 = label (coneCylinder X p.1) := by
          symm
          exact ConcreteCategory.congr_hom (pushout.inl_desc _ _ _) p.1
        _ = label (coneCylinder X r.1) := hl0
        _ = cylinderLabel r.1 := ConcreteCategory.congr_hom (pushout.inl_desc _ _ _) r.1
    have hx : (CartesianMonoidalCategory.fst X I) p.1 =
        (CartesianMonoidalCategory.fst X I) r.1 := by
      change (if (CartesianMonoidalCategory.snd X I) p.1 = 1 then none
        else some ((CartesianMonoidalCategory.fst X I) p.1)) =
        (if (CartesianMonoidalCategory.snd X I) r.1 = 1 then none
        else some ((CartesianMonoidalCategory.fst X I) r.1)) at hl
      simp only [hp, hr, ↓reduceIte] at hl
      exact Option.some.inj hl
    exact Prod.ext hx ht
  exact (isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hq, hi⟩).homeomorph q

@[simp]
lemma coneLowerCylinderHomeomorph_apply (X : TopCat.{u}) [Nonempty X]
    (p : (coneCylinder X).hom ⁻¹' coneLowerSet X) :
    (coneLowerCylinderHomeomorph X p).1 = coneCylinder X p.1 := by
  simp only [coneLowerCylinderHomeomorph, IsHomeomorph.homeomorph_apply]
  rfl

/-- Projection of the lower cone neighborhood onto its base. -/
noncomputable def coneLowerProjection (X : TopCat.{u}) [Nonempty X] :
    TopCat.of (coneLowerSet X) ⟶ X :=
  TopCat.ofHom
    { toFun := fun z =>
        (CartesianMonoidalCategory.fst X I) ((coneLowerCylinderHomeomorph X).symm z).1
      continuous_toFun := by fun_prop }

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma coneBaseToLower_coneLowerProjection (X : TopCat.{u}) [Nonempty X] :
    TopPair.coneBaseToLower X ≫ coneLowerProjection X = 𝟙 X := by
  apply TopCat.ext
  intro x
  let p : (coneCylinder X).hom ⁻¹' coneLowerSet X :=
    ⟨(x, (0 : I)), by
      change ((I.homeomorph (coneHeight X (coneCylinder X (x, (0 : I)))) :
        unitInterval) : ℝ) < 2 / 3
      rw [← ConcreteCategory.comp_apply, coneCylinder_coneHeight]
      change ((0 : unitInterval) : ℝ) < 2 / 3
      norm_num⟩
  have hp : coneLowerCylinderHomeomorph X p = TopPair.coneBaseToLower X x := by
    apply Subtype.ext
    simp only [coneLowerCylinderHomeomorph_apply]
    change coneCylinder X (x, (0 : I)) = coneBase X x
    rfl
  change (CartesianMonoidalCategory.fst X I)
      ((coneLowerCylinderHomeomorph X).symm (TopPair.coneBaseToLower X x)).1 = x
  rw [← hp, (coneLowerCylinderHomeomorph X).symm_apply_apply]
  rfl

private noncomputable def coneLowerCollapse : I.{u} ⟶ I :=
  TopCat.ofHom
    { toFun := fun t => I.homeomorph.symm
        ⟨max 0 (3 * (I.homeomorph t : ℝ) - 2), by
          constructor
          · exact le_max_left _ _
          · apply max_le
            · norm_num
            · have ht := (I.homeomorph t).property.2
              linarith⟩
      continuous_toFun := by fun_prop }

@[simp]
private lemma coneLowerCollapse_homeomorph_coe (t : I.{u}) :
    ((I.homeomorph (coneLowerCollapse t) : unitInterval) : ℝ) =
      max 0 (3 * ((I.homeomorph t : unitInterval) : ℝ) - 2) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
private lemma coneLowerCollapse_one : coneLowerCollapse (1 : I.{u}) = 1 := by
  apply I.ext
  apply Subtype.ext
  simp
  norm_num

set_option backward.isDefEq.respectTransparency false in
private lemma coneLowerCollapse_eq_zero_of_lt_two_thirds (t : I.{u})
    (ht : ((I.homeomorph t : unitInterval) : ℝ) < 2 / 3) :
    coneLowerCollapse t = 0 := by
  apply I.ext
  apply Subtype.ext
  simp only [coneLowerCollapse_homeomorph_coe, I.homeomorph_zero]
  have hle : 3 * ((I.homeomorph t : unitInterval) : ℝ) - 2 ≤ 0 := by
    linarith
  exact max_eq_left hle

set_option backward.isDefEq.respectTransparency false in
private noncomputable def coneLowerCollapseHomotopy :
    TopCat.Homotopy (𝟙 I.{u}) coneLowerCollapse :=
  { toFun := fun p => I.homeomorph.symm
      ⟨max 0
          ((1 + 2 * (p.1 : ℝ)) * ((I.homeomorph p.2 : unitInterval) : ℝ) -
            2 * (p.1 : ℝ)), by
        constructor
        · exact le_max_left _ _
        · apply max_le
          · norm_num
          · have hs₀ := p.1.property.1
            have hs₁ := p.1.property.2
            have ht₁ := (I.homeomorph p.2).property.2
            have hmul : 2 * (p.1 : ℝ) *
                (((I.homeomorph p.2 : unitInterval) : ℝ) - 1) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr ht₁)
            nlinarith⟩
    continuous_toFun := by fun_prop
    map_zero_left := by
      intro t
      apply I.ext
      apply Subtype.ext
      simp only [Set.Icc.coe_zero, mul_zero, add_zero, one_mul, sub_zero,
        Homeomorph.apply_symm_apply, hom_id, ContinuousMap.id_apply, sup_eq_right]
      exact (I.homeomorph t).property.1
    map_one_left := by
      intro t
      apply I.ext
      apply Subtype.ext
      change max 0 ((1 + 2 * (1 : ℝ)) *
          ((I.homeomorph t : unitInterval) : ℝ) - 2 * (1 : ℝ)) =
        max 0 (3 * ((I.homeomorph t : unitInterval) : ℝ) - 2)
      ring_nf }

set_option backward.isDefEq.respectTransparency false in
private lemma coneLowerCollapseHomotopy_one_right (s : unitInterval) :
    coneLowerCollapseHomotopy (s, (1 : I.{u})) = 1 := by
  apply I.ext
  apply Subtype.ext
  change max 0 ((1 + 2 * (s : ℝ)) * (1 : ℝ) - 2 * (s : ℝ)) = 1
  ring_nf
  norm_num

set_option backward.isDefEq.respectTransparency false in
private lemma coneLowerCollapseHomotopy_lt_two_thirds (s : unitInterval) (t : I.{u})
    (ht : ((I.homeomorph t : unitInterval) : ℝ) < 2 / 3) :
    ((I.homeomorph (coneLowerCollapseHomotopy (s, t)) : unitInterval) : ℝ) < 2 / 3 := by
  change max 0
      ((1 + 2 * (s : ℝ)) * ((I.homeomorph t : unitInterval) : ℝ) - 2 * (s : ℝ)) <
    2 / 3
  exact max_lt (by norm_num) (by
    have hs₀ := s.property.1
    have hs₁ := s.property.2
    have ht₁ := (I.homeomorph t).property.2
    have hmul : 2 * (s : ℝ) * (((I.homeomorph t : unitInterval) : ℝ) - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr ht₁)
    nlinarith)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private lemma coneLowerProjection_coneBase (X : TopCat.{u}) [Nonempty X] :
    coneLowerProjection X ≫ coneBase X =
      AlgebraicTopology.subspaceIncl (coneLowerSet X) ≫
        coneReparam X coneLowerCollapse coneLowerCollapse_one := by
  apply TopCat.ext
  intro z
  let p := (coneLowerCylinderHomeomorph X).symm z
  have hp : coneLowerCylinderHomeomorph X p = z :=
    (coneLowerCylinderHomeomorph X).apply_symm_apply z
  have hpval : coneCylinder X p.1 = z.1 := by
    have h := congrArg Subtype.val hp
    simpa only [coneLowerCylinderHomeomorph_apply] using h
  have hlt : ((I.homeomorph
      ((CartesianMonoidalCategory.snd X I) p.1) : unitInterval) : ℝ) < 2 / 3 := by
    have hm := p.property
    change ((I.homeomorph (coneHeight X (coneCylinder X p.1)) : unitInterval) : ℝ) <
      2 / 3 at hm
    rw [← ConcreteCategory.comp_apply, coneCylinder_coneHeight] at hm
    exact hm
  change coneBase X ((CartesianMonoidalCategory.fst X I) p.1) =
    coneReparam X coneLowerCollapse coneLowerCollapse_one z.1
  rw [← hpval]
  have hcollapse := coneLowerCollapse_eq_zero_of_lt_two_thirds
    ((CartesianMonoidalCategory.snd X I) p.1) hlt
  have hreparam := ConcreteCategory.congr_hom
    (coneCylinder_coneReparam X coneLowerCollapse coneLowerCollapse_one) p.1
  have hreparam' :
      coneReparam X coneLowerCollapse coneLowerCollapse_one (coneCylinder X p.1) =
        coneCylinder X (p.1.1, coneLowerCollapse p.1.2) := by
    simpa only [ConcreteCategory.comp_apply, TopCat.whiskerLeft_apply] using hreparam
  rw [hreparam']
  have hcollapse' : coneLowerCollapse p.1.2 = 0 := hcollapse
  change coneBase X p.1.1 = coneCylinder X (p.1.1, coneLowerCollapse p.1.2)
  rw [hcollapse']
  rfl

private lemma coneId_one : ((𝟙 I.{u} : I ⟶ I) 1) = 1 := rfl

private lemma coneReparam_id (X : TopCat.{u}) [Nonempty X] :
    coneReparam X (𝟙 I) coneId_one = 𝟙 (cone X) := by
  apply pushout.hom_ext
  · change coneCylinder X ≫ coneReparam X (𝟙 I) coneId_one =
      coneCylinder X ≫ 𝟙 (cone X)
    rw [coneCylinder_coneReparam]
    apply TopCat.hom_ext
    ext p
    rfl
  · change conePoint X ≫ coneReparam X (𝟙 I) coneId_one =
      conePoint X ≫ 𝟙 (cone X)
    rw [conePoint_coneReparam]
    simp

/-- The lower cone neighborhood deformation retracts onto the cone base. -/
noncomputable opaque coneLowerDeformationHomotopy (X : TopCat.{u}) [Nonempty X] :
    TopCat.Homotopy (𝟙 (TopCat.of (coneLowerSet X)))
      (coneLowerProjection X ≫ TopPair.coneBaseToLower X) := by
  let H := coneReparamHomotopy X coneLowerCollapseHomotopy coneId_one
    coneLowerCollapse_one coneLowerCollapseHomotopy_one_right
  refine
    { toFun := fun p => ⟨H (p.1, p.2.1), ?_⟩
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_ }
  · let q := (coneLowerCylinderHomeomorph X).symm p.2
    have hq : coneCylinder X q.1 = p.2.1 := by
      have h := congrArg Subtype.val ((coneLowerCylinderHomeomorph X).apply_symm_apply p.2)
      simpa only [coneLowerCylinderHomeomorph_apply] using h
    have hlt : ((I.homeomorph
        ((CartesianMonoidalCategory.snd X I) q.1) : unitInterval) : ℝ) < 2 / 3 := by
      have hm := q.property
      change ((I.homeomorph (coneHeight X (coneCylinder X q.1)) : unitInterval) : ℝ) <
        2 / 3 at hm
      rw [← ConcreteCategory.comp_apply, coneCylinder_coneHeight] at hm
      exact hm
    change ((I.homeomorph (coneHeight X (H (p.1, p.2.1))) : unitInterval) : ℝ) < 2 / 3
    rw [← hq]
    change ((I.homeomorph
      (coneHeight X (coneReparamHomotopy X coneLowerCollapseHomotopy coneId_one
        coneLowerCollapse_one coneLowerCollapseHomotopy_one_right
          (p.1, coneCylinder X q.1))) : unitInterval) : ℝ) < 2 / 3
    rw [coneReparamHomotopy_apply_coneCylinder]
    let r : ↑(X ⊗ I) := (q.1.1, coneLowerCollapseHomotopy (p.1, q.1.2))
    have hr := ConcreteCategory.congr_hom (coneCylinder_coneHeight X) r
    change ((I.homeomorph (coneHeight X (coneCylinder X r)) : unitInterval) : ℝ) < 2 / 3
    have hr' : coneHeight X (coneCylinder X r) = r.2 := hr.trans rfl
    rw [hr']
    exact coneLowerCollapseHomotopy_lt_two_thirds p.1 q.1.2 hlt
  · apply Continuous.subtype_mk
      (H.continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  · intro z
    apply Subtype.ext
    change H (0, z.1) = z.1
    rw [ContinuousMap.Homotopy.apply_zero]
    rw [coneReparam_id]
    rfl
  · intro z
    apply Subtype.ext
    change H (1, z.1) = coneBase X (coneLowerProjection X z)
    rw [ContinuousMap.Homotopy.apply_one]
    exact (ConcreteCategory.congr_hom (coneLowerProjection_coneBase X) z).symm

/-- The cone base is homotopy equivalent to the lower cone neighborhood. -/
noncomputable def coneBaseToLowerHomotopyEquiv (X : TopCat.{u}) [Nonempty X] :
    ContinuousMap.HomotopyEquiv X (TopCat.of (coneLowerSet X)) where
  toFun := (TopPair.coneBaseToLower X).hom
  invFun := (coneLowerProjection X).hom
  left_inv := by
    have h := congrArg TopCat.Hom.hom (coneBaseToLower_coneLowerProjection X)
    rw [show (coneLowerProjection X).hom.comp (TopPair.coneBaseToLower X).hom =
        ContinuousMap.id X from h]
  right_inv := ⟨(coneLowerDeformationHomotopy X).symm⟩

@[simp]
lemma coneBaseToLowerHomotopyEquiv_toFun (X : TopCat.{u}) [Nonempty X] :
    TopCat.ofHom (coneBaseToLowerHomotopyEquiv X).toFun =
      TopPair.coneBaseToLower X := rfl

@[simp]
lemma coneBaseToLowerHomotopyEquiv_invFun (X : TopCat.{u}) [Nonempty X] :
    TopCat.ofHom (coneBaseToLowerHomotopyEquiv X).invFun =
      coneLowerProjection X := rfl

/-- The cone apex mapped into its upper height neighborhood. -/
noncomputable def conePointToUpper (X : TopCat.{u}) :
    TopCat.of PUnit ⟶ TopCat.of (coneUpperSet X) :=
  TopCat.ofHom
    { toFun := fun p => ⟨conePoint X p, by
        change (1 : ℝ) / 3 <
          ((I.homeomorph (coneHeight X (conePoint X p)) : unitInterval) : ℝ)
        rw [← ConcreteCategory.comp_apply, conePoint_coneHeight]
        norm_num [TopCat.const]⟩
      continuous_toFun := by fun_prop }

/-- The upper cone neighborhood deformation retracts onto the cone apex. -/
noncomputable opaque coneUpperDeformationHomotopy
    (X : TopCat.{u}) [Nonempty X] :
    TopCat.Homotopy (𝟙 (TopCat.of (coneUpperSet X)))
      (isTerminalPUnit.from (TopCat.of (coneUpperSet X)) ≫
        conePointToUpper X) := by
  let H := coneContractingHomotopy X
  refine
    { toFun := fun p => ⟨H (p.1, p.2.1), ?_⟩
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_ }
  · change (1 : ℝ) / 3 <
      ((I.homeomorph (coneHeight X (H (p.1, p.2.1))) : unitInterval) : ℝ)
    rw [coneContractingHomotopy_coneHeight]
    rw [I.homeomorph.apply_symm_apply]
    exact lt_of_lt_of_le p.2.property
      (Set.Icc.le_convexComb (I.homeomorph (coneHeight X p.2.1)).property.2 p.1)
  · apply Continuous.subtype_mk
      (H.continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  · intro z
    apply Subtype.ext
    change H (0, z.1) = z.1
    rw [ContinuousMap.Homotopy.apply_zero]
    rfl
  · intro z
    apply Subtype.ext
    change H (1, z.1) = conePoint X PUnit.unit
    rw [ContinuousMap.Homotopy.apply_one]
    rfl

noncomputable instance contractibleSpace_coneUpperSet
    (X : TopCat.{u}) [Nonempty X] :
    ContractibleSpace (coneUpperSet X) := by
  rw [contractible_iff_id_nullhomotopic]
  let p : coneUpperSet X := ⟨conePoint X PUnit.unit, by
    change (1 : ℝ) / 3 <
      ((I.homeomorph (coneHeight X (conePoint X PUnit.unit)) : unitInterval) : ℝ)
    rw [← ConcreteCategory.comp_apply, conePoint_coneHeight]
    norm_num [TopCat.const]⟩
  refine ⟨p, ⟨?_⟩⟩
  let H := coneUpperDeformationHomotopy X
  exact ContinuousMap.Homotopy.cast H
    rfl (by
      apply ContinuousMap.ext
      intro z
      apply Subtype.ext
      rfl)

noncomputable instance contractibleSpace_suspensionUpperSet
    (X : TopCat.{u}) [Nonempty X] :
    ContractibleSpace (suspensionUpperSet X) :=
  (coneUpperToSuspensionUpperHomeomorph X).symm.contractibleSpace

/-- The suspension basepoint is a homotopy equivalence onto its upper height neighborhood. -/
noncomputable def suspensionPointToUpperHomotopyEquiv
    (X : TopCat.{u}) [Nonempty X] :
    ContinuousMap.HomotopyEquiv PUnit (suspensionUpperSet X) :=
  ContinuousMap.HomotopyEquiv.ofContractible
    (TopPair.suspensionPointToUpper X).hom

@[simp]
lemma suspensionPointToUpperHomotopyEquiv_toFun
    (X : TopCat.{u}) [Nonempty X] :
    TopCat.ofHom (suspensionPointToUpperHomotopyEquiv X).toFun =
      TopPair.suspensionPointToUpper X := rfl

@[simp]
lemma suspensionPointToUpperHomotopyEquiv_invFun
    (X : TopCat.{u}) [Nonempty X] :
    TopCat.ofHom (suspensionPointToUpperHomotopyEquiv X).invFun =
      isTerminalPUnit.from (TopCat.of (suspensionUpperSet X)) := by
  apply isTerminalPUnit.hom_ext

end TopCat
