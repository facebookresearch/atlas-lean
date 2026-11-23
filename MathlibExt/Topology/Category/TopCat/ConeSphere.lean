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
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Cones on unit spheres

This file defines the radial map from the topological cone on a unit sphere
to the corresponding closed unit ball and records its values on the cylinder
and cone point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

universe u

namespace TopCat

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial coordinates from the cylinder on the unit sphere to the closed unit ball.
The cone coordinate `0` is the sphere boundary and coordinate `1` is the origin. -/
def unitSphereConeCylinderMap :
    TopCat.of (Metric.sphere (0 : E) 1) ⊗ TopCat.I ⟶
      TopCat.of (Metric.closedBall (0 : E) 1) :=
  TopCat.ofHom
    { toFun := fun p ↦
        ⟨(1 - (TopCat.I.homeomorph p.2).1) • p.1.1, by
          rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
            Real.norm_eq_abs, norm_eq_of_mem_sphere p.1]
          have ht0 : 0 ≤ (TopCat.I.homeomorph p.2).1 :=
            (TopCat.I.homeomorph p.2).property.1
          have ht1 : (TopCat.I.homeomorph p.2).1 ≤ 1 :=
            (TopCat.I.homeomorph p.2).property.2
          rw [abs_of_nonneg (sub_nonneg.mpr ht1), mul_one]
          linarith⟩
      continuous_toFun := by fun_prop }

@[reassoc (attr := simp)]
theorem ι₁_unitSphereConeCylinderMap :
    (TopCat.ι₁ : TopCat.of (Metric.sphere (0 : E) 1) ⟶
        TopCat.of (Metric.sphere (0 : E) 1) ⊗ TopCat.I) ≫
        unitSphereConeCylinderMap E =
      TopCat.isTerminalPUnit.from _ ≫
        TopCat.ofHom (ContinuousMap.const _ ⟨0, by simp⟩) := by
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  change (1 - (TopCat.I.homeomorph (1 : TopCat.I.{u})).1) • x.1 = 0
  simp

/-- The radial cylinder map descends through the cone quotient. -/
def unitSphereConeMap :
    TopCat.cone (TopCat.of (Metric.sphere (0 : E) 1)) ⟶
      TopCat.of (Metric.closedBall (0 : E) 1) :=
  pushout.desc (unitSphereConeCylinderMap E)
    (TopCat.ofHom (ContinuousMap.const _ ⟨0, by simp⟩))
    (ι₁_unitSphereConeCylinderMap E)

@[reassoc (attr := simp)]
theorem coneCylinder_unitSphereConeMap :
    coneCylinder (TopCat.of (Metric.sphere (0 : E) 1)) ≫
        unitSphereConeMap E =
      unitSphereConeCylinderMap E :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem conePoint_unitSphereConeMap :
    conePoint (TopCat.of (Metric.sphere (0 : E) 1)) ≫
        unitSphereConeMap E =
      TopCat.ofHom (ContinuousMap.const _ ⟨0, by simp⟩) :=
  pushout.inr_desc _ _ _

/-- Every nonzero point of the closed unit ball has radial cylinder coordinates. -/
theorem exists_unitSphereConeCylinderMap_eq_of_ne_zero
    (y : Metric.closedBall (0 : E) 1) (hy : y.1 ≠ 0) :
    ∃ p : ↥(TopCat.of (Metric.sphere (0 : E) 1) ⊗ TopCat.I),
      unitSphereConeCylinderMap E p = y := by
  set r : ℝ := ‖y.1‖
  have hrpos : 0 < r := by simpa only [r, norm_pos_iff] using hy
  have hrle : r ≤ 1 := by simpa only [r] using (mem_closedBall_zero_iff.mp y.2)
  have hx : r⁻¹ • y.1 ∈ Metric.sphere (0 : E) 1 := by
    rw [Metric.mem_sphere, dist_zero_right]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hrpos), inv_mul_cancel₀ hrpos.ne']
  set x : Metric.sphere (0 : E) 1 := ⟨r⁻¹ • y.1, hx⟩
  set t₀ : unitInterval := ⟨1 - r, by constructor <;> linarith⟩
  set t : TopCat.I.{u} := TopCat.I.homeomorph.symm t₀
  refine ⟨(x, t), ?_⟩
  apply Subtype.ext
  change (1 - (TopCat.I.homeomorph t : ℝ)) • (x.val : E) = y.1
  rw [show TopCat.I.homeomorph t = t₀ from by simp [t, t₀]]
  have h1 : (1 : ℝ) - (t₀ : ℝ) = r := by simp [t₀, sub_sub_cancel]
  rw [h1]
  rw [show (x.val : E) = r⁻¹ • y.1 from rfl]
  rw [smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]

/-- The canonical map from the cone on the unit sphere onto the closed unit ball is surjective. -/
theorem unitSphereConeMap_surjective :
    Function.Surjective (unitSphereConeMap E) := by
  intro y
  by_cases hy : y.1 = 0
  · refine ⟨conePoint (TopCat.of (Metric.sphere (0 : E) 1)) PUnit.unit, ?_⟩
    apply Subtype.ext
    simp only [← ConcreteCategory.comp_apply,
      ConcreteCategory.congr_hom (conePoint_unitSphereConeMap E) PUnit.unit]
    exact hy.symm
  · obtain ⟨p, hp⟩ := exists_unitSphereConeCylinderMap_eq_of_ne_zero E y hy
    refine ⟨coneCylinder (TopCat.of (Metric.sphere (0 : E) 1)) p, ?_⟩
    simpa only [← ConcreteCategory.comp_apply,
      coneCylinder_unitSphereConeMap] using hp

/-- Equal radial cylinder points define the same point of the cone. -/
theorem coneCylinder_eq_of_unitSphereConeCylinderMap_eq
    (p q : ↥(TopCat.of (Metric.sphere (0 : E) 1) ⊗ TopCat.I))
    (h : unitSphereConeCylinderMap E p =
      unitSphereConeCylinderMap E q) :
    coneCylinder (TopCat.of (Metric.sphere (0 : E) 1)) p =
      coneCylinder (TopCat.of (Metric.sphere (0 : E) 1)) q := by
  have hval : (1 - (TopCat.I.homeomorph p.2 : ℝ)) • (p.1.1 : E) =
      (1 - (TopCat.I.homeomorph q.2 : ℝ)) • (q.1.1 : E) :=
    congrArg Subtype.val h
  have hscale_eq : 1 - (TopCat.I.homeomorph p.2 : ℝ) =
      1 - (TopCat.I.homeomorph q.2 : ℝ) := by
    have hnorm : ‖(1 - (TopCat.I.homeomorph p.2 : ℝ)) • (p.1.1 : E)‖ =
        ‖(1 - (TopCat.I.homeomorph q.2 : ℝ)) • (q.1.1 : E)‖ :=
      congrArg norm hval
    simp only [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (TopCat.I.homeomorph p.2).2.2),
      abs_of_nonneg (sub_nonneg.mpr (TopCat.I.homeomorph q.2).2.2),
      norm_eq_of_mem_sphere p.1, norm_eq_of_mem_sphere q.1, mul_one] at hnorm
    linarith
  have ht : p.2 = q.2 := by
    apply TopCat.I.homeomorph.injective
    apply Subtype.ext
    linarith
  by_cases hp : p.2 = 1
  · have hq : q.2 = 1 := ht.symm.trans hp
    have hp_eq :=
      coneCylinder_eq_conePoint_of_snd_eq_one (TopCat.of (Metric.sphere (0 : E) 1)) p hp
    have hq_eq :=
      coneCylinder_eq_conePoint_of_snd_eq_one (TopCat.of (Metric.sphere (0 : E) 1)) q hq
    exact hp_eq.trans hq_eq.symm
  · have hscale : 1 - (TopCat.I.homeomorph p.2 : ℝ) ≠ 0 := by
      intro hzero
      have h1 : (TopCat.I.homeomorph p.2 : ℝ) = 1 :=
        (sub_eq_zero.mp hzero).symm
      have : p.2 = 1 := by
        apply TopCat.I.homeomorph.injective
        apply Subtype.ext
        simpa using h1
      exact hp this
    have hx : p.1 = q.1 := by
      apply Subtype.ext
      have hsmul : (1 - (TopCat.I.homeomorph p.2 : ℝ)) • (p.1.1 : E) =
          (1 - (TopCat.I.homeomorph p.2 : ℝ)) • (q.1.1 : E) := by
        calc (1 - (TopCat.I.homeomorph p.2 : ℝ)) • (p.1.1 : E)
            = (1 - (TopCat.I.homeomorph q.2 : ℝ)) • (q.1.1 : E) := hval
          _ = (1 - (TopCat.I.homeomorph p.2 : ℝ)) • (q.1.1 : E) := by
              rw [← hscale_eq]
      exact smul_right_injective E hscale hsmul
    exact congrArg (coneCylinder (TopCat.of (Metric.sphere (0 : E) 1))) (Prod.ext hx ht)

/-- The canonical map from the cone on the unit sphere to the closed unit ball is injective. -/
theorem unitSphereConeMap_injective :
    Function.Injective (unitSphereConeMap E) := by
  classical
  intro x y hxy
  rcases isEmpty_or_nonempty (Metric.sphere (0 : E) 1) with h | h
  · let _ : IsEmpty (Metric.sphere (0 : E) 1) := h
    have hx := cone_eq_conePoint_of_isEmpty (TopCat.of (Metric.sphere (0 : E) 1)) x
    have hy := cone_eq_conePoint_of_isEmpty (TopCat.of (Metric.sphere (0 : E) 1)) y
    exact hx.trans hy.symm
  · let _ : Nonempty (Metric.sphere (0 : E) 1) := h
    obtain ⟨p, rfl⟩ := (coneCylinder_isQuotientMap
      (TopCat.of (Metric.sphere (0 : E) 1))).surjective x
    obtain ⟨q, rfl⟩ := (coneCylinder_isQuotientMap
      (TopCat.of (Metric.sphere (0 : E) 1))).surjective y
    apply coneCylinder_eq_of_unitSphereConeCylinderMap_eq E
    simpa only [← ConcreteCategory.comp_apply,
      coneCylinder_unitSphereConeMap] using hxy

/-- The canonical map from the cone on the unit sphere to the closed unit ball is bijective. -/
theorem unitSphereConeMap_bijective :
    Function.Bijective (unitSphereConeMap E) :=
  ⟨unitSphereConeMap_injective E, unitSphereConeMap_surjective E⟩

omit [NormedSpace ℝ E] in
/-- The categorical cone on the unit sphere of a proper normed space is compact. -/
theorem unitSphereConeCompactSpace [ProperSpace E] :
    CompactSpace (TopCat.cone (TopCat.of (Metric.sphere (0 : E) 1))) := by
  let _ : CompactSpace TopCat.I.{u} :=
    TopCat.I.homeomorph.symm.compactSpace
  let _ : CompactSpace ↑((TopCat.prodBinaryFan
      (TopCat.of (Metric.sphere (0 : E) 1)) TopCat.I).pt) := by
    change CompactSpace (Metric.sphere (0 : E) 1 × TopCat.I.{u})
    infer_instance
  let _ : CompactSpace
      (↑(TopCat.of (Metric.sphere (0 : E) 1) ⊗ TopCat.I)) :=
    (TopCat.homeoOfIso
      ((CartesianMonoidalCategory.tensorProductIsBinaryProduct
        (TopCat.of (Metric.sphere (0 : E) 1)) TopCat.I).conePointUniqueUpToIso
        (TopCat.prodBinaryFanIsLimit
          (TopCat.of (Metric.sphere (0 : E) 1)) TopCat.I))).symm.compactSpace
  rcases isEmpty_or_nonempty (Metric.sphere (0 : E) 1) with h | h
  · let _ : IsEmpty (Metric.sphere (0 : E) 1) := h
    exact Function.Surjective.compactSpace
      (conePoint (TopCat.of (Metric.sphere (0 : E) 1))).hom.continuous
      (fun y => ⟨PUnit.unit, (cone_eq_conePoint_of_isEmpty _ y).symm⟩)
  · let _ : Nonempty (Metric.sphere (0 : E) 1) := h
    exact Function.Surjective.compactSpace
      (coneCylinder (TopCat.of (Metric.sphere (0 : E) 1))).hom.continuous
      (coneCylinder_isQuotientMap
        (TopCat.of (Metric.sphere (0 : E) 1))).surjective

noncomputable def unitSphereConeHomeomorph [ProperSpace E] :
    ↑(TopCat.cone (TopCat.of (Metric.sphere (0 : E) 1))) ≃ₜ
      Metric.closedBall (0 : E) 1 := by
  let _ := unitSphereConeCompactSpace E
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (unitSphereConeMap E)
      (unitSphereConeMap_bijective E))
    (unitSphereConeMap E).hom.continuous

@[simp]
theorem unitSphereConeHomeomorph_apply [ProperSpace E]
    (x : ↑(TopCat.cone (TopCat.of (Metric.sphere (0 : E) 1)))) :
    unitSphereConeHomeomorph E x = unitSphereConeMap E x :=
  rfl

@[simp]
theorem isoOfHomeo_unitSphereConeHomeomorph_hom [ProperSpace E] :
    (TopCat.isoOfHomeo (unitSphereConeHomeomorph E)).hom =
      unitSphereConeMap E :=
  rfl

def unitSphereClosedBallInclusion :
    TopCat.of (Metric.sphere (0 : E) 1) ⟶
      TopCat.of (Metric.closedBall (0 : E) 1) :=
  TopCat.ofHom
    ⟨fun x => ⟨x.val, by
        have h : dist x.val (0 : E) = 1 := Metric.mem_sphere.mp x.property
        exact Metric.mem_closedBall.mpr (le_of_eq h)⟩,
      by continuity⟩

@[reassoc (attr := simp)]
theorem ι₀_unitSphereConeCylinderMap :
    (TopCat.ι₀ : TopCat.of (Metric.sphere (0 : E) 1) ⟶
        TopCat.of (Metric.sphere (0 : E) 1) ⊗ TopCat.I) ≫
        unitSphereConeCylinderMap E =
      unitSphereClosedBallInclusion E := by
  ext x
  change (1 - (TopCat.I.homeomorph (0 : TopCat.I.{u})).1) • x.1 = x.1
  simp

@[reassoc (attr := simp)]
theorem coneBase_unitSphereConeMap :
    coneBase (TopCat.of (Metric.sphere (0 : E) 1)) ≫
        unitSphereConeMap E =
      unitSphereClosedBallInclusion E := by
  rw [← ι₀_coneCylinder, Category.assoc,
    coneCylinder_unitSphereConeMap, ι₀_unitSphereConeCylinderMap]

end TopCat
