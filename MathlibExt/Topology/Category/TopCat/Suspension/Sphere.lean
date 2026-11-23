/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.Topology.Sphere.SuspensionQuotient
public import MathlibExt.Topology.Category.TopCat.Suspension
public import MathlibExt.Topology.Category.TopCat.SpherePointed

/-!
# Suspensions of spheres

The cylinder quotient map identifies the categorical suspension of the standard
`m`-sphere with the `(m+1)`-sphere. The construction records both poles and
gives the corresponding isomorphism of pointed spheres.
-/

public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

universe u

namespace TopCat

/-- Cylinder map from `Sᵐ × I` to `Sᵐ⁺¹` via the quotient map. -/
noncomputable def sphereSuspensionCylinderMap (m : ℕ) :
    TopCat.sphere.{u} m ⊗ TopCat.I ⟶ TopCat.sphere.{u} (m + 1) :=
  TopCat.ofHom
    { toFun := fun p =>
        ULift.up
          (AlgebraicTopology.sphereSuspensionQuotientMap m
            (p.1.down, TopCat.I.homeomorph p.2))
      continuous_toFun := by
        apply continuous_uliftUp.comp
        apply (AlgebraicTopology.sphereSuspensionQuotientMap m).continuous.comp
        exact (continuous_uliftDown.comp continuous_fst).prodMk
          (TopCat.I.homeomorph.continuous.comp continuous_snd) }

/-- The original cylinder map evaluates by the original sphere quotient map. -/
private theorem sphereSuspensionCylinderMap_apply_aux (m : ℕ)
    (p : (TopCat.sphere.{u} m ⊗ TopCat.I : TopCat.{u})) :
    sphereSuspensionCylinderMap.{u} m p =
      ULift.up (AlgebraicTopology.sphereSuspensionQuotientMap m
        (p.1.down, TopCat.I.homeomorph p.2)) := rfl

@[simp]
theorem sphereSuspensionCylinderMap_apply (m : ℕ)
    (p : (TopCat.sphere.{u} m ⊗ TopCat.I : TopCat.{u})) :
    sphereSuspensionCylinderMap.{u} m p =
      ULift.up (AlgebraicTopology.sphereSuspensionQuotientMap m
        (p.1.down, TopCat.I.homeomorph p.2)) := sphereSuspensionCylinderMap_apply_aux m p

/-- Constant map to the north pole of `Sᵐ⁺¹`. -/
noncomputable def sphereNorthMap (m : ℕ) :
    TopCat.of PUnit ⟶ TopCat.sphere.{u} (m + 1) :=
  TopCat.ofHom (ContinuousMap.const _
    (ULift.up (AlgebraicTopology.northPt (m + 1))))

/-- The original north-point map is constant at the original north pole. -/
private theorem sphereNorthMap_apply_aux (m : ℕ) (p : (TopCat.of PUnit : TopCat.{u})) :
    sphereNorthMap.{u} m p = ULift.up (AlgebraicTopology.northPt (m + 1)) := rfl

@[simp]
theorem sphereNorthMap_apply (m : ℕ) (p : (TopCat.of PUnit : TopCat.{u})) :
    sphereNorthMap.{u} m p = ULift.up (AlgebraicTopology.northPt (m + 1)) := sphereNorthMap_apply_aux m p

/-- Constant map to the south pole of `Sᵐ⁺¹`. -/
noncomputable def sphereSouthMap (m : ℕ) :
    TopCat.of PUnit ⟶ TopCat.sphere.{u} (m + 1) :=
  TopCat.ofHom (ContinuousMap.const _
    (ULift.up (AlgebraicTopology.southPt (m + 1))))

/-- The original south-point map is constant at the original south pole. -/
private theorem sphereSouthMap_apply_aux (m : ℕ) (p : (TopCat.of PUnit : TopCat.{u})) :
    sphereSouthMap.{u} m p = ULift.up (AlgebraicTopology.southPt (m + 1)) := rfl

@[simp]
theorem sphereSouthMap_apply (m : ℕ) (p : (TopCat.of PUnit : TopCat.{u})) :
    sphereSouthMap.{u} m p = ULift.up (AlgebraicTopology.southPt (m + 1)) := sphereSouthMap_apply_aux m p

/-- The cylinder map hits the north pole at the top of the interval. -/
theorem sphereSuspensionCylinderMap_at_one (m : ℕ) :
    (TopCat.ι₁ : TopCat.sphere.{u} m ⟶
        TopCat.sphere.{u} m ⊗ TopCat.I) ≫
      sphereSuspensionCylinderMap m =
    TopCat.isTerminalPUnit.from _ ≫ sphereNorthMap m := by
  apply ConcreteCategory.hom_ext
  intro x
  apply ULift.down_injective
  change AlgebraicTopology.sphereSuspensionQuotientMap m
      (x.down, TopCat.I.homeomorph (1 : TopCat.I.{u})) = _
  rw [TopCat.I.homeomorph_one]
  exact AlgebraicTopology.sphereSuspensionQuotientMap_one m x.down

/-- The cylinder map hits the south pole at the bottom of the interval. -/
theorem sphereSuspensionCylinderMap_at_zero (m : ℕ) :
    (TopCat.ι₀ : TopCat.sphere.{u} m ⟶
        TopCat.sphere.{u} m ⊗ TopCat.I) ≫
      sphereSuspensionCylinderMap m =
    TopCat.isTerminalPUnit.from _ ≫ sphereSouthMap m := by
  apply ConcreteCategory.hom_ext
  intro x
  apply ULift.down_injective
  change AlgebraicTopology.sphereSuspensionQuotientMap m
      (x.down, TopCat.I.homeomorph (0 : TopCat.I.{u})) = _
  rw [TopCat.I.homeomorph_zero]
  exact AlgebraicTopology.sphereSuspensionQuotientMap_zero m x.down

/-- Cone map from the cone on `Sᵐ` to `Sᵐ⁺¹`. -/
noncomputable def sphereConeMap (m : ℕ) :
    TopCat.cone (TopCat.sphere.{u} m) ⟶ TopCat.sphere.{u} (m + 1) :=
  pushout.desc (sphereSuspensionCylinderMap m) (sphereNorthMap m)
    (sphereSuspensionCylinderMap_at_one m)

/-- The cone map acts by the cylinder map on cylinder points. -/
@[reassoc (attr := simp)] theorem coneCylinder_sphereConeMap (m : ℕ) :
    coneCylinder (TopCat.sphere.{u} m) ≫ sphereConeMap m =
      sphereSuspensionCylinderMap m :=
  pushout.inl_desc _ _ _

/-- The cone map sends the apex to the north pole. -/
@[reassoc (attr := simp)] theorem conePoint_sphereConeMap (m : ℕ) :
    conePoint (TopCat.sphere.{u} m) ≫ sphereConeMap m = sphereNorthMap m :=
  pushout.inr_desc _ _ _

/-- The cone map sends the base to the south pole. -/
theorem coneBase_sphereConeMap (m : ℕ) :
    coneBase (TopCat.sphere.{u} m) ≫ sphereConeMap m =
      TopCat.isTerminalPUnit.from _ ≫ sphereSouthMap m := by
  rw [← TopCat.ι₀_coneCylinder, Category.assoc, coneCylinder_sphereConeMap,
    sphereSuspensionCylinderMap_at_zero]

/-- The canonical continuous map from the categorical suspension of the standard
sphere to the standard sphere in the next dimension. -/
noncomputable def suspensionSphereMap (m : ℕ) :
    pushout (TopCat.isTerminalPUnit.from (TopCat.sphere.{u} m))
        (coneBase (TopCat.sphere.{u} m)) ⟶ TopCat.sphere.{u} (m + 1) :=
  pushout.desc (sphereSouthMap m) (sphereConeMap m)
    (by simpa using (coneBase_sphereConeMap m).symm)

/-- The actual point leg of the suspension maps to the original south pole. -/
@[reassoc (attr := simp)]
theorem suspensionInl_suspensionSphereMap (m : ℕ) :
    pushout.inl (TopCat.isTerminalPUnit.from (TopCat.sphere.{u} m))
        (coneBase (TopCat.sphere.{u} m)) ≫ suspensionSphereMap.{u} m =
      sphereSouthMap.{u} m :=
  pushout.inl_desc _ _ _

/-- The suspension map acts by the cone map on the cone leg. -/
@[reassoc (attr := simp)] theorem suspensionInr_suspensionSphereMap (m : ℕ) :
    pushout.inr (TopCat.isTerminalPUnit.from (TopCat.sphere.{u} m))
        (coneBase (TopCat.sphere.{u} m)) ≫ suspensionSphereMap m =
      sphereConeMap m :=
  pushout.inr_desc _ _ _

/-- The suspension map sends the suspension point to the north pole. -/
-- Not `@[simp]`: simp already proves this via `suspensionFunctor_obj_hom`,
-- `suspensionInr_suspensionSphereMap`, and `conePoint_sphereConeMap`.
@[reassoc] theorem suspensionPoint_suspensionSphereMap (m : ℕ) :
    (TopCat.suspensionFunctor.obj (TopCat.sphere.{u} m)).hom ≫
      suspensionSphereMap m = sphereNorthMap m := by
  change conePoint (TopCat.sphere.{u} m) ≫
      (pushout.inr (TopCat.isTerminalPUnit.from (TopCat.sphere.{u} m))
        (coneBase (TopCat.sphere.{u} m)) ≫ suspensionSphereMap.{u} m) = _
  rw [suspensionInr_suspensionSphereMap, conePoint_sphereConeMap]

/-- Cylinder cover of the suspension by `Sᵐ × I`. -/
noncomputable def suspensionCylinder (m : ℕ) :
    TopCat.sphere.{u} m ⊗ TopCat.I ⟶
      pushout (TopCat.isTerminalPUnit.from (TopCat.sphere.{u} m))
        (coneBase (TopCat.sphere.{u} m)) :=
  coneCylinder (TopCat.sphere.{u} m) ≫
    pushout.inr (TopCat.isTerminalPUnit.from (TopCat.sphere.{u} m))
      (coneBase (TopCat.sphere.{u} m))

/-- Every suspension point is a cylinder point. -/
theorem suspensionCylinder_surjective (m : ℕ) :
    Function.Surjective (suspensionCylinder.{u} m) := by
  let X := TopCat.sphere.{u} m
  let _ : Nonempty X := ⟨ULift.up (AlgebraicTopology.northPt m)⟩
  let f : X ⟶ TopCat.of PUnit := TopCat.isTerminalPUnit.from X
  let g : X ⟶ cone X := coneBase X
  let q : TopCat.of PUnit ⨿ cone X ⟶ pushout f g :=
    coprod.desc (pushout.inl f g) (pushout.inr f g)
  intro z
  obtain ⟨p, hp⟩ := (pushoutCoproductMap_isQuotientMap f g).surjective z
  let hc := isColimitOfPreserves (forget TopCat)
    (coprodIsCoprod (TopCat.of PUnit) (cone X))
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hc p
  cases j with
  | mk j =>
    cases j with
    | left =>
      change PUnit at y
      let x : X := ULift.up (AlgebraicTopology.northPt m)
      refine ⟨(x, (0 : TopCat.I)), ?_⟩
      rw [← hp, ← hy]
      change (coneCylinder X ≫ pushout.inr f g) (x, (0 : TopCat.I)) =
        q ((coprod.inl : TopCat.of PUnit ⟶ TopCat.of PUnit ⨿ cone X) y)
      change (coneBase X ≫ pushout.inr f g) x = _
      calc
        (coneBase X ≫ pushout.inr f g) x =
            (f ≫ pushout.inl f g) x :=
          ConcreteCategory.congr_hom (pushout.condition.symm) x
        _ = q ((coprod.inl : TopCat.of PUnit ⟶ TopCat.of PUnit ⨿ cone X) y) := by
          cases y
          rw [← ConcreteCategory.comp_apply, coprod.inl_desc]
          rfl
    | right =>
      change cone X at y
      obtain ⟨p, hp'⟩ := (coneCylinder_isQuotientMap X).surjective y
      refine ⟨p, ?_⟩
      rw [← hp, ← hy]
      change (coneCylinder X ≫ pushout.inr f g) p =
        q ((coprod.inr : cone X ⟶ TopCat.of PUnit ⨿ cone X) y)
      rw [← hp']
      rw [← ConcreteCategory.comp_apply, coprod.inr_desc]
      rfl

/-- The suspension map acts by the cylinder map on cylinder points. -/
theorem suspensionCylinder_suspensionSphereMap (m : ℕ) :
    suspensionCylinder.{u} m ≫ suspensionSphereMap.{u} m =
      sphereSuspensionCylinderMap.{u} m := by
  change coneCylinder (TopCat.sphere.{u} m) ≫
      (pushout.inr (TopCat.isTerminalPUnit.from (TopCat.sphere.{u} m))
        (coneBase (TopCat.sphere.{u} m)) ≫ suspensionSphereMap.{u} m) = _
  rw [suspensionInr_suspensionSphereMap, coneCylinder_sphereConeMap]

private theorem suspensionSphereMap_injective (m : ℕ) :
    Function.Injective (suspensionSphereMap.{u} m) := by
  intro a b hab
  obtain ⟨p, rfl⟩ := suspensionCylinder_surjective.{u} m a
  obtain ⟨q, rfl⟩ := suspensionCylinder_surjective.{u} m b
  have hcyl : sphereSuspensionCylinderMap.{u} m p =
      sphereSuspensionCylinderMap.{u} m q := by
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      suspensionCylinder_suspensionSphereMap] at hab
    exact hab
  have hjoin :
      AlgebraicTopology.sphereSuspensionQuotientMap m
          (p.1.down, TopCat.I.homeomorph p.2) =
        AlgebraicTopology.sphereSuspensionQuotientMap m
          (q.1.down, TopCat.I.homeomorph q.2) := by
    apply ULift.up_injective
    exact hcyl
  obtain ⟨ht, hp0 | hp1 | hx⟩ :=
    AlgebraicTopology.sphereSuspensionQuotientMap_eq m
      (p.1.down, TopCat.I.homeomorph p.2)
      (q.1.down, TopCat.I.homeomorph q.2) hjoin
  · have hp0' : p.2 = 0 := by
      apply TopCat.I.homeomorph.injective
      change TopCat.I.homeomorph p.2 = 0 at hp0
      simpa using hp0
    have hq0' : q.2 = 0 := by
      apply TopCat.I.homeomorph.injective
      change TopCat.I.homeomorph p.2 = TopCat.I.homeomorph q.2 at ht
      change TopCat.I.homeomorph p.2 = 0 at hp0
      rw [← ht]
      simpa using hp0
    have hpbase : coneCylinder (TopCat.sphere.{u} m) p =
        coneBase (TopCat.sphere.{u} m) p.1 := by
      change coneCylinder (TopCat.sphere.{u} m) (p.1, p.2) = _
      rw [hp0']
      change (TopCat.ι₀ ≫ coneCylinder (TopCat.sphere.{u} m)) p.1 = _
      rw [TopCat.ι₀_coneCylinder]
    have hqbase : coneCylinder (TopCat.sphere.{u} m) q =
        coneBase (TopCat.sphere.{u} m) q.1 := by
      change coneCylinder (TopCat.sphere.{u} m) (q.1, q.2) = _
      rw [hq0']
      change (TopCat.ι₀ ≫ coneCylinder (TopCat.sphere.{u} m)) q.1 = _
      rw [TopCat.ι₀_coneCylinder]
    dsimp only [suspensionCylinder]
    simp only [ConcreteCategory.comp_apply, hpbase, hqbase]
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
      pushout.condition.symm]
    rfl
  · have hp1' : p.2 = 1 := by
      apply TopCat.I.homeomorph.injective
      change TopCat.I.homeomorph p.2 = 1 at hp1
      simpa using hp1
    have hq1' : q.2 = 1 := by
      apply TopCat.I.homeomorph.injective
      change TopCat.I.homeomorph p.2 = TopCat.I.homeomorph q.2 at ht
      change TopCat.I.homeomorph p.2 = 1 at hp1
      rw [← ht]
      simpa using hp1
    have hpcone := coneCylinder_eq_conePoint_of_snd_eq_one
      (TopCat.sphere.{u} m) p hp1'
    have hqcone := coneCylinder_eq_conePoint_of_snd_eq_one
      (TopCat.sphere.{u} m) q hq1'
    dsimp only [suspensionCylinder]
    simp only [ConcreteCategory.comp_apply, hpcone, hqcone]
  · have hx' : p.1 = q.1 := ULift.down_injective hx
    have ht' : p.2 = q.2 := TopCat.I.homeomorph.injective ht
    exact congrArg (suspensionCylinder.{u} m) (Prod.ext hx' ht')

private theorem suspensionSphereMap_surjective (m : ℕ) :
    Function.Surjective (suspensionSphereMap.{u} m) := by
  intro z
  obtain ⟨p, hp⟩ :=
    (AlgebraicTopology.sphereSuspensionQuotientMap_isQuotientMap m).surjective z.down
  let p' : ↑(TopCat.sphere.{u} m ⊗ TopCat.I) :=
    (ULift.up p.1, TopCat.I.homeomorph.symm p.2)
  refine ⟨suspensionCylinder.{u} m p', ?_⟩
  rw [← ConcreteCategory.comp_apply,
    suspensionCylinder_suspensionSphereMap]
  apply ULift.down_injective
  exact hp

/-- The categorical suspension of the standard `m`-sphere is homeomorphic to
the standard `(m+1)`-sphere. -/
noncomputable def suspensionSphereHomeomorph (m : ℕ) :
    ↑((suspensionFunctor.obj (TopCat.sphere.{u} m)).right) ≃ₜ
      ↑(TopCat.sphere.{u} (m + 1)) := by
  change ↑(pushout (TopCat.isTerminalPUnit.from (TopCat.sphere.{u} m))
      (coneBase (TopCat.sphere.{u} m))) ≃ₜ ↑(TopCat.sphere.{u} (m + 1))
  let _ : CompactSpace TopCat.I.{u} :=
    TopCat.I.homeomorph.symm.compactSpace
  let _ : CompactSpace ↑(TopCat.sphere.{u} m) := by
    change CompactSpace (ULift (Metric.sphere
      (0 : EuclideanSpace ℝ (Fin (m + 1))) 1))
    convert! Homeomorph.compactSpace Homeomorph.ulift.symm
    infer_instance
  let _ : CompactSpace ↑((TopCat.prodBinaryFan
      (TopCat.sphere.{u} m) TopCat.I).pt) := by
    change CompactSpace (↑(TopCat.sphere.{u} m) × TopCat.I.{u})
    infer_instance
  let _ : CompactSpace ↑(TopCat.sphere.{u} m ⊗ TopCat.I) :=
    (TopCat.homeoOfIso
      ((CartesianMonoidalCategory.tensorProductIsBinaryProduct
        (TopCat.sphere.{u} m) TopCat.I).conePointUniqueUpToIso
        (TopCat.prodBinaryFanIsLimit
          (TopCat.sphere.{u} m) TopCat.I))).symm.compactSpace
  let _ : CompactSpace
      ↑(pushout (TopCat.isTerminalPUnit.from (TopCat.sphere.{u} m))
        (coneBase (TopCat.sphere.{u} m))) :=
    Function.Surjective.compactSpace
      (suspensionCylinder.{u} m).hom.continuous
      (suspensionCylinder_surjective.{u} m)
  let _ : T2Space ↑(TopCat.sphere.{u} (m + 1)) := by
    change T2Space (ULift (Metric.sphere
      (0 : EuclideanSpace ℝ (Fin ((m + 1) + 1))) 1))
    infer_instance
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (suspensionSphereMap.{u} m)
      ⟨suspensionSphereMap_injective.{u} m,
        suspensionSphereMap_surjective.{u} m⟩)
    (suspensionSphereMap.{u} m).hom.continuous

/-- The categorical suspension of the standard `m`-sphere is isomorphic in
`TopCat` to the standard `(m+1)`-sphere. -/
noncomputable def suspensionSphereIso (m : ℕ) :
    (suspensionFunctor.obj (TopCat.sphere.{u} m)).right ≅
      TopCat.sphere.{u} (m + 1) :=
  TopCat.isoOfHomeo (suspensionSphereHomeomorph.{u} m)

private theorem suspensionSphereIso_hom_aux (m : ℕ) :
    (suspensionSphereIso.{u} m).hom = suspensionSphereMap.{u} m := rfl

@[simp] theorem suspensionSphereIso_hom (m : ℕ) :
    (suspensionSphereIso.{u} m).hom = suspensionSphereMap.{u} m :=
  suspensionSphereIso_hom_aux m

/-- The categorical suspension of the standard pointed `m`-sphere is the
standard pointed `(m+1)`-sphere. -/
noncomputable def suspensionSpherePointedIso (m : ℕ) :
    suspensionFunctor.obj (TopCat.sphere.{u} m) ≅
      TopCat.pointedSphere.{u} (m + 1) :=
  Under.isoMk (suspensionSphereIso.{u} m) (by
    rw [suspensionSphereIso_hom]
    exact suspensionPoint_suspensionSphereMap.{u} m)

/-- The pointed suspension isomorphism uses the same original sphere map. -/
private theorem suspensionSpherePointedIso_hom_right_aux (m : ℕ) :
    (suspensionSpherePointedIso.{u} m).hom.right = suspensionSphereMap.{u} m := rfl

@[simp]
theorem suspensionSpherePointedIso_hom_right (m : ℕ) :
    (suspensionSpherePointedIso.{u} m).hom.right = suspensionSphereMap.{u} m
      := suspensionSpherePointedIso_hom_right_aux m

end TopCat
