/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SpectrumIndexMaps
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OperatorStabilizationK
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StableK
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativeKan
import MathlibExt.CategoryTheory.Enriched.LeftKanTensor

/-!
# Native index stabilization transport

The original coefficient-first inclusions, complete operator Hom maps and sphere
comparisons determine the transported stabilization maps. The symmetric and
orthogonal families retain every original block label; the sequential family
retains its original one-circle successor inclusion.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory BraidedCategory
open HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open scoped CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport

attribute [local instance] CategoryTheory.Spectra.OrthogonalIndex.enrichedCategory
  CategoryTheory.Spectra.OrthogonalIndex.category
  CategoryTheory.Spectra.OrthogonalIndex.monoidalCategory
  CategoryTheory.Spectra.OrthogonalIndex.enrichedOrdinaryCategory
  CategoryTheory.Spectra.OrthogonalIndex.symmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal

open CategoryTheory.Spectra CategoryTheory.Spectra.SpectrumIndexMaps
open CategoryTheory.EnrichedFunctorCat
local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

/-- Every actual symmetric block inclusion maps to the original orthogonal inclusion
through the original complete sphere comparison, including empty blocks. -/
theorem symmetricOrthogonal_inclusion (n a : I) :
    Actual.symmetricNu.{u, v} n a ≫
      symmetricOrthogonalOperatorHomMap.{u, v} n (n ⊗ a) =
    (originalSymmetricOrthogonalCoefficientIso.{u, v} a).hom ≫
      OrthogonalOperatorIndex.nu.{u, v} n.of.len a.of.len := by
  let S := PointedCGWH.sphereSequence.{u, v}.functor.obj a
  let T := PointedCGWH.orthogonalSphere.{u, v} a.of.len
  let c : S ⟶ T := (originalSymmetricOrthogonalCoefficientIso.{u, v} a).hom
  let P := PointedCGWH.basedDiscreteObj.{u, v, 0} (a ⊗ n ⟶ n ⊗ a)
  let H := PointedCGWH.symmetricOperatorObj.{u, v} n ⟶[PointedCGWH.{u, v}]
    PointedCGWH.symmetricOperatorObj.{u, v} (n ⊗ a)
  let Q := OrthogonalIndex.hom.{u, v} (a.of.len + n.of.len) (n.of.len + a.of.len)
  let Z := OrthogonalOperatorIndex.hom.{u, v} n.of.len (n.of.len + a.of.len)
  let p : 𝟙_ PointedCGWH.{u, v} ⟶ P :=
    PointedCGWH.basedDiscreteIncl.{u, v, 0} (a ⊗ n ⟶ n ⊗ a) (β_ a n).hom
  let q : P ⟶ Q := symmetricOrthogonalHomMap.{u, v} (a ⊗ n) (n ⊗ a)
  let r : 𝟙_ PointedCGWH.{u, v} ⟶ Q := eHomEquiv PointedCGWH.{u, v}
    (β_ (a.of.len : OrthogonalIndex) (n.of.len : OrthogonalIndex)).hom
  let i : Q ⊗ T ⟶ Z :=
    OrthogonalOperatorIndex.ι.{u, v} n.of.len (n.of.len + a.of.len) a.of.len
  let is : P ⊗ S ⟶ H := Enriched.weightedCoend.ι
    (Enriched.SphereOperator.weight (PointedCGWH.copowerUnderlyingMonoidalData.{u, v, 0} I)
      ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj n)
      ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj (n ⊗ a)))
    PointedCGWH.sphereCopowerEnrichedFunctor.{u, v}
    ((PointedCGWH.copowerRestriction.{u, v, 0} I).obj a)
  let m : H ⟶ Z := symmetricOrthogonalOperatorHomMap.{u, v} n (n ⊗ a)
  have hp : p ≫ q = r := by
    have h := symmetricOrthogonalHomMap_generator.{u, v} (β_ a n).hom
    have hb : OrthogonalIndex.matrixPoint.{u, v} (smallBijectionMatrix (β_ a n).hom) = r :=
      congrArg (OrthogonalIndex.matrixPoint.{u, v}) (smallBijectionMatrix_braiding a n)
    exact h.trans hb
  have hg : is ≫ m = (q ⊗ₘ c) ≫ i :=
    symmetricOrthogonalOperatorHomMap_generator.{u, v} n (n ⊗ a) a
  have hs : Actual.symmetricNu.{u, v} n a = (λ_ S).inv ≫ (p ⊗ₘ 𝟙 S) ≫ is := rfl
  have ho : OrthogonalOperatorIndex.nu.{u, v} n.of.len a.of.len =
      (λ_ T).inv ≫ (r ⊗ₘ 𝟙 T) ≫ i := rfl
  have ht : (p ⊗ₘ 𝟙 S) ≫ (q ⊗ₘ c) = r ⊗ₘ c := by
    rw [tensorHom_comp_tensorHom, Category.id_comp, hp]
  have hu : (λ_ S).inv ≫ (r ⊗ₘ c) = c ≫ (λ_ T).inv ≫ (r ⊗ₘ 𝟙 T) := by
    rw [leftUnitor_inv_naturality_assoc, ← id_tensorHom,
      tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  rw [hs, ho]
  change ((λ_ S).inv ≫ (p ⊗ₘ 𝟙 S) ≫ is) ≫ m =
    c ≫ (λ_ T).inv ≫ (r ⊗ₘ 𝟙 T) ≫ i
  calc
    _ = (λ_ S).inv ≫ (p ⊗ₘ 𝟙 S) ≫ (is ≫ m) := by simp only [Category.assoc]
    _ = (λ_ S).inv ≫ (p ⊗ₘ 𝟙 S) ≫ (q ⊗ₘ c) ≫ i := by rw [hg]
    _ = (λ_ S).inv ≫ (r ⊗ₘ c) ≫ i := by
      rw [← Category.assoc (p ⊗ₘ 𝟙 S) (q ⊗ₘ c) i, ht]
    _ = c ≫ (λ_ T).inv ≫ (r ⊗ₘ 𝟙 T) ≫ i := by
      rw [← Category.assoc (λ_ S).inv (r ⊗ₘ c) i, hu]
      simp only [Category.assoc]

section FullRestriction

variable {A B : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  [EnrichedCategory PointedCGWH.{u, v} B]

/-- Restriction keeps the entire original coefficient-first action for every full Hom. -/
theorem restriction_action (j : EnrichedFunctor PointedCGWH.{u, v} A B)
    (a b : A) (K : PointedCGWH.{u, v}) (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (X : EnrichedFunctorCat PointedCGWH.{u, v} B) :
    CurrentFree.action a b K D ((EnrichedFunctorCat.restriction j).obj X) =
      CurrentFree.action (j.obj a) (j.obj b) K (D ≫ j.map a b) X := by
  change (D ▷ X.toEnrichedFunctor.obj (j.obj a)) ≫
    (β_ (X.toEnrichedFunctor.obj (j.obj a)) (a ⟶[PointedCGWH.{u, v}] b)).inv ≫
      MonoidalClosed.uncurry (j.map a b ≫ X.toEnrichedFunctor.map (j.obj a) (j.obj b)) =
    ((D ≫ j.map a b) ▷ X.toEnrichedFunctor.obj (j.obj a)) ≫
      (β_ (X.toEnrichedFunctor.obj (j.obj a))
        (j.obj a ⟶[PointedCGWH.{u, v}] j.obj b)).inv ≫
          MonoidalClosed.uncurry (X.toEnrichedFunctor.map (j.obj a) (j.obj b))
  rw [MonoidalClosed.uncurry_natural_left, comp_whiskerRight]
  simp only [Category.assoc]
  rw [← braiding_inv_naturality_left_assoc]

/-- The actual original Omega transpose restricts through the same complete Hom map. -/
theorem restriction_adjoint (j : EnrichedFunctor PointedCGWH.{u, v} A B)
    (a b : A) (K : PointedCGWH.{u, v}) (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (X : EnrichedFunctorCat PointedCGWH.{u, v} B) :
    CurrentFree.adjoint a b K D ((EnrichedFunctorCat.restriction j).obj X) =
      CurrentFree.adjoint (j.obj a) (j.obj b) K (D ≫ j.map a b) X :=
  congrArg MonoidalClosed.curry (restriction_action j a b K D X)

end FullRestriction

section FreeTransport

variable {A B : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  [EnrichedCategory PointedCGWH.{u, v} B]

private theorem freeUnit_original (a : B) (M : PointedCGWH.{u, v}) :
    (Free.adjunction a).unit.app M = (ρ_ M).inv ≫ (M ◁ eId PointedCGWH.{u, v} a) := by
  have h := (Free.adjunction a).homEquiv_id M
  rw [Free.adjunction_homEquiv] at h
  change (ρ_ M).inv ≫ (M ◁ eId PointedCGWH.{u, v} a) ≫
    component (𝟙 (Free.object a M)) a = _ at h
  rw [component_id, Category.comp_id] at h
  exact h.symm

private theorem freeUnit_action (a b : B) (M : PointedCGWH.{u, v}) :
    (((ρ_ M).inv ≫ (M ◁ eId PointedCGWH.{u, v} a)) ▷
      (a ⟶[PointedCGWH.{u, v}] b)) ≫ Free.action a M a b =
        𝟙 (M ⊗ (a ⟶[PointedCGWH.{u, v}] b)) := by
  have h := Free.reconstruct_component a M (Free.object a M) (𝟙 _) b
  simpa only [component_id, Free.extensionComponent, Free.evaluate,
    Category.comp_id, tensorHom_id, Free.object_uncurry_map,
    MonoidalClosed.uncurry_curry] using h.symm

/-- The actual original free/Lan unit acts through every entire enriched Hom map. -/
theorem leftKanFreeIso_full_component
    (j : EnrichedFunctor PointedCGWH.{u, v} A B) (a b : A) (M : PointedCGWH.{u, v}) :
    component ((leftKanRestrictionAdjunction j).unit.app (Free.object a M)) b ≫
      component ((HomotopicalAlgebra.EnrichedProjective.Native.Kan.leftKanFreeIso j a).hom.app M)
        (j.obj b) = M ◁ j.map a b := by
  let Y := (restriction j).obj (Free.object (j.obj a) M)
  let t : Free.object a M ⟶ Y :=
    (leftKanRestrictionAdjunction j).unit.app (Free.object a M) ≫
      restrictionMap j
        ((HomotopicalAlgebra.EnrichedProjective.Native.Kan.leftKanFreeIso j a).hom.app M)
  let eta : M ⟶ Y.toEnrichedFunctor.obj a :=
    (Free.adjunction (j.obj a)).unit.app M
  let g : Free.object a M ⟶ Y := ((Free.adjunction a).homEquiv M Y).symm eta
  have ht : (Free.adjunction a).homEquiv M Y t = eta := by
    rw [Adjunction.homEquiv_apply]
    change (Free.adjunction a).unit.app M ≫ component t a = eta
    dsimp only [t]
    rw [component_comp, restrictionMap_component]
    exact HomotopicalAlgebra.EnrichedProjective.Native.Kan.leftKanFreeIso_unit j a M
  have htg : t = g := by
    apply ((Free.adjunction a).homEquiv M Y).injective
    exact ht.trans (((Free.adjunction a).homEquiv M Y).apply_symm_apply eta).symm
  have hg : g = Free.extend a M Y eta := by
    dsimp only [g]
    rw [Free.adjunction_homEquiv]
    rfl
  let H := a ⟶[PointedCGWH.{u, v}] b
  let H' := j.obj a ⟶[PointedCGWH.{u, v}] j.obj b
  let N := M ⊗ (j.obj a ⟶[PointedCGWH.{u, v}] j.obj a)
  let L := M ⊗ H'
  let eta0 : M ⟶ N := eta
  let q : H ⟶ H' := j.map a b
  let m : H' ⟶ (ihom N).obj L :=
    (Free.object (j.obj a) M).toEnrichedFunctor.map (j.obj a) (j.obj b)
  let act : N ⊗ H' ⟶ L := Free.action (j.obj a) M (j.obj a) (j.obj b)
  have hm : MonoidalClosed.uncurry m = act := Free.object_uncurry_map _ _ _ _
  have heta : eta0 = (ρ_ M).inv ≫ (M ◁ eId PointedCGWH.{u, v} (j.obj a)) :=
    freeUnit_original (j.obj a) M
  have ha : (eta0 ▷ H') ≫ act = 𝟙 (M ⊗ H') := by
    rw [heta]
    exact freeUnit_action _ _ M
  have hc0 : (eta0 ▷ H) ≫ MonoidalClosed.uncurry (q ≫ m) = M ◁ q := by
    rw [MonoidalClosed.uncurry_natural_left, hm, ← whisker_exchange_assoc, ha, Category.comp_id]
  have he0 : Free.extensionComponent a M Y eta b =
      (eta0 ⊗ₘ 𝟙 H) ≫ MonoidalClosed.uncurry (q ≫ m) := rfl
  have he1 : (eta0 ⊗ₘ 𝟙 H) ≫ MonoidalClosed.uncurry (q ≫ m) =
      (eta0 ▷ H) ≫ MonoidalClosed.uncurry (q ≫ m) :=
    congrArg (fun f : M ⊗ H ⟶ N ⊗ H => f ≫ MonoidalClosed.uncurry (q ≫ m))
      (tensorHom_id eta0 H)
  have ht0 : component t b = component (Free.extend a M Y eta) b :=
    congrArg (fun f : Free.object a M ⟶ Y => component f b) (htg.trans hg)
  have hc : component t b = M ◁ j.map a b :=
    ht0.trans ((Free.extend_component a M Y eta b).trans (he0.trans (he1.trans hc0)))
  dsimp only [t] at hc
  rw [component_comp, restrictionMap_component] at hc
  exact hc


private theorem free_leftKanHom_component
    (j : EnrichedFunctor PointedCGWH.{u, v} A B) (b : A) (K : PointedCGWH.{u, v})
    (Y : EnrichedFunctorCat PointedCGWH.{u, v} B)
    (h : (leftKan j).obj (Free.object b K) ⟶ Y) :
    (Free.adjunction b).homEquiv K ((restriction j).obj Y)
      ((leftKanRestrictionAdjunction j).homEquiv (Free.object b K) Y h) =
    (Free.adjunction b).unit.app K ≫
      component ((leftKanRestrictionAdjunction j).unit.app (Free.object b K)) b ≫
        component h (j.obj b) := by
  let eta : K ⟶ (Free.object b K).toEnrichedFunctor.obj b := (Free.adjunction b).unit.app K
  let ub : Free.object b K ⟶ (restriction j).obj ((leftKan j).obj (Free.object b K)) :=
    (leftKanRestrictionAdjunction j).unit.app (Free.object b K)
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply]
  change eta ≫ component (ub ≫ restrictionMap j h) b =
    eta ≫ component ub b ≫ component h (j.obj b)
  rw [component_comp, restrictionMap_component]
  exact Category.assoc eta (component ub b) (component h (j.obj b))

private theorem leftKanHom_component
    (j : EnrichedFunctor PointedCGWH.{u, v} A B)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A)
    (Y : EnrichedFunctorCat PointedCGWH.{u, v} B) (g : (leftKan j).obj X ⟶ Y) (a : A) :
    component ((leftKanRestrictionAdjunction j).homEquiv X Y g) a =
      component ((leftKanRestrictionAdjunction j).unit.app X) a ≫ component g (j.obj a) := by
  let u : X ⟶ (restriction j).obj ((leftKan j).obj X) :=
    (leftKanRestrictionAdjunction j).unit.app X
  have hu : (leftKanRestrictionAdjunction j).homEquiv X Y g = u ≫ restrictionMap j g := by
    rw [Adjunction.homEquiv_apply]
  have hr : component (restrictionMap j g) a = component g (j.obj a) :=
    restrictionMap_component j g a
  exact (congrArg (fun f : X ⟶ (restriction j).obj Y => component f a) hu).trans
    ((component_comp u (restrictionMap j g) a).trans
      (congrArg (fun f => component u a ≫ f) hr))

private theorem free_leftKan_map_post
    (j : EnrichedFunctor PointedCGWH.{u, v} A B) (b : A) (K : PointedCGWH.{u, v})
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A)
    (Y : EnrichedFunctorCat PointedCGWH.{u, v} B)
    (f : Free.object b K ⟶ X) (g : (leftKan j).obj X ⟶ Y) :
    (Free.adjunction b).homEquiv K ((restriction j).obj Y)
      ((leftKanRestrictionAdjunction j).homEquiv (Free.object b K) Y
        ((leftKan j).map f ≫ g)) =
    (Free.adjunction b).homEquiv K X f ≫
      component ((leftKanRestrictionAdjunction j).unit.app X) b ≫ component g (j.obj b) := by
  let l := (leftKanRestrictionAdjunction j).homEquiv X Y g
  let e : K ⟶ X.toEnrichedFunctor.obj b := (Free.adjunction b).homEquiv K X f
  have hl : (leftKanRestrictionAdjunction j).homEquiv (Free.object b K) Y
      ((leftKan j).map f ≫ g) = f ≫ l :=
    (leftKanRestrictionAdjunction j).homEquiv_naturality_left f g
  have hf : (Free.adjunction b).homEquiv K ((restriction j).obj Y) (f ≫ l) =
      e ≫ component l b := (Free.adjunction b).homEquiv_naturality_right f l
  have hc := leftKanHom_component j X Y g b
  exact (congrArg ((Free.adjunction b).homEquiv K ((restriction j).obj Y)) hl).trans
    (hf.trans ((congrArg (fun h : X.toEnrichedFunctor.obj b ⟶ Y.toEnrichedFunctor.obj (j.obj b) =>
      e ≫ h) hc).trans (Category.assoc _ _ _).symm))

private theorem free_leftKan_iso_post
    (j : EnrichedFunctor PointedCGWH.{u, v} A B) (b : A) (K : PointedCGWH.{u, v})
    (Y : EnrichedFunctorCat PointedCGWH.{u, v} B) (g : Free.object (j.obj b) K ⟶ Y) :
    (Free.adjunction b).homEquiv K ((restriction j).obj Y)
      ((leftKanRestrictionAdjunction j).homEquiv (Free.object b K) Y
        ((HomotopicalAlgebra.EnrichedProjective.Native.Kan.leftKanFreeIso j b).hom.app K ≫ g)) =
    (Free.adjunction (j.obj b)).homEquiv K Y g := by
  let S := Free.object b K
  let T := Free.object (j.obj b) K
  let t : (leftKan j).obj S ⟶ T :=
    (HomotopicalAlgebra.EnrichedProjective.Native.Kan.leftKanFreeIso j b).hom.app K
  let u : S ⟶ (restriction j).obj ((leftKan j).obj S) :=
    (leftKanRestrictionAdjunction j).unit.app S
  let eta : K ⟶ S.toEnrichedFunctor.obj b := (Free.adjunction b).unit.app K
  let eta' : K ⟶ T.toEnrichedFunctor.obj (j.obj b) := (Free.adjunction (j.obj b)).unit.app K
  let c : S.toEnrichedFunctor.obj b ⟶ ((leftKan j).obj S).toEnrichedFunctor.obj (j.obj b) :=
    component u b
  let d : ((leftKan j).obj S).toEnrichedFunctor.obj (j.obj b) ⟶ T.toEnrichedFunctor.obj (j.obj b) :=
    component t (j.obj b)
  let h : T.toEnrichedFunctor.obj (j.obj b) ⟶ Y.toEnrichedFunctor.obj (j.obj b) :=
    component g (j.obj b)
  have hu : eta ≫ c ≫ d = eta' :=
    HomotopicalAlgebra.EnrichedProjective.Native.Kan.leftKanFreeIso_unit j b K
  have hc : component (t ≫ g) (j.obj b) = d ≫ h := component_comp t g (j.obj b)
  have hf : eta' ≫ h = (Free.adjunction (j.obj b)).homEquiv K Y g :=
    ((Free.adjunction (j.obj b)).homEquiv_apply K Y g).symm
  exact (free_leftKanHom_component j b K Y (t ≫ g)).trans
    ((congrArg (fun f => eta ≫ c ≫ f) hc).trans
      ((Category.assoc eta c (d ≫ h)).symm.trans
        ((Category.assoc (eta ≫ c) d h).symm.trans ((congrArg (fun f => f ≫ h) hu).trans hf))))

private theorem free_leftKan_homEq_ext
    (j : EnrichedFunctor PointedCGWH.{u, v} A B) (b : A) (K : PointedCGWH.{u, v})
    (Y : EnrichedFunctorCat PointedCGWH.{u, v} B)
    (f g : (leftKan j).obj (Free.object b K) ⟶ Y)
    (h : (Free.adjunction b).homEquiv K ((restriction j).obj Y)
      ((leftKanRestrictionAdjunction j).homEquiv (Free.object b K) Y f) =
      (Free.adjunction b).homEquiv K ((restriction j).obj Y)
        ((leftKanRestrictionAdjunction j).homEquiv (Free.object b K) Y g)) : f = g := by
  apply ((leftKanRestrictionAdjunction j).homEquiv (Free.object b K) Y).injective
  exact ((Free.adjunction b).homEquiv K ((restriction j).obj Y)).injective h

private theorem unit_seed {C : Type*} [Category C] [MonoidalCategory C]
    {K H H' : C} (D : K ⟶ H) (m : H ⟶ H') :
    (D ≫ (λ_ H).inv) ≫ ((𝟙_ C) ◁ m) = (D ≫ m) ≫ (λ_ H').inv :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun h => D ≫ h) (leftUnitor_inv_naturality m).symm).trans
      (Category.assoc _ _ _).symm)

/-- Actual prolongation transports every original free stabilization through the full Hom map. -/
theorem leftKan_stabilization
    (j : EnrichedFunctor PointedCGWH.{u, v} A B) (a b : A) (K : PointedCGWH.{u, v})
    (D : K ⟶ (a ⟶[PointedCGWH.{u, v}] b)) :
    (leftKan j).map
      (HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.CurrentFree.stabilization
          a b K D) ≫
      (HomotopicalAlgebra.EnrichedProjective.Native.Kan.leftKanFreeIso j a).hom.app
        (𝟙_ PointedCGWH.{u, v}) =
    (HomotopicalAlgebra.EnrichedProjective.Native.Kan.leftKanFreeIso j b).hom.app K ≫
      HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.CurrentFree.stabilization
        (j.obj a) (j.obj b) K (D ≫ j.map a b) := by
  let T := Free.object a (𝟙_ PointedCGWH.{u, v})
  let Y := Free.object (j.obj a) (𝟙_ PointedCGWH.{u, v})
  let f : Free.object b K ⟶ T :=
    HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.CurrentFree.stabilization
      a b K D
  let g : Free.object (j.obj b) K ⟶ Y :=
    HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.CurrentFree.stabilization
      (j.obj a) (j.obj b) K (D ≫ j.map a b)
  let ea : (leftKan j).obj T ⟶ Y :=
    (HomotopicalAlgebra.EnrichedProjective.Native.Kan.leftKanFreeIso j a).hom.app
      (𝟙_ PointedCGWH.{u, v})
  let eb : (leftKan j).obj (Free.object b K) ⟶ Free.object (j.obj b) K :=
    (HomotopicalAlgebra.EnrichedProjective.Native.Kan.leftKanFreeIso j b).hom.app K
  let s : K ⟶ T.toEnrichedFunctor.obj b := (Free.adjunction b).homEquiv K T f
  let u : T.toEnrichedFunctor.obj b ⟶ ((leftKan j).obj T).toEnrichedFunctor.obj (j.obj b) :=
    component ((leftKanRestrictionAdjunction j).unit.app T) b
  let t : ((leftKan j).obj T).toEnrichedFunctor.obj (j.obj b) ⟶ Y.toEnrichedFunctor.obj (j.obj b) :=
    component ea (j.obj b)
  have hl := free_leftKan_map_post j b K T Y f ea
  have hr := free_leftKan_iso_post j b K Y g
  have hs : s = D ≫ (λ_ (a ⟶[PointedCGWH.{u, v}] b)).inv :=
    CurrentFree.stabilization_adjunct
      a b K D
  have hc : u ≫ t = (𝟙_ PointedCGWH.{u, v}) ◁ j.map a b :=
    leftKanFreeIso_full_component j a b (𝟙_ PointedCGWH.{u, v})
  have ht : (Free.adjunction (j.obj b)).homEquiv K Y g =
      (D ≫ j.map a b) ≫ (λ_ (j.obj a ⟶[PointedCGWH.{u, v}] j.obj b)).inv :=
    CurrentFree.stabilization_adjunct
      (j.obj a) (j.obj b) K (D ≫ j.map a b)
  have hm : (s ≫ u) ≫ t =
      (D ≫ (λ_ (a ⟶[PointedCGWH.{u, v}] b)).inv) ≫
        ((𝟙_ PointedCGWH.{u, v}) ◁ j.map a b) :=
    (Category.assoc s u t).trans
      (congrArg₂ (fun f : K ⟶ T.toEnrichedFunctor.obj b =>
        fun g : T.toEnrichedFunctor.obj b ⟶ Y.toEnrichedFunctor.obj (j.obj b) => f ≫ g) hs hc)
  apply free_leftKan_homEq_ext j b K Y
  exact hl.trans (hm.trans ((unit_seed D (j.map a b)).trans (ht.symm.trans hr.symm)))


end FreeTransport

private theorem adjoint_coefficient {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
    (a b : A) {S T : PointedCGWH.{u, v}} (c : S ⟶ T)
    (D : T ⟶ (a ⟶[PointedCGWH.{u, v}] b))
    (X : EnrichedFunctorCat PointedCGWH.{u, v} A) :
    CurrentFree.adjoint a b S (c ≫ D) X =
      CurrentFree.adjoint a b T D X ≫ (MonoidalClosed.pre c).app (X.toEnrichedFunctor.obj b) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_pre_app, CurrentFree.adjoint_uncurry,
    CurrentFree.adjoint_uncurry]
  unfold CurrentFree.action
  rw [comp_whiskerRight]
  simp only [Category.assoc]

/-- Every original symmetric Omega transpose is the full orthogonal transpose followed
by precomposition with the actual original sphere comparison. -/
theorem symmetricOrthogonal_adjoint (n a : I) (X : Actual.OrthogonalCarrier.{u, v}) :
    NativeK.adjoint Actual.symmetricFamily.{u, v} (n, a)
        ((EnrichedFunctorCat.restriction symmetricOrthogonalOperatorIndexFunctor.{u, v}).obj X) =
      NativeK.adjoint Actual.orthogonalFamily.{u, v} (n.of.len, a.of.len) X ≫
        (MonoidalClosed.pre (originalSymmetricOrthogonalCoefficientIso.{u, v} a).hom).app
          (X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (n.of.len + a.of.len))) := by
  let i := OrthogonalOperatorIndex.ofIndex n.of.len
  let k := OrthogonalOperatorIndex.ofIndex (n.of.len + a.of.len)
  let S := PointedCGWH.sphereSequence.{u, v}.functor.obj a
  let d : S ⟶ (i ⟶[PointedCGWH.{u, v}] k) :=
    Actual.symmetricNu n a ≫ symmetricOrthogonalOperatorHomMap n (n ⊗ a)
  let c := (originalSymmetricOrthogonalCoefficientIso.{u, v} a).hom
  let t := OrthogonalOperatorIndex.nu.{u, v} n.of.len a.of.len
  have hd : d = c ≫ t := symmetricOrthogonal_inclusion n a
  have hr : NativeK.adjoint Actual.symmetricFamily (n, a)
      ((EnrichedFunctorCat.restriction symmetricOrthogonalOperatorIndexFunctor).obj X) =
      CurrentFree.adjoint i k S d X :=
    restriction_adjoint symmetricOrthogonalOperatorIndexFunctor
      (PointedCGWH.symmetricOperatorObj n) (PointedCGWH.symmetricOperatorObj (n ⊗ a))
      S (Actual.symmetricNu n a) X
  have hc : CurrentFree.adjoint i k S d X = CurrentFree.adjoint i k S (c ≫ t) X :=
    congrArg (fun f : S ⟶ (i ⟶[PointedCGWH.{u, v}] k) => CurrentFree.adjoint i k S f X) hd
  exact hr.trans (hc.trans (adjoint_coefficient i k c t X))

/-- The same full-label native weak test is unchanged by original coefficient transport. -/
theorem symmetricOrthogonal_weak_adjoint_iff (n a : I) (X : Actual.OrthogonalCarrier.{u, v}) :
    weakEquivalences PointedCGWH.{u, v}
      (NativeK.adjoint Actual.symmetricFamily.{u, v} (n, a)
        ((EnrichedFunctorCat.restriction symmetricOrthogonalOperatorIndexFunctor.{u, v}).obj X)) ↔
    weakEquivalences PointedCGWH.{u, v}
      (NativeK.adjoint Actual.orthogonalFamily.{u, v} (n.of.len, a.of.len) X) := by
  let e := originalSymmetricOrthogonalCoefficientIso.{u, v} a
  let Y := X.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex (n.of.len + a.of.len))
  let q : (ihom (PointedCGWH.orthogonalSphere.{u, v} a.of.len)).obj Y ≅
      (ihom (PointedCGWH.sphereSequence.{u, v}.functor.obj a)).obj Y :=
    { hom := (MonoidalClosed.pre e.hom).app Y
      inv := (MonoidalClosed.pre e.inv).app Y
      hom_inv_id := by
        rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, e.inv_hom_id,
          MonoidalClosed.pre_id, NatTrans.id_app]
      inv_hom_id := by
        rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, e.hom_inv_id,
          MonoidalClosed.pre_id, NatTrans.id_app] }
  let _ : IsIso q.hom := q.isIso_hom
  have hq : weakEquivalences PointedCGWH.{u, v} q.hom :=
    (weakEquivalences PointedCGWH.{u, v}).of_isIso q.hom
  rw [symmetricOrthogonal_adjoint]
  change weakEquivalences PointedCGWH.{u, v}
    (NativeK.adjoint Actual.orthogonalFamily (n.of.len, a.of.len) X ≫ q.hom) ↔ _
  constructor
  · intro h
    exact (weakEquivalences PointedCGWH.{u, v}).of_postcomp _ _ hq h
  · intro h
    exact (weakEquivalences PointedCGWH.{u, v}).comp_mem _ _ h hq

/-- Actual restriction identifies the complete original symmetric and orthogonal Omega tests. -/
theorem symmetricOrthogonal_isOmega_iff (X : Actual.OrthogonalCarrier.{u, v}) :
    NativeK.IsOmega Actual.symmetricFamily.{u, v}
      ((EnrichedFunctorCat.restriction symmetricOrthogonalOperatorIndexFunctor.{u, v}).obj X) ↔
    NativeK.IsOmega Actual.orthogonalFamily.{u, v} X := by
  constructor
  · intro h na
    let n : I := ⟨FintypeCat.Skeleton.mk na.1⟩
    let a : I := ⟨FintypeCat.Skeleton.mk na.2⟩
    exact (symmetricOrthogonal_weak_adjoint_iff n a X).mp (h (n, a))
  · intro h na
    exact (symmetricOrthogonal_weak_adjoint_iff na.1 na.2 X).mpr
      (h (na.1.of.len, na.2.of.len))

end HomotopicalAlgebra.EnrichedProjective.Native.IndexStabilizationTransport
