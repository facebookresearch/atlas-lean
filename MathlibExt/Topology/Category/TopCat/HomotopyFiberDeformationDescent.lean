/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberBaseChange

import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Fiber comparison under a lifted base deformation

A deformation of a base into a retract, together with a compatible lifted
total-space homotopy, determines a retraction into the actual restricted
pullback. The restriction of the lift supplies its other homotopy inverse;
the lift need not be pointwise constant on the restricted total space.

The canonical strict-fiber endpoint map and the restricted fiber comparison
are the two geometric hypotheses. Naturality and changing-base invariance
then prove the current constant-path fiber comparison is a weak equivalence.
Open-cover and skeletal passage criteria are separate results.

Mathematical source: the deformation criterion of Dold–Lashof, Lemma 1.3,
as used in Quillen, *Higher algebraic K-theory I*, LNM 341 (1973), p. 98.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace TopCat

variable {E B A : TopCat.{u}}

/-- The endpoint of a lifted deformation gives the canonical map into the
actual pullback over the retract. -/
def liftedDeformationRetraction
    (p : E ⟶ B) (i : A ⟶ B) (r : B ⟶ A)
    (H : Homotopy (𝟙 B) (r ≫ i)) (m : E ⟶ E) (K : Homotopy (𝟙 E) m)
    (cover : ∀ (t : unitInterval) (e : E), p (K (t, e)) = H (t, p e)) :
    E ⟶ pullback p i :=
  pullback.lift m (p ≫ r) (by
    apply TopCat.ext
    intro e
    change p (m e) = i (r (p e))
    calc
      p (m e) = p (K (1, e)) := congrArg p (K.map_one_left e).symm
      _ = H (1, p e) := cover 1 e
      _ = i (r (p e)) := H.map_one_left (p e))

/-- The retraction's total-space coordinate is the actual endpoint of the lift. -/
@[reassoc (attr := simp)]
theorem liftedDeformationRetraction_fst
    (p : E ⟶ B) (i : A ⟶ B) (r : B ⟶ A)
    (H : Homotopy (𝟙 B) (r ≫ i)) (m : E ⟶ E) (K : Homotopy (𝟙 E) m)
    (cover : ∀ (t : unitInterval) (e : E), p (K (t, e)) = H (t, p e)) :
    liftedDeformationRetraction p i r H m K cover ≫ pullback.fst p i = m := by
  dsimp only [liftedDeformationRetraction]
  rw [pullback.lift_fst]

/-- The lifted retraction covers the base retraction. -/
@[reassoc (attr := simp)]
theorem liftedDeformationRetraction_snd
    (p : E ⟶ B) (i : A ⟶ B) (r : B ⟶ A)
    (H : Homotopy (𝟙 B) (r ≫ i)) (m : E ⟶ E) (K : Homotopy (𝟙 E) m)
    (cover : ∀ (t : unitInterval) (e : E), p (K (t, e)) = H (t, p e)) :
    liftedDeformationRetraction p i r H m K cover ≫ pullback.snd p i = p ≫ r := by
  dsimp only [liftedDeformationRetraction]
  rw [pullback.lift_snd]

private def restrictedDeformationFamily
    (p : E ⟶ B) (i : A ⟶ B) (r : B ⟶ A)
    (H : Homotopy (𝟙 B) (r ≫ i)) (m : E ⟶ E) (K : Homotopy (𝟙 E) m)
    (cover : ∀ (t : unitInterval) (e : E), p (K (t, e)) = H (t, p e))
    (stat : ∀ (t : unitInterval) (a : A), H (t, i a) = i a) :
    C(unitInterval × (pullback p i : TopCat.{u}), (pullback p i : TopCat.{u})) := by
  let X := TopCat.of (unitInterval × (pullback p i : TopCat.{u}))
  let f : X ⟶ E := TopCat.ofHom
    (K.toContinuousMap.comp
      (ContinuousMap.prodMap (ContinuousMap.id unitInterval) (pullback.fst p i).hom))
  let g : X ⟶ A := TopCat.ofHom
    ((pullback.snd p i).hom.comp
      (ContinuousMap.snd :
        C(unitInterval × (pullback p i : TopCat.{u}), (pullback p i : TopCat.{u}))))
  have w : f ≫ p = g ≫ i := by
    apply TopCat.ext
    intro z
    change p (K (z.1, pullback.fst p i z.2)) = i (pullback.snd p i z.2)
    have hp : p (pullback.fst p i z.2) = i (pullback.snd p i z.2) :=
      ConcreteCategory.congr_hom (pullback.condition :
        pullback.fst p i ≫ p = pullback.snd p i ≫ i) z.2
    rw [cover, hp, stat]
  exact (pullback.lift f g w).hom

private theorem restrictedDeformationFamily_fst
    (p : E ⟶ B) (i : A ⟶ B) (r : B ⟶ A)
    (H : Homotopy (𝟙 B) (r ≫ i)) (m : E ⟶ E) (K : Homotopy (𝟙 E) m)
    (cover : ∀ (t : unitInterval) (e : E), p (K (t, e)) = H (t, p e))
    (stat : ∀ (t : unitInterval) (a : A), H (t, i a) = i a)
    (z : unitInterval × (pullback p i : TopCat.{u})) :
    pullback.fst p i (restrictedDeformationFamily p i r H m K cover stat z) =
      K (z.1, pullback.fst p i z.2) := by
  dsimp only [restrictedDeformationFamily]
  exact ConcreteCategory.congr_hom
    (pullback.lift_fst (C := TopCat.{u})
      (W := TopCat.of (unitInterval × (pullback p i : TopCat.{u})))
      (f := p) (g := i) _ _ _) z

private theorem restrictedDeformationFamily_snd
    (p : E ⟶ B) (i : A ⟶ B) (r : B ⟶ A)
    (H : Homotopy (𝟙 B) (r ≫ i)) (m : E ⟶ E) (K : Homotopy (𝟙 E) m)
    (cover : ∀ (t : unitInterval) (e : E), p (K (t, e)) = H (t, p e))
    (stat : ∀ (t : unitInterval) (a : A), H (t, i a) = i a)
    (z : unitInterval × (pullback p i : TopCat.{u})) :
    pullback.snd p i (restrictedDeformationFamily p i r H m K cover stat z) =
      pullback.snd p i z.2 := by
  dsimp only [restrictedDeformationFamily]
  exact ConcreteCategory.congr_hom
    (pullback.lift_snd (C := TopCat.{u})
      (W := TopCat.of (unitInterval × (pullback p i : TopCat.{u})))
      (f := p) (g := i) _ _ _) z

private def restrictedDeformationHomotopy
    (p : E ⟶ B) (i : A ⟶ B) (r : B ⟶ A) (retract : i ≫ r = 𝟙 A)
    (H : Homotopy (𝟙 B) (r ≫ i)) (m : E ⟶ E) (K : Homotopy (𝟙 E) m)
    (cover : ∀ (t : unitInterval) (e : E), p (K (t, e)) = H (t, p e))
    (stat : ∀ (t : unitInterval) (a : A), H (t, i a) = i a) :
    Homotopy (𝟙 (pullback p i))
      (pullback.fst p i ≫ liftedDeformationRetraction p i r H m K cover) where
  toContinuousMap := restrictedDeformationFamily p i r H m K cover stat
  map_zero_left z := by
    apply Types.ext_of_isPullback
      ((IsPullback.of_hasPullback p i).map (forget TopCat))
    · change pullback.fst p i
        (restrictedDeformationFamily p i r H m K cover stat (0, z)) = pullback.fst p i z
      rw [restrictedDeformationFamily_fst]
      exact K.map_zero_left (pullback.fst p i z)
    · change pullback.snd p i
        (restrictedDeformationFamily p i r H m K cover stat (0, z)) = pullback.snd p i z
      exact restrictedDeformationFamily_snd p i r H m K cover stat (0, z)
  map_one_left z := by
    apply Types.ext_of_isPullback
      ((IsPullback.of_hasPullback p i).map (forget TopCat))
    · change pullback.fst p i
        (restrictedDeformationFamily p i r H m K cover stat (1, z)) =
          pullback.fst p i
            (liftedDeformationRetraction p i r H m K cover (pullback.fst p i z))
      rw [restrictedDeformationFamily_fst]
      exact (K.map_one_left (pullback.fst p i z)).trans
        (ConcreteCategory.congr_hom
          (liftedDeformationRetraction_fst p i r H m K cover) (pullback.fst p i z)).symm
    · change pullback.snd p i
        (restrictedDeformationFamily p i r H m K cover stat (1, z)) =
          pullback.snd p i
            (liftedDeformationRetraction p i r H m K cover (pullback.fst p i z))
      rw [restrictedDeformationFamily_snd]
      have hr := ConcreteCategory.congr_hom retract (pullback.snd p i z)
      have hp := ConcreteCategory.congr_hom (pullback.condition :
        pullback.fst p i ≫ p = pullback.snd p i ≫ i) z
      have hs := ConcreteCategory.congr_hom
        (liftedDeformationRetraction_snd p i r H m K cover) (pullback.fst p i z)
      change r (i (pullback.snd p i z)) = pullback.snd p i z at hr
      change p (pullback.fst p i z) = i (pullback.snd p i z) at hp
      change pullback.snd p i
          (liftedDeformationRetraction p i r H m K cover (pullback.fst p i z)) =
        r (p (pullback.fst p i z)) at hs
      exact hr.symm.trans ((congrArg r hp.symm).trans hs.symm)

/-- The base deformation and its lifted total homotopy construct both
homotopy inverses of the canonical map into the restricted pullback. -/
def liftedDeformationHomotopyEquiv
    (p : E ⟶ B) (i : A ⟶ B) (r : B ⟶ A) (retract : i ≫ r = 𝟙 A)
    (H : Homotopy (𝟙 B) (r ≫ i)) (m : E ⟶ E) (K : Homotopy (𝟙 E) m)
    (cover : ∀ (t : unitInterval) (e : E), p (K (t, e)) = H (t, p e))
    (stat : ∀ (t : unitInterval) (a : A), H (t, i a) = i a) :
    ContinuousMap.HomotopyEquiv E (pullback p i : TopCat.{u}) where
  toFun := (liftedDeformationRetraction p i r H m K cover).hom
  invFun := (pullback.fst p i).hom
  left_inv := ⟨by
    change Homotopy
      (liftedDeformationRetraction p i r H m K cover ≫ pullback.fst p i) (𝟙 E)
    rw [liftedDeformationRetraction_fst]
    exact K.symm⟩
  right_inv := ⟨(restrictedDeformationHomotopy p i r retract H m K cover stat).symm⟩

/-- The constructed homotopy equivalence uses the actual endpoint retraction. -/
@[simp]
theorem liftedDeformationHomotopyEquiv_toFun
    (p : E ⟶ B) (i : A ⟶ B) (r : B ⟶ A) (retract : i ≫ r = 𝟙 A)
    (H : Homotopy (𝟙 B) (r ≫ i)) (m : E ⟶ E) (K : Homotopy (𝟙 E) m)
    (cover : ∀ (t : unitInterval) (e : E), p (K (t, e)) = H (t, p e))
    (stat : ∀ (t : unitInterval) (a : A), H (t, i a) = i a) :
    TopCat.ofHom (liftedDeformationHomotopyEquiv p i r retract H m K cover stat).toFun =
      liftedDeformationRetraction p i r H m K cover := by
  rfl

/-- The inverse of the constructed equivalence is the actual restricted
total-space inclusion. -/
@[simp]
theorem liftedDeformationHomotopyEquiv_invFun
    (p : E ⟶ B) (i : A ⟶ B) (r : B ⟶ A) (retract : i ≫ r = 𝟙 A)
    (H : Homotopy (𝟙 B) (r ≫ i)) (m : E ⟶ E) (K : Homotopy (𝟙 E) m)
    (cover : ∀ (t : unitInterval) (e : E), p (K (t, e)) = H (t, p e))
    (stat : ∀ (t : unitInterval) (a : A), H (t, i a) = i a) :
    TopCat.ofHom (liftedDeformationHomotopyEquiv p i r retract H m K cover stat).invFun =
      pullback.fst p i := by
  rfl

private def baseDeformationHomotopyEquiv
    (i : A ⟶ B) (r : B ⟶ A) (retract : i ≫ r = 𝟙 A)
    (H : Homotopy (𝟙 B) (r ≫ i)) : ContinuousMap.HomotopyEquiv B A where
  toFun := r.hom
  invFun := i.hom
  left_inv := ⟨H.symm⟩
  right_inv := ⟨by
    change Homotopy (i ≫ r) (𝟙 A)
    rw [retract]
    exact Homotopy.refl _⟩

/-- The geometric strict-fiber endpoint map and the induction comparison on
the restricted projection imply the current constant-path comparison is weak. -/
theorem strictFiberToHomotopyFiber_mem_of_liftedDeformation
    (p : E ⟶ B) (i : A ⟶ B) (r : B ⟶ A) (retract : i ≫ r = 𝟙 A)
    (H : Homotopy (𝟙 B) (r ≫ i)) (m : E ⟶ E) (K : Homotopy (𝟙 E) m)
    (cover : ∀ (t : unitInterval) (e : E), p (K (t, e)) = H (t, p e))
    (stat : ∀ (t : unitInterval) (a : A), H (t, i a) = i a) (b : B)
    (hfiber : weakHomotopyEquivalences
      (strictFiberMapOfSquare (liftedDeformationRetraction p i r H m K cover) r
        (liftedDeformationRetraction_snd p i r H m K cover).symm b))
    (hcomparison : weakHomotopyEquivalences
      (strictFiberToHomotopyFiber (pullback.snd p i) (r b))) :
    weakHomotopyEquivalences (strictFiberToHomotopyFiber p b) := by
  have hs : weakHomotopyEquivalences (liftedDeformationRetraction p i r H m K cover) := by
    have hw := homotopyEquiv_toFun_mem
      (liftedDeformationHomotopyEquiv p i r retract H m K cover stat)
    simpa only [liftedDeformationHomotopyEquiv_toFun] using hw
  have hr : weakHomotopyEquivalences r :=
    homotopyEquiv_toFun_mem (baseDeformationHomotopyEquiv i r retract H)
  exact strictFiberToHomotopyFiber_mem_of_square
    (liftedDeformationRetraction p i r H m K cover) r
    (liftedDeformationRetraction_snd p i r H m K cover).symm b hs hr hfiber hcomparison

end TopCat
