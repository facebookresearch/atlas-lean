/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberDeformationDescent

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopCat

variable {E B A : TopCat.{u}}

-- The public homotopy equivalence proves the actual retraction weak, with
-- no independent weak-equivalence assumption on that map.
example (p : E ⟶ B) (i : A ⟶ B) (r : B ⟶ A) (retract : i ≫ r = 𝟙 A)
    (H : Homotopy (𝟙 B) (r ≫ i)) (m : E ⟶ E) (K : Homotopy (𝟙 E) m)
    (cover : ∀ (t : unitInterval) (e : E), p (K (t, e)) = H (t, p e))
    (stat : ∀ (t : unitInterval) (a : A), H (t, i a) = i a) :
    weakHomotopyEquivalences (liftedDeformationRetraction p i r H m K cover) := by
  have hw := homotopyEquiv_toFun_mem
    (liftedDeformationHomotopyEquiv p i r retract H m K cover stat)
  simpa only [liftedDeformationHomotopyEquiv_toFun] using hw

-- The inverse characteristic theorem exposes the actual inclusion through
-- the standard homotopy-equivalence API, without unfolding private data.
example (p : E ⟶ B) (i : A ⟶ B) (r : B ⟶ A) (retract : i ≫ r = 𝟙 A)
    (H : Homotopy (𝟙 B) (r ≫ i)) (m : E ⟶ E) (K : Homotopy (𝟙 E) m)
    (cover : ∀ (t : unitInterval) (e : E), p (K (t, e)) = H (t, p e))
    (stat : ∀ (t : unitInterval) (a : A), H (t, i a) = i a) :
    weakHomotopyEquivalences (pullback.fst p i) := by
  have hw := homotopyEquiv_invFun_mem
    (liftedDeformationHomotopyEquiv p i r retract H m K cover stat)
  simpa only [liftedDeformationHomotopyEquiv_invFun] using hw

-- The public coordinate theorem identifies the actual lifted endpoint.
example (p : E ⟶ B) (i : A ⟶ B) (r : B ⟶ A)
    (H : Homotopy (𝟙 B) (r ≫ i)) (m : E ⟶ E) (K : Homotopy (𝟙 E) m)
    (cover : ∀ (t : unitInterval) (e : E), p (K (t, e)) = H (t, p e)) (e : E) :
    pullback.fst p i (liftedDeformationRetraction p i r H m K cover e) = m e :=
  ConcreteCategory.congr_hom (liftedDeformationRetraction_fst p i r H m K cover) e

private abbrev intervalBase : TopCat := TopCat.of unitInterval
private def intervalInclusion : TopCat.of PUnit ⟶ intervalBase := TopCat.const 0
private def intervalRetraction : intervalBase ⟶ TopCat.of PUnit :=
  TopCat.isTerminalPUnit.from _

private def intervalDeformation :
    Homotopy (𝟙 intervalBase) (intervalRetraction ≫ intervalInclusion) where
  toFun z := ⟨(1 - (z.1 : ℝ)) * (z.2 : ℝ),
    unitInterval.mul_mem (unitInterval.symm z.1).property z.2.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_subtype_val.comp continuous_snd)
  map_zero_left x := by
    apply Subtype.ext
    simp
  map_one_left x := by
    apply Subtype.ext
    change (1 - (1 : ℝ)) * (x : ℝ) = (intervalInclusion (intervalRetraction x) : ℝ)
    have hzero : intervalInclusion (intervalRetraction x) = 0 :=
      TopCat.const_apply 0 _
    rw [hzero]
    simp

private theorem intervalRetract : intervalInclusion ≫ intervalRetraction = 𝟙 _ :=
  TopCat.isTerminalPUnit.hom_ext _ _

private theorem intervalDeformation_cover :
    ∀ (t : unitInterval) (e : intervalBase),
      (𝟙 intervalBase) (intervalDeformation (t, e)) =
        intervalDeformation (t, (𝟙 intervalBase) e) := by
  intro t e
  rfl

private theorem intervalDeformation_stat :
    ∀ (t : unitInterval) (a : TopCat.of PUnit),
      intervalDeformation (t, intervalInclusion a) = intervalInclusion a := by
  intro t a
  apply Subtype.ext
  change (1 - (t : ℝ)) * (intervalInclusion a : ℝ) = (intervalInclusion a : ℝ)
  have hzero : intervalInclusion a = 0 := TopCat.const_apply 0 a
  rw [hzero]
  simp

-- A nonidentity deformation of the interval to its zero endpoint supplies
-- the total-space equivalence from concrete base and lifted homotopies.
example : weakHomotopyEquivalences
    (liftedDeformationRetraction (𝟙 intervalBase) intervalInclusion intervalRetraction
      intervalDeformation (intervalRetraction ≫ intervalInclusion) intervalDeformation
      intervalDeformation_cover) := by
  have hw := homotopyEquiv_toFun_mem
    (liftedDeformationHomotopyEquiv (𝟙 intervalBase) intervalInclusion intervalRetraction
      intervalRetract intervalDeformation (intervalRetraction ≫ intervalInclusion)
      intervalDeformation intervalDeformation_cover intervalDeformation_stat)
  simpa only [liftedDeformationHomotopyEquiv_toFun] using hw

-- With the base fixed to a point, the same interval contraction moves the
-- entire restricted total space. No stationarity assumption on that lift
-- is needed to construct its homotopy inverse.
example : weakHomotopyEquivalences
    (liftedDeformationRetraction intervalRetraction (𝟙 (TopCat.of PUnit)) (𝟙 _)
      (Homotopy.refl (𝟙 _)) (intervalRetraction ≫ intervalInclusion) intervalDeformation
      (by intro t e; exact Subsingleton.elim _ _)) := by
  have hw := homotopyEquiv_toFun_mem
    (liftedDeformationHomotopyEquiv intervalRetraction (𝟙 (TopCat.of PUnit)) (𝟙 _)
      (by simp) (Homotopy.refl (𝟙 _)) (intervalRetraction ≫ intervalInclusion)
      intervalDeformation (by intro t e; exact Subsingleton.elim _ _)
      (by intro t a; rfl))
  simpa only [liftedDeformationHomotopyEquiv_toFun] using hw

#print axioms TopCat.liftedDeformationRetraction
#print axioms TopCat.liftedDeformationRetraction_fst
#print axioms TopCat.liftedDeformationRetraction_snd
#print axioms TopCat.liftedDeformationHomotopyEquiv
#print axioms TopCat.liftedDeformationHomotopyEquiv_toFun
#print axioms TopCat.liftedDeformationHomotopyEquiv_invFun
#print axioms TopCat.strictFiberToHomotopyFiber_mem_of_liftedDeformation

end TopCat
