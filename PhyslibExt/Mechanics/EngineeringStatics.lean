/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.CrossProduct
public import PhyslibExt.Mechanics.HarmonicMechanics
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

/-!
# Three-dimensional wrench origin transport

The moment of a finite three-dimensional load system about a reference point, the wrench it
defines, and the change of reference point.

## i. Overview

A finite load system in one inertial frame: forces `F i` applied at the points `r i` and free
couples `C i`, for `i` in a finite index type. Its resultant is `R = ∑ i, F i`, the existing
`PhyslibExt.Mechanics.HarmonicMechanics.resultantForce`, and its moment about a reference point
`O` is `M_O = ∑ i, ((r i - O) ⨯₃ F i + C i)`, the lever arm running from `O` to the point of
application. The pair `(R, M_O)` is the wrench of the system about `O`.

Model inputs (hypotheses of the module):

* all points, forces and couples are components in one inertial frame;
* a free couple contributes its moment about every reference point;
* lengths and forces keep their own units: positions carry a length factor, forces a force
  factor, and couples and moments their product;
* no elasticity: the loads are given, and no deformation or constitutive law enters.

Moving the reference point from `O` to `O'` keeps the resultant and adds `(O - O') ⨯₃ R` to the
moment. The moment is therefore the same about every point when the resultant vanishes, and some
reference point changes it when the resultant does not.

The planar projection concerns the forces alone, with the free couples discarded: the planar
moment `PhyslibExt.Mechanics.HarmonicMechanics.moment2D` carries no couples. For the forces,
projection onto the plane of the first two axes keeps only the third component of the moment about
the origin, which is the planar moment of the projected forces; its shift law is
`PhyslibExt.Mechanics.HarmonicMechanics.moment2D_shift`. A force normal to that plane can carry a
nonzero moment that the projection loses.

Non-goals: equilibrium of a constrained body, reactions, distributed loads, the central axis of a
wrench, and any empirical adequacy or system safety claim.

## ii. Key results

- `momentAbout_eq_add_cross`, `wrenchAbout_eq_transport` : the origin transport
  `M_O' = M_O + (O - O') ⨯₃ R`, for the moment and for the wrench record.
- `momentAbout_eq_of_resultantForce_eq_zero`, `exists_momentAbout_ne_of_resultantForce_ne_zero` :
  the moment is origin independent exactly when the resultant vanishes.
- `wrenchAbout_smul` : with positions and the reference point scaled by a length factor, forces
  by a force factor and couples by the product of the two, the resultant scales with the force
  factor and the moment with the product.
- `moment2D_planarPart` : for the forces alone, free couples discarded, the planar moment of the
  projected forces is the third component of their moment about the origin.

## iii. Table of contents

- A. Resultant, moment and wrench of a finite load system
- B. Origin transport and origin invariance
- C. Units
- D. Planar projection of the forces

## iv. References

- F. P. Beer, E. R. Johnston Jr. and D. F. Mazurek, *Vector Mechanics for Engineers: Statics*,
  chapter 3 (equivalent systems of forces; moving a force-couple system to another point).
- J. L. Meriam and L. G. Kraige, *Engineering Mechanics: Statics*, chapter 2 (moments and
  couples in three dimensions; resultants and the wrench).
-/

@[expose] public section

open scoped Matrix

namespace Mechanics.EngineeringStatics

open PhyslibExt.Mechanics.HarmonicMechanics

variable {ι : Type*} [Fintype ι]

/-! ## A. Resultant, moment and wrench of a finite load system -/

/-- Moment about the reference point `O` of the forces `F i` applied at the points `r i` and the
free couples `C i`: `M_O = ∑ i, ((r i - O) ⨯₃ F i + C i)`. -/
noncomputable def momentAbout (r F C : ι → Fin 3 → ℝ) (O : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ∑ i, ((r i - O) ⨯₃ F i + C i)

/-- A three-dimensional wrench: a resultant force and a moment about a reference point. -/
structure Wrench where
  /-- The resultant force. -/
  force : Fin 3 → ℝ
  /-- The moment about the reference point. -/
  moment : Fin 3 → ℝ

/-- The wrench of the load system about `O`: the resultant `R = ∑ i, F i` and the moment
`M_O`. -/
noncomputable def wrenchAbout (r F C : ι → Fin 3 → ℝ) (O : Fin 3 → ℝ) : Wrench :=
  ⟨resultantForce F, momentAbout r F C O⟩

/-- Transport of a wrench from the reference point `O` to the reference point `O'`: the force is
kept and the moment gains `(O - O') ⨯₃ force`. -/
noncomputable def Wrench.transport (W : Wrench) (O O' : Fin 3 → ℝ) : Wrench :=
  ⟨W.force, W.moment + (O - O') ⨯₃ W.force⟩

/-! ## B. Origin transport and origin invariance -/

/-- Origin transport of the moment: `M_O' = M_O + (O - O') ⨯₃ R`. -/
lemma momentAbout_eq_add_cross (r F C : ι → Fin 3 → ℝ) (O O' : Fin 3 → ℝ) :
    momentAbout r F C O' = momentAbout r F C O + (O - O') ⨯₃ resultantForce F := by
  unfold momentAbout resultantForce
  have hadd : ∀ a b c : Fin 3 → ℝ, (a + b) ⨯₃ c = a ⨯₃ c + b ⨯₃ c := fun a b c => by
    rw [map_add, LinearMap.add_apply]
  have hdecomp : ∀ i, r i - O' = (r i - O) + (O - O') := fun i => by abel
  have hrearr : ∀ i : ι, (r i - O) ⨯₃ F i + (O - O') ⨯₃ F i + C i
      = ((r i - O) ⨯₃ F i + C i) + (O - O') ⨯₃ F i := fun i => by abel
  simp_rw [hdecomp, hadd, hrearr, Finset.sum_add_distrib]
  congr 1
  exact (map_sum _ _ _).symm

/-- The wrench about `O'` is the wrench about `O` transported to `O'`. -/
lemma wrenchAbout_eq_transport (r F C : ι → Fin 3 → ℝ) (O O' : Fin 3 → ℝ) :
    wrenchAbout r F C O' = (wrenchAbout r F C O).transport O O' := by
  have h1 : wrenchAbout r F C O' = ⟨resultantForce F, momentAbout r F C O'⟩ := rfl
  have h2 : wrenchAbout r F C O = ⟨resultantForce F, momentAbout r F C O⟩ := rfl
  have h3 : (⟨resultantForce F, momentAbout r F C O⟩ : Wrench).transport O O'
      = ⟨resultantForce F, momentAbout r F C O + (O - O') ⨯₃ resultantForce F⟩ := rfl
  rw [h1, h2, h3, momentAbout_eq_add_cross]

/-- Origin invariance: when the resultant vanishes, the moment is the same about every
reference point. -/
lemma momentAbout_eq_of_resultantForce_eq_zero {r F C : ι → Fin 3 → ℝ}
    (hR : resultantForce F = 0) (O O' : Fin 3 → ℝ) :
    momentAbout r F C O' = momentAbout r F C O := by
  rw [momentAbout_eq_add_cross, hR, map_zero, add_zero]

/-- A nonzero resultant changes the moment: some reference point gives a different moment. -/
lemma exists_momentAbout_ne_of_resultantForce_ne_zero {r F C : ι → Fin 3 → ℝ}
    (hR : resultantForce F ≠ 0) (O : Fin 3 → ℝ) :
    ∃ O' : Fin 3 → ℝ, momentAbout r F C O' ≠ momentAbout r F C O := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hR
  rw [Pi.zero_apply] at hj
  fin_cases j
  · refine ⟨O - ![0, 1, 0], ?_⟩
    rw [momentAbout_eq_add_cross, sub_sub_cancel]
    intro hcon
    rw [add_eq_left] at hcon
    rw [show (![0, 1, 0] : Fin 3 → ℝ) ⨯₃ resultantForce F
        = ![resultantForce F 2, 0, -resultantForce F 0] from by simp [cross_apply]] at hcon
    have h2 := congrFun hcon 2
    apply hj
    simpa using h2
  · refine ⟨O - ![0, 0, 1], ?_⟩
    rw [momentAbout_eq_add_cross, sub_sub_cancel]
    intro hcon
    rw [add_eq_left] at hcon
    rw [show (![0, 0, 1] : Fin 3 → ℝ) ⨯₃ resultantForce F
        = ![-resultantForce F 1, resultantForce F 0, 0] from by simp [cross_apply]] at hcon
    have h0 := congrFun hcon 0
    apply hj
    simpa using h0
  · refine ⟨O - ![1, 0, 0], ?_⟩
    rw [momentAbout_eq_add_cross, sub_sub_cancel]
    intro hcon
    rw [add_eq_left] at hcon
    rw [show (![1, 0, 0] : Fin 3 → ℝ) ⨯₃ resultantForce F
        = ![0, -resultantForce F 2, resultantForce F 1] from by simp [cross_apply]] at hcon
    have h1 := congrFun hcon 1
    apply hj
    simpa using h1

/-! ## C. Units -/

/-- Physical dimensions are retained: with lengths scaled by `ℓ`, forces by `f`, and couples by
`ℓ * f`, the resultant scales by `f` and the moment about the scaled reference point by
`ℓ * f`. -/
lemma wrenchAbout_smul (ℓ f : ℝ) (r F C : ι → Fin 3 → ℝ) (O : Fin 3 → ℝ) :
    wrenchAbout (fun i => ℓ • r i) (fun i => f • F i) (fun i => (ℓ * f) • C i) (ℓ • O) =
      ⟨f • resultantForce F, (ℓ * f) • momentAbout r F C O⟩ := by
  have hs : ∀ u v : Fin 3 → ℝ, (ℓ • u) ⨯₃ (f • v) = (ℓ * f) • (u ⨯₃ v) := by
    intro u v
    rw [map_smul crossProduct ℓ u, LinearMap.smul_apply, map_smul (crossProduct u) f v,
      smul_smul]
  have hW : wrenchAbout (fun i => ℓ • r i) (fun i => f • F i) (fun i => (ℓ * f) • C i) (ℓ • O)
      = ⟨resultantForce (fun i => f • F i),
        momentAbout (fun i => ℓ • r i) (fun i => f • F i) (fun i => (ℓ * f) • C i)
          (ℓ • O)⟩ := rfl
  rw [hW]
  congr 1
  · exact Finset.smul_sum.symm
  · unfold momentAbout
    simp_rw [← smul_sub, hs, ← smul_add]
    exact Finset.smul_sum.symm

/-! ## D. Planar projection of the forces -/

/-- Components on the plane of the first two axes. -/
def planarPart (v : Fin 3 → ℝ) : Fin 2 → ℝ :=
  ![v 0, v 1]

/-- Force-only planar projection: the planar moment of the projected forces about the origin is the
third component of the moment about the origin of the forces alone, with the free couples discarded
(`C = 0`), since the planar moment carries no couples. -/
lemma moment2D_planarPart (r F : ι → Fin 3 → ℝ) :
    moment2D (fun i => planarPart (r i)) (fun i => planarPart (F i)) =
      momentAbout r F (fun _ => 0) 0 2 := by
  unfold moment2D momentAbout planarPart
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [cross_apply]

end Mechanics.EngineeringStatics

end
