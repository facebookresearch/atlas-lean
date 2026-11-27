/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.EngineeringStatics
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for `PhyslibExt.Mechanics.EngineeringStatics`

* a balanced couple: zero resultant and the moment `e₃` about every reference point;
* a single force: its moment changes with the reference point, the transport law predicts the
  change, and the units law rescales the moment;
* a force normal to the plane of the first two axes: its moment lies in that plane, and the
  planar projection loses it;
* a 3-4-5 triangle truss on a pin and a roller: a verified injective equilibrium matrix and the
  unique balance of the load `(8, -12)` at its apex;
* a two-bar collinear chain pinned at both ends (`m + r = 2 j`): a state of self-stress, hence a
  one-parameter family of balances for an axial load, and a transverse mechanism of the middle
  joint, hence no balance for a transverse load; the same chain on a pin and a roller
  (`m + r < 2 j`): injective (no self-stress), yet the same mechanism leaves the transverse load
  without balance.
-/

@[expose] public section

open scoped Matrix

namespace PhyslibExtTest.Mechanics.EngineeringStatics

open _root_.Mechanics.EngineeringStatics _root_.PhyslibExt.Mechanics.HarmonicMechanics

/-! ## A. A balanced couple -/

/-- A balanced couple: the force `e₂` at `e₁` and the force `-e₂` at the origin. -/
def couplePoint : Fin 2 → Fin 3 → ℝ :=
  ![![1, 0, 0], ![0, 0, 0]]

/-- The two opposite forces of the balanced couple. -/
def coupleForce : Fin 2 → Fin 3 → ℝ :=
  ![![0, 1, 0], ![0, -1, 0]]

/-- The balanced couple has zero resultant and the nonzero moment `e₃` about every reference
point. -/
lemma couple_fixture :
    resultantForce coupleForce = 0 ∧
      ∀ O : Fin 3 → ℝ, momentAbout couplePoint coupleForce (fun _ => 0) O = ![0, 0, 1] := by
  refine ⟨?_, ?_⟩
  · unfold resultantForce coupleForce
    rw [Fin.sum_univ_two]
    ext i
    fin_cases i <;> simp
  · intro O
    unfold momentAbout couplePoint coupleForce
    rw [Fin.sum_univ_two]
    ext j
    fin_cases j <;> simp [cross_apply]

-- Origin invariance from the zero resultant alone: the couple has the same moment about any two
-- reference points.
example (O O' : Fin 3 → ℝ) :
    momentAbout couplePoint coupleForce (fun _ => 0) O' =
      momentAbout couplePoint coupleForce (fun _ => 0) O :=
  momentAbout_eq_of_resultantForce_eq_zero couple_fixture.1 O O'

/-! ## B. A single force -/

/-- One force `e₂` applied at `e₁`, without couple. -/
def leverPoint : Fin 1 → Fin 3 → ℝ :=
  ![![1, 0, 0]]

/-- The single force of the lever fixture. -/
def leverForce : Fin 1 → Fin 3 → ℝ :=
  ![![0, 1, 0]]

/-- A nonzero resultant changes the origin moment: the force `e₂` at `e₁` has moment `e₃` about
the origin and moment `0` about its point of application. -/
lemma lever_fixture :
    resultantForce leverForce = ![0, 1, 0] ∧
      momentAbout leverPoint leverForce (fun _ => 0) 0 = ![0, 0, 1] ∧
      momentAbout leverPoint leverForce (fun _ => 0) ![1, 0, 0] = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold resultantForce leverForce
    rw [Fin.sum_univ_one, Matrix.cons_val_zero]
  · unfold momentAbout leverPoint leverForce
    rw [Fin.sum_univ_one]
    ext i
    fin_cases i <;> simp [cross_apply]
  · unfold momentAbout leverPoint leverForce
    rw [Fin.sum_univ_one]
    simp

-- The transport law predicts the moment about the point of application from the moment about
-- the origin: `e₃ + (0 - e₁) ⨯₃ e₂ = 0`.
example : momentAbout leverPoint leverForce (fun _ => 0) ![1, 0, 0] = 0 := by
  rw [momentAbout_eq_add_cross leverPoint leverForce (fun _ => 0) 0 ![1, 0, 0],
    lever_fixture.2.1, lever_fixture.1]
  ext i
  fin_cases i <;> simp [cross_apply]

-- A nonzero resultant: some reference point changes the moment about the origin.
example : ∃ O' : Fin 3 → ℝ,
    momentAbout leverPoint leverForce (fun _ => 0) O' ≠
      momentAbout leverPoint leverForce (fun _ => 0) 0 := by
  refine exists_momentAbout_ne_of_resultantForce_ne_zero ?_ 0
  rw [lever_fixture.1]
  intro h
  have h1 := congrFun h 1
  simp at h1

-- Units: in millimetres and kilonewtons (length factor `1000`, force factor `1 / 1000`) the
-- moment factor is `1000 * (1 / 1000) = 1`, so the moment about the origin is still `e₃`.
example :
    (wrenchAbout (fun i => (1000 : ℝ) • leverPoint i) (fun i => (1 / 1000 : ℝ) • leverForce i)
        (fun _ => ((1000 : ℝ) * (1 / 1000)) • (0 : Fin 3 → ℝ)) ((1000 : ℝ) • 0)).moment =
      ![0, 0, 1] := by
  rw [wrenchAbout_smul, lever_fixture.2.1]
  ext i
  fin_cases i <;> norm_num

-- The planar moment of the projected force is the third component `1` of its moment `e₃`.
example :
    moment2D (fun i => planarPart (leverPoint i)) (fun i => planarPart (leverForce i)) = 1 := by
  rw [moment2D_planarPart, lever_fixture.2.1]
  simp

/-! ## C. A force normal to the plane -/

/-- One force `e₃`, normal to the plane of the first two axes, applied at `e₂`. -/
def normalPoint : Fin 1 → Fin 3 → ℝ :=
  ![![0, 1, 0]]

/-- The single force of the planar-loss fixture. -/
def normalForce : Fin 1 → Fin 3 → ℝ :=
  ![![0, 0, 1]]

/-- A planar projection can lose an out-of-plane moment: the force `e₃` at `e₂` has moment `e₁`
about the origin, while its projection has zero planar resultant and zero planar moment. -/
lemma normal_fixture :
    momentAbout normalPoint normalForce (fun _ => 0) 0 = ![1, 0, 0] ∧
      resultantForce (fun i => planarPart (normalForce i)) = 0 ∧
      moment2D (fun i => planarPart (normalPoint i)) (fun i => planarPart (normalForce i)) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold momentAbout normalPoint normalForce
    rw [Fin.sum_univ_one]
    ext i
    fin_cases i <;> simp [cross_apply]
  · unfold resultantForce planarPart normalForce
    rw [Fin.sum_univ_one]
    ext i
    fin_cases i <;> simp
  · unfold moment2D planarPart normalPoint normalForce
    rw [Fin.sum_univ_one]
    simp

section Truss

open _root_.Mechanics.TrussCompatibility _root_.Mechanics.TrussEquilibrium

/-! ## D. A loaded triangle -/

/-- Joints of a 3-4-5 triangle: `(0, 0)`, `(4, 0)`, `(0, 3)`. -/
def triangleJoints : Fin 3 → (Fin 2 → ℝ) :=
  ![![0, 0], ![4, 0], ![0, 3]]

/-- First member endpoints `0, 1, 0` (members `0-1`, `1-2`, `0-2`). -/
def triangleTail : Fin 3 → Fin 3 :=
  ![0, 1, 0]

/-- Second member endpoints `1, 2, 2`. -/
def triangleHead : Fin 3 → Fin 3 :=
  ![1, 2, 2]

/-- A pin at joint `0` (two reactions) and a roller at joint `1`. -/
def triangleSupportJoint : Fin 3 → Fin 3 :=
  ![0, 0, 1]

/-- Reaction directions `x` and `y` at the pin, `y` at the roller. -/
def triangleSupportDir : Fin 3 → (Fin 2 → ℝ) :=
  ![![1, 0], ![0, 1], ![0, 1]]

/-- The load `(8, -12)` at the apex joint `2`. -/
def triangleLoad : Fin 3 × Fin 2 → ℝ :=
  fun q => ![![0, 0], ![0, 0], ![8, -12]] q.1 q.2

private lemma sqrt_of_sq {x y : ℝ} (hy : 0 ≤ y) (h : x = y ^ 2) : Real.sqrt x = y := by
  rw [h, Real.sqrt_sq hy]

private lemma sqrt9 : Real.sqrt 9 = 3 := sqrt_of_sq (by norm_num) (by norm_num)

private lemma sqrt16 : Real.sqrt 16 = 4 := sqrt_of_sq (by norm_num) (by norm_num)

private lemma sqrt25 : Real.sqrt 25 = 5 := sqrt_of_sq (by norm_num) (by norm_num)

/-- The triangle is square (`m + r = 6 = 2 j`), and its equilibrium matrix has injective
`mulVec` (explicitly verified full rank). -/
lemma triangle_injective :
    Fintype.card (Fin 3) + Fintype.card (Fin 3) = 2 * Fintype.card (Fin 3) ∧
      Function.Injective (equilibriumMatrix triangleJoints triangleTail triangleHead
        triangleSupportJoint triangleSupportDir).mulVec := by
  refine ⟨by simp, fun x y hxy => ?_⟩
  have hEq : equilibriumMatrix triangleJoints triangleTail triangleHead triangleSupportJoint
      triangleSupportDir *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  rw [← Sum.elim_comp_inl_inr (x - y)] at hEq
  have hb := (jointBalance_iff_mulVec triangleJoints triangleTail triangleHead
    triangleSupportJoint triangleSupportDir 0 _ _).2 hEq
  have e00 := hb 0 0
  have e01 := hb 0 1
  have e10 := hb 1 0
  have e11 := hb 1 1
  have e20 := hb 2 0
  have e21 := hb 2 1
  simp [triangleJoints, triangleTail, triangleHead, triangleSupportJoint, triangleSupportDir,
    axialEndpointForce, memberLength, endpointJoint, Fintype.sum_prod_type, Fin.sum_univ_three]
    at e00 e01 e10 e11 e20 e21
  norm_num [sqrt9, sqrt16, sqrt25] at e00 e01 e10 e11 e20 e21
  funext u
  rcases u with i | i <;> fin_cases i <;> simp <;> linarith

/-- The unique balance of the loaded triangle: member forces `8` (member `0-1`, tension), `-10`
(member `1-2`, compression) and `-6` (member `0-2`, compression); pin reactions `-8` and `6`,
roller reaction `6`. -/
lemma triangle_jointBalance_iff (N ρ : Fin 3 → ℝ) :
    JointBalance triangleJoints triangleTail triangleHead triangleSupportJoint triangleSupportDir
        triangleLoad N ρ ↔ N = ![8, -10, -6] ∧ ρ = ![-8, 6, 6] := by
  have hsol : JointBalance triangleJoints triangleTail triangleHead triangleSupportJoint
      triangleSupportDir triangleLoad ![8, -10, -6] ![-8, 6, 6] := by
    intro j k
    fin_cases j <;> fin_cases k <;>
      simp [triangleJoints, triangleTail, triangleHead, triangleSupportJoint,
        triangleSupportDir, triangleLoad, axialEndpointForce, memberLength, endpointJoint,
        Fintype.sum_prod_type, Fin.sum_univ_three] <;>
      norm_num [sqrt9, sqrt16, sqrt25]
  constructor
  · intro h
    exact jointBalance_unique_of_injective triangle_injective.2 h hsol
  · rintro ⟨rfl, rfl⟩
    exact hsol

-- Square and injective: the triangle has exactly one balance for every joint load.
example (f : Fin 3 × Fin 2 → ℝ) :
    ∃! p : (Fin 3 → ℝ) × (Fin 3 → ℝ), JointBalance triangleJoints triangleTail triangleHead
      triangleSupportJoint triangleSupportDir f p.1 p.2 :=
  jointBalance_existsUnique_of_injective _ _ _ _ _ triangle_injective.1 triangle_injective.2 f

-- The rank test passes for the triangle load, which has a balance.
example :
    (equilibriumMatrix triangleJoints triangleTail triangleHead triangleSupportJoint
        triangleSupportDir).rank =
      (Matrix.of (fun i => Sum.elim (equilibriumMatrix triangleJoints triangleTail triangleHead
        triangleSupportJoint triangleSupportDir i) (fun _ : Fin 1 => triangleLoad i)) :
          Matrix (Fin 3 × Fin 2) ((Fin 3 ⊕ Fin 3) ⊕ Fin 1) ℝ).rank :=
  (exists_jointBalance_iff_rank _ _ _ _ _ _).1
    ⟨_, _, (triangle_jointBalance_iff _ _).2 ⟨rfl, rfl⟩⟩

-- Injectivity rules out coincident member endpoints: every triangle member has two distinct ends.
example (e : Fin 3) : triangleJoints (triangleTail e) ≠ triangleJoints (triangleHead e) :=
  endpoints_ne_of_injective triangle_injective.2 e

/-! ## E. A collinear chain: self-stress and mechanism -/

/-- Joints of a two-bar collinear chain: `(0, 0)`, `(1, 0)`, `(2, 0)`. -/
def chainJoints : Fin 3 → (Fin 2 → ℝ) :=
  ![![0, 0], ![1, 0], ![2, 0]]

/-- First member endpoints `0, 1` (members `0-1`, `1-2`). -/
def chainTail : Fin 2 → Fin 3 :=
  ![0, 1]

/-- Second member endpoints `1, 2`. -/
def chainHead : Fin 2 → Fin 3 :=
  ![1, 2]

/-- Pins at joints `0` and `2`: reactions along `x` and `y` at each (`m + r = 6 = 2 j`). -/
def pinnedSupportJoint : Fin 4 → Fin 3 :=
  ![0, 0, 2, 2]

/-- Reaction directions of the two pins. -/
def pinnedSupportDir : Fin 4 → (Fin 2 → ℝ) :=
  ![![1, 0], ![0, 1], ![1, 0], ![0, 1]]

/-- A pin at joint `0` and a roller at joint `2` (`m + r = 5 < 2 j`). -/
def rollerSupportJoint : Fin 3 → Fin 3 :=
  ![0, 0, 2]

/-- Reaction directions `x`, `y` at the pin and `y` at the roller. -/
def rollerSupportDir : Fin 3 → (Fin 2 → ℝ) :=
  ![![1, 0], ![0, 1], ![0, 1]]

/-- A unit transverse load `(0, -1)` at the middle joint. -/
def transverseLoad : Fin 3 × Fin 2 → ℝ :=
  fun q => ![![0, 0], ![0, -1], ![0, 0]] q.1 q.2

/-- An axial load `(3, 0)` at the middle joint. -/
def axialLoad : Fin 3 × Fin 2 → ℝ :=
  fun q => ![![0, 0], ![3, 0], ![0, 0]] q.1 q.2

/-- Singular geometry: the pinned chain has `m + r = 2 j`, yet the self-stress `N = (1, 1)`,
`ρ = (-1, 0, 1, 0)` balances zero loads, so its equilibrium matrix is not injective. -/
lemma chain_not_injective :
    Fintype.card (Fin 2) + Fintype.card (Fin 4) = 2 * Fintype.card (Fin 3) ∧
      JointBalance chainJoints chainTail chainHead pinnedSupportJoint pinnedSupportDir 0
        ![1, 1] ![-1, 0, 1, 0] ∧
      ¬ Function.Injective (equilibriumMatrix chainJoints chainTail chainHead pinnedSupportJoint
        pinnedSupportDir).mulVec := by
  have hself : JointBalance chainJoints chainTail chainHead pinnedSupportJoint pinnedSupportDir 0
      ![1, 1] ![-1, 0, 1, 0] := by
    intro j k
    fin_cases j <;> fin_cases k <;>
      norm_num [chainJoints, chainTail, chainHead, pinnedSupportJoint, pinnedSupportDir,
        axialEndpointForce, memberLength, endpointJoint, Fintype.sum_prod_type,
        Fin.sum_univ_two, Fin.sum_univ_four]
  refine ⟨by simp, hself, fun hinj => ?_⟩
  have hzero : JointBalance chainJoints chainTail chainHead pinnedSupportJoint pinnedSupportDir 0
      0 0 := by
    intro j k
    simp [axialEndpointForce]
  have := (jointBalance_unique_of_injective hinj hself hzero).1
  have h0 := congrFun this 0
  simp at h0

/-- No balance: the transverse load at the middle joint of the pinned chain has no balancing
pair, and the rank test fails (`rank A ≠ rank (A | f)`). -/
lemma chain_transverse_no_balance :
    (¬ ∃ (N : Fin 2 → ℝ) (ρ : Fin 4 → ℝ), JointBalance chainJoints chainTail chainHead
        pinnedSupportJoint pinnedSupportDir transverseLoad N ρ) ∧
      (equilibriumMatrix chainJoints chainTail chainHead pinnedSupportJoint pinnedSupportDir).rank ≠
        (Matrix.of (fun i => Sum.elim (equilibriumMatrix chainJoints chainTail chainHead
          pinnedSupportJoint pinnedSupportDir i) (fun _ : Fin 1 => transverseLoad i)) :
            Matrix (Fin 3 × Fin 2) ((Fin 2 ⊕ Fin 4) ⊕ Fin 1) ℝ).rank := by
  have hno : ¬ ∃ (N : Fin 2 → ℝ) (ρ : Fin 4 → ℝ), JointBalance chainJoints chainTail chainHead
      pinnedSupportJoint pinnedSupportDir transverseLoad N ρ := by
    rintro ⟨N, ρ, h⟩
    have h11 := h 1 1
    simp [chainJoints, chainTail, chainHead, pinnedSupportJoint, pinnedSupportDir,
      transverseLoad, axialEndpointForce, endpointJoint, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_four] at h11
  exact ⟨hno, fun h => hno ((exists_jointBalance_iff_rank _ _ _ _ _ _).2 h)⟩

/-- A nonunique compatible family: the axial load at the middle joint of the pinned chain is
balanced by `N = (3, 0)`, `ρ = (-3, 0, 0, 0)` plus every multiple `μ` of the self-stress. -/
lemma chain_axial_family (μ : ℝ) :
    JointBalance chainJoints chainTail chainHead pinnedSupportJoint pinnedSupportDir axialLoad
      (![3, 0] + μ • ![1, 1]) (![-3, 0, 0, 0] + μ • ![-1, 0, 1, 0]) := by
  intro j k
  fin_cases j <;> fin_cases k <;>
    simp [chainJoints, chainTail, chainHead, pinnedSupportJoint, pinnedSupportDir, axialLoad,
      axialEndpointForce, memberLength, endpointJoint, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_four] <;>
    ring

/-- Full column rank alone is not enough: the chain on a pin and a roller has `m + r = 5 < 2 j`
and an injective equilibrium matrix, but the transverse load still has no balance. -/
lemma rollerChain_injective_no_balance :
    Fintype.card (Fin 2) + Fintype.card (Fin 3) < 2 * Fintype.card (Fin 3) ∧
      Function.Injective (equilibriumMatrix chainJoints chainTail chainHead rollerSupportJoint
        rollerSupportDir).mulVec ∧
      ¬ ∃ (N : Fin 2 → ℝ) (ρ : Fin 3 → ℝ), JointBalance chainJoints chainTail chainHead
        rollerSupportJoint rollerSupportDir transverseLoad N ρ := by
  refine ⟨by simp, fun x y hxy => ?_, ?_⟩
  · have hEq : equilibriumMatrix chainJoints chainTail chainHead rollerSupportJoint
        rollerSupportDir *ᵥ (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    rw [← Sum.elim_comp_inl_inr (x - y)] at hEq
    have hb := (jointBalance_iff_mulVec chainJoints chainTail chainHead rollerSupportJoint
      rollerSupportDir 0 _ _).2 hEq
    have e00 := hb 0 0
    have e01 := hb 0 1
    have e10 := hb 1 0
    have e20 := hb 2 0
    have e21 := hb 2 1
    norm_num [chainJoints, chainTail, chainHead, rollerSupportJoint, rollerSupportDir,
      axialEndpointForce, memberLength, endpointJoint, Fintype.sum_prod_type, Fin.sum_univ_two,
      Fin.sum_univ_three] at e00 e01 e10 e20 e21
    funext u
    rcases u with i | i <;> fin_cases i <;> simp <;> linarith
  · rintro ⟨N, ρ, h⟩
    have h11 := h 1 1
    simp [chainJoints, chainTail, chainHead, rollerSupportJoint, rollerSupportDir,
      transverseLoad, axialEndpointForce, endpointJoint, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_three] at h11

-- The axial load has a balance but not a unique one: `μ = 0` and `μ = 1` give two.
example : ¬ ∃! p : (Fin 2 → ℝ) × (Fin 4 → ℝ), JointBalance chainJoints chainTail chainHead
    pinnedSupportJoint pinnedSupportDir axialLoad p.1 p.2 := by
  rintro ⟨p, -, huniq⟩
  have h0 := huniq (_, _) (chain_axial_family 0)
  have h1 := huniq (_, _) (chain_axial_family 1)
  have h := congrArg (fun q => q.1 1) (h0.trans h1.symm)
  norm_num at h

end Truss

end PhyslibExtTest.Mechanics.EngineeringStatics

end
