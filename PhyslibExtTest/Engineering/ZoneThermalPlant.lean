/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Engineering.ZoneThermalPlant
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import PhyslibExt.Engineering.ZoneHeatInventory
import PhyslibExt.Engineering.ZoneQuadraticDissipation
import PhyslibExt.Mechanics.HarmonicMechanics

/-!
# Tests for `PhyslibExt.Engineering.ZoneThermalPlant`

Owner-record transport, the output map and matrix round trip, the
heat-inventory and quadratic-dissipation contracts, two-zone witnesses with
unequal capacities and with outside-temperature and heater channels, invalid
controls, and agreement with the grounded stiffness matrix without
self-links.
-/

@[expose] public section

namespace PhyslibExtTest.Engineering.ZoneThermalPlant

open _root_.ZoneHeatInventory
open Matrix
open PhyslibExt.Mechanics.HarmonicMechanics

#print axioms ZoneHeatInventory.thermal_trajectory_iff

/-- The statement of `thermal_trajectory_iff` with its premise removed. -/
private def plantTrajectoryStmt {ι : Type*} [Fintype ι] [DecidableEq ι] (C : ι → ℝ)
    (G : ι → ι → ℝ) (g0 : ι → ℝ)
    (T : ι → ℝ → ℝ) (Tout : ℝ → ℝ) (P : ι → ℝ → ℝ) : Prop :=
  (∀ t, HasDerivAt (fun s i => T i s)
      (thermalA C G g0 *ᵥ (fun i => T i t) +
        thermalB C g0 *ᵥ Sum.elim (fun _ => Tout t) (fun i => P i t)) t) ↔
    ∀ t i, ∃ Tv, HasDerivAt (T i) Tv t ∧
      C i * Tv = (∑ j, G i j * (T j t - T i t)) + g0 i * (Tout t - T i t) + P i t


/-! ## A. Owner record and trajectory correspondence -/

/-- ownerForm_trajectory_iff: owner-record form through `thermalPlant`. -/
private lemma ownerForm_trajectory_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {C : ι → ℝ}
    {G : ι → ι → ℝ}
    {g0 : ι → ℝ} (hC : ∀ i, 0 < C i) (T : ι → ℝ → ℝ) (Tout : ℝ → ℝ) (P : ι → ℝ → ℝ) :
    (∀ t, HasDerivAt (fun s i => T i s)
        ((thermalPlant C G g0).A (fun i => T i t) +
          (thermalPlant C G g0).B (Sum.elim (fun _ => Tout t) (fun i => P i t))) t) ↔
      ∀ t i, ∃ Tv, HasDerivAt (T i) Tv t ∧
        C i * Tv = (∑ j, G i j * (T j t - T i t)) + g0 i * (Tout t - T i t) + P i t := by
  simp only [thermalPlant, ControlTheory.StateSpaceCoeffs.ofMatrix_A_apply,
    ControlTheory.StateSpaceCoeffs.ofMatrix_B_apply]
  exact thermal_trajectory_iff hC T Tout P

-- the the correspondence docstring claim verbatim: for `S = ofMatrix` of the four matrices, with
-- `z = fun s i => T i s` and `w = fun s => Sum.elim …`, the inline owner condition reduces by
-- `simp only [ofMatrix_A_apply, ofMatrix_B_apply]` to the correspondence's left side; `rw` does not
-- fire under the
-- binder.
example {ι : Type*} [Fintype ι] [DecidableEq ι] {C : ι → ℝ} {G : ι → ι → ℝ}
    {g0 : ι → ℝ} (hC : ∀ i, 0 < C i) (T : ι → ℝ → ℝ) (Tout : ℝ → ℝ) (P : ι → ℝ → ℝ) :
    (∀ t, HasDerivAt (fun s i => T i s)
        ((ControlTheory.StateSpaceCoeffs.ofMatrix (thermalA C G g0) (thermalB C g0) thermalC
            thermalD).A ((fun s i => T i s) t) +
          (ControlTheory.StateSpaceCoeffs.ofMatrix (thermalA C G g0) (thermalB C g0) thermalC
            thermalD).B ((fun s => Sum.elim (fun _ => Tout s) (fun i => P i s)) t)) t) ↔
      ∀ t i, ∃ Tv, HasDerivAt (T i) Tv t ∧
        C i * Tv = (∑ j, G i j * (T j t - T i t)) + g0 i * (Tout t - T i t) + P i t := by
  fail_if_success rw [ControlTheory.StateSpaceCoeffs.ofMatrix_A_apply]
  simp only [ControlTheory.StateSpaceCoeffs.ofMatrix_A_apply,
    ControlTheory.StateSpaceCoeffs.ofMatrix_B_apply]
  exact thermal_trajectory_iff hC T Tout P

-- arbitrary owner state curve `z` and input curve `w`; the curve form of the correspondence loses
-- nothing.
example {ι : Type*} [Fintype ι] [DecidableEq ι] {C : ι → ℝ} {G : ι → ι → ℝ}
    {g0 : ι → ℝ} (hC : ∀ i, 0 < C i) (z : ℝ → ι → ℝ) (w : ℝ → Unit ⊕ ι → ℝ) :
    (∀ t, HasDerivAt z ((thermalPlant C G g0).A (z t) + (thermalPlant C G g0).B (w t)) t) ↔
      ∀ t i, ∃ Tv, HasDerivAt (fun s => z s i) Tv t ∧
        C i * Tv = (∑ j, G i j * (z t j - z t i)) + g0 i * (w t (Sum.inl ()) - z t i)
          + w t (Sum.inr i) := by
  have hw : ∀ t, Sum.elim (fun _ => w t (Sum.inl ())) (fun i => w t (Sum.inr i)) = w t := by
    intro t
    funext x
    rcases x with u | i
    · cases u
      rfl
    · rfl
  have h := ownerForm_trajectory_iff (G := G) (g0 := g0) hC (fun i s => z s i)
    (fun s => w s (Sum.inl ()))
    (fun i s => w s (Sum.inr i))
  simp only [hw] at h
  exact h

-- owner-record output is the zone temperature vector, no feedthrough.
example {ι : Type*} [Fintype ι] [DecidableEq ι] (C : ι → ℝ) (G : ι → ι → ℝ)
    (g0 : ι → ℝ) (x : ι → ℝ) (w : Unit ⊕ ι → ℝ) :
    (thermalPlant C G g0).C x + (thermalPlant C G g0).D w = x := by
  rw [thermalPlant, ControlTheory.StateSpaceCoeffs.ofMatrix_C_apply,
    ControlTheory.StateSpaceCoeffs.ofMatrix_D_apply, thermalC, thermalD, one_mulVec,
    zero_mulVec, add_zero]

-- `toMatrix` round trip.
example {ι : Type*} [Fintype ι] [DecidableEq ι] (C : ι → ℝ) (G : ι → ι → ℝ)
    (g0 : ι → ℝ) :
    ControlTheory.StateSpaceCoeffs.toMatrix (thermalPlant C G g0) =
      (thermalA C G g0, thermalB C g0, thermalC, thermalD) := by
  rw [thermalPlant, ControlTheory.StateSpaceCoeffs.toMatrix_ofMatrix]

-- input contract the heat-inventory producer, forward: a plant trajectory with reciprocal
-- conductances gives
-- the heat-inventory producer's heat-inventory balance with boundary input `g0 i * (Tout - T i)`.
example {ι : Type*} [Fintype ι] [DecidableEq ι] {C : ι → ℝ} {G : ι → ι → ℝ}
    {g0 : ι → ℝ} (hC : ∀ i, 0 < C i) (hG : ∀ i j, G i j = G j i) {T : ι → ℝ → ℝ}
    {Tout : ℝ → ℝ} {P : ι → ℝ → ℝ}
    (hplant : ∀ t, HasDerivAt (fun s i => T i s)
        (thermalA C G g0 *ᵥ (fun i => T i t) +
          thermalB C g0 *ᵥ Sum.elim (fun _ => Tout t) (fun i => P i t)) t) (t : ℝ) :
    HasDerivAt (fun s => ∑ i, C i * T i s) (∑ i, (g0 i * (Tout t - T i t) + P i t)) t := by
  have h := (thermal_trajectory_iff hC T Tout P).mp hplant
  choose Tv hT hzone using h
  exact heat_inventory_deriv C G T (fun i s => Tv s i) (fun i s => g0 i * (Tout s - T i s)) P
    hG (fun i s => hT s i) (fun i s => hzone s i) t

-- input contract the heat-inventory producer, reverse: the heat-inventory producer's hypotheses
-- with boundary input
-- `b i t = g0 i * (Tout t - T i t)` give a plant trajectory (beta reduction only).
example {ι : Type*} [Fintype ι] [DecidableEq ι] {C : ι → ℝ} {G : ι → ι → ℝ}
    {g0 : ι → ℝ} (hC : ∀ i, 0 < C i) {T Tv P : ι → ℝ → ℝ} {Tout : ℝ → ℝ}
    (hT : ∀ i t, HasDerivAt (T i) (Tv i t) t)
    (hzone : ∀ i t, C i * Tv i t
      = (∑ j, G i j * (T j t - T i t)) + (fun i t => g0 i * (Tout t - T i t)) i t + P i t) :
    ∀ t, HasDerivAt (fun s i => T i s)
      (thermalA C G g0 *ᵥ (fun i => T i t) +
        thermalB C g0 *ᵥ Sum.elim (fun _ => Tout t) (fun i => P i t)) t :=
  (thermal_trajectory_iff hC T Tout P).mpr fun t i => ⟨Tv i t, hT i t, hzone i t⟩

-- consistency with the quadratic-dissipation producer at a constant outside temperature.
example {ι : Type*} [Fintype ι] [DecidableEq ι] {C : ι → ℝ} {G : ι → ι → ℝ}
    {g0 : ι → ℝ} (hC : ∀ i, 0 < C i) (hG : ∀ i j, G i j = G j i) {T P : ι → ℝ → ℝ}
    (Tout : ℝ)
    (hplant : ∀ t, HasDerivAt (fun s i => T i s)
        (thermalA C G g0 *ᵥ (fun i => T i t) +
          thermalB C g0 *ᵥ Sum.elim (fun _ => Tout) (fun i => P i t)) t) (t : ℝ) :
    HasDerivAt (fun s => (1 / 2) * ∑ i, C i * (T i s - Tout) ^ 2)
      (-((1 / 2) * ∑ i, ∑ j, G i j * (T j t - T i t) ^ 2
        + ∑ i, g0 i * (T i t - Tout) ^ 2)
        + ∑ i, (T i t - Tout) * P i t) t := by
  have h := (thermal_trajectory_iff hC T (fun _ => Tout) P).mp hplant
  choose Tv hT hzone using h
  exact quadratic_dissipation_deriv C G g0 Tout T (fun i s => Tv s i) P hG
    (fun i s => hT s i) (fun i s => hzone s i) t

/-! ## B. Domain: only `C i ≠ 0` is used; `C = 0` breaks the correspondence -/

/-- Generalization: the correspondence for `C i ≠ 0` (same route as the pin proof). -/
private lemma plantTrajectoryStmt_of_ne {ι : Type*} [Fintype ι] [DecidableEq ι] {C : ι → ℝ}
    {G : ι → ι → ℝ}
    {g0 : ι → ℝ} (hC : ∀ i, C i ≠ 0) (T : ι → ℝ → ℝ) (Tout : ℝ → ℝ) (P : ι → ℝ → ℝ) :
    plantTrajectoryStmt C G g0 T Tout P := by
  have hrow : ∀ t i, C i * (thermalA C G g0 *ᵥ (fun i => T i t) +
      thermalB C g0 *ᵥ Sum.elim (fun _ => Tout t) (fun i => P i t)) i =
      (∑ j, G i j * (T j t - T i t)) + g0 i * (Tout t - T i t) + P i t := by
    intro t i
    have hCi : C i ≠ 0 := hC i
    have hsum : (∑ j, G i j * (T j t - T i t)) =
        (∑ j, G i j * T j t) - (∑ j, G i j) * T i t := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [thermalA, thermalB, Pi.add_apply, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal,
      Matrix.sub_mulVec, Matrix.fromCols_mulVec_sumElim, Matrix.one_mulVec, Pi.sub_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Matrix.replicateCol_apply,
      Fintype.sum_unique]
    rw [hsum]
    field_simp
    ring
  constructor
  · intro h t i
    exact ⟨_, hasDerivAt_pi.mp (h t) i, hrow t i⟩
  · intro h t
    refine hasDerivAt_pi.mpr fun i => ?_
    obtain ⟨Tv, hTv, heq⟩ := h t i
    have hv : Tv = (thermalA C G g0 *ᵥ (fun i => T i t) +
        thermalB C g0 *ᵥ Sum.elim (fun _ => Tout t) (fun i => P i t)) i :=
      mul_left_cancel₀ (hC i) (heq.trans (hrow t i).symm)
    exact hv ▸ hTv

-- Negative capacities: the identity still holds (the sign is the physical domain only).
example (G : Unit → Unit → ℝ) (g0 : Unit → ℝ) (T : Unit → ℝ → ℝ)
    (Tout : ℝ → ℝ) (P : Unit → ℝ → ℝ) : plantTrajectoryStmt (fun _ => (-1 : ℝ)) G g0 T Tout P :=
  plantTrajectoryStmt_of_ne (fun _ => by norm_num) T Tout P

-- Control: at `C = 0` (one zone, no links, no inputs, `T = id`) the zone-equation side holds with
-- `Tv = 1` but the plant derivative is `0`: the correspondence fails, so `hC` is needed.
example :
    ¬ plantTrajectoryStmt (fun _ : Unit => (0 : ℝ)) (fun _ _ => 0) (fun _ => 0)
      (fun _ s => s) (fun _ => 0)
      (fun _ _ => 0) := by
  intro h
  have hR : ∀ (t : ℝ) (i : Unit), ∃ Tv, HasDerivAt ((fun (_ : Unit) (s : ℝ) => s) i) Tv t ∧
      (fun _ : Unit => (0 : ℝ)) i * Tv =
        (∑ j, (fun (_ : Unit) (_ : Unit) => (0 : ℝ)) i j *
          ((fun (_ : Unit) (s : ℝ) => s) j t - (fun (_ : Unit) (s : ℝ) => s) i t)) +
        (fun _ : Unit => (0 : ℝ)) i * ((fun _ : ℝ => (0 : ℝ)) t - (fun (_ : Unit) (s : ℝ) => s) i t)
        + (fun (_ : Unit) (_ : ℝ) => (0 : ℝ)) i t :=
    fun t _ => ⟨1, hasDerivAt_id t, by simp⟩
  have hL := h.mpr hR 0
  have hc : HasDerivAt (fun s (_ : Unit) => s) (fun _ => (1 : ℝ)) 0 :=
    hasDerivAt_pi.mpr fun _ => hasDerivAt_id 0
  have hu := hL.unique hc
  have h1 := congrFun hu ()
  simp [thermalA, thermalB] at h1

/-! ## C. Focused check 1: two unequal capacities -/

/-- The two-zone link of conductance `2`. -/
private def linkTwo : Fin 2 → Fin 2 → ℝ := fun i j => if i = j then 0 else 2

-- finite read-off: `C = (1, 2)`, one link of conductance `2`, no envelope.
example : thermalA ![1, 2] linkTwo 0 = !![-2, 2; 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [thermalA, linkTwo, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_two]

private lemma hasDerivAt_exp_neg_three (t : ℝ) :
    HasDerivAt (fun s => Real.exp (-3 * s)) (-3 * Real.exp (-3 * t)) t := by
  have h := ((hasDerivAt_id t).const_mul (-3 : ℝ)).exp
  simp only [id, mul_one] at h
  convert h using 1
  ring

/-- The relaxing two-zone curve `(1 + 2 e^{-3s}, 1 - e^{-3s})`. -/
private noncomputable def relaxingCurve : Fin 2 → ℝ → ℝ :=
  ![fun s => 1 + 2 * Real.exp (-3 * s), fun s => 1 - Real.exp (-3 * s)]

/-- witness: the relaxing curve is a trajectory of the unequal-capacity plant. -/
private lemma relaxingCurve_trajectory : ∀ t, HasDerivAt (fun s i => relaxingCurve i s)
    (thermalA ![1, 2] linkTwo 0 *ᵥ (fun i => relaxingCurve i t) +
      thermalB ![1, 2] 0 *ᵥ Sum.elim (fun _ => (fun _ => (0 : ℝ)) t)
        (fun i => (fun (_ : Fin 2) (_ : ℝ) => (0 : ℝ)) i t)) t := by
  refine (thermal_trajectory_iff (C := ![1, 2]) (G := linkTwo) (g0 := 0)
    (by intro i; fin_cases i <;> norm_num) relaxingCurve (fun _ => 0) (fun _ _ => 0)).mpr ?_
  intro t i
  fin_cases i
  · refine ⟨-6 * Real.exp (-3 * t), ?_, ?_⟩
    · show HasDerivAt (fun s => 1 + 2 * Real.exp (-3 * s)) (-6 * Real.exp (-3 * t)) t
      exact (((hasDerivAt_exp_neg_three t).const_mul (2 : ℝ)).const_add 1).congr_deriv
        (by ring)
    · simp [relaxingCurve, linkTwo, Fin.sum_univ_two]
      ring
  · refine ⟨3 * Real.exp (-3 * t), ?_, ?_⟩
    · show HasDerivAt (fun s => 1 - Real.exp (-3 * s)) (3 * Real.exp (-3 * t)) t
      exact ((hasDerivAt_exp_neg_three t).const_sub 1).congr_deriv (by ring)
    · simp [relaxingCurve, linkTwo, Fin.sum_univ_two]
      ring

-- control: the column-normalized matrix `(G - diag) * diag (1 / C)` does not carry the
-- same curve, so the correspondence forces row `i` to be zone equation `i` divided by `C i`.
example :
    ¬ ∀ t, HasDerivAt (fun s i => relaxingCurve i s)
      (((of linkTwo - diagonal fun i => (∑ j, linkTwo i j) + (0 : Fin 2 → ℝ) i) *
        diagonal (fun i => 1 / (![1, 2] : Fin 2 → ℝ) i)) *ᵥ (fun i => relaxingCurve i t)) t := by
  intro h
  have hu := (relaxingCurve_trajectory 0).unique (h 0)
  have h1 := congrFun hu 1
  simp [relaxingCurve, linkTwo, thermalA, thermalB, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.mul_apply, Matrix.diagonal_apply] at h1
  norm_num at h1

-- control: with equal capacities `(2, 2)` the same curve is not a trajectory.
example :
    ¬ ∀ t, HasDerivAt (fun s i => relaxingCurve i s)
      (thermalA ![2, 2] linkTwo 0 *ᵥ (fun i => relaxingCurve i t) +
        thermalB ![2, 2] 0 *ᵥ Sum.elim (fun _ => (0 : ℝ)) (fun _ => 0)) t := by
  intro h
  have hu := (relaxingCurve_trajectory 0).unique (h 0)
  have h0 := congrFun hu 0
  simp [relaxingCurve, linkTwo, thermalA, thermalB, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.mul_apply, Matrix.diagonal_apply] at h0
  norm_num at h0

/-! ## D. Focused check 2: outside-temperature and heater channels -/

-- Channel entries (universal): the outside column has gain `g0 i / C i`; the heater of zone
-- `j` enters only zone `j`, with gain `1 / C j`.
example {ι : Type*} [Fintype ι] [DecidableEq ι] (C g0 : ι → ℝ) (i j : ι) :
    thermalB C g0 i (Sum.inl ()) = g0 i / C i ∧
      thermalB C g0 i (Sum.inr j) = if i = j then 1 / C i else 0 := by
  constructor
  · simp [thermalB, Matrix.diagonal_mul, div_eq_inv_mul]
  · by_cases hij : i = j
    · subst hij
      simp [thermalB, Matrix.diagonal_mul]
    · simp [thermalB, Matrix.diagonal_mul, hij]

-- finite read-off: `C = (2, 3)`, `g0 = (1, 0)` (the second zone has no envelope path).
example :
    thermalB ![2, 3] ![1, 0] 0 (Sum.inl ()) = 1 / 2 ∧ thermalB ![2, 3] ![1, 0] 1 (Sum.inl ()) = 0 ∧
      thermalB ![2, 3] ![1, 0] 0 (Sum.inr 0) = 1 / 2 ∧
      thermalB ![2, 3] ![1, 0] 1 (Sum.inr 0) = 0 ∧
      thermalB ![2, 3] ![1, 0] 0 (Sum.inr 1) = 0 ∧
      thermalB ![2, 3] ![1, 0] 1 (Sum.inr 1) = 1 / 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [thermalB, Matrix.diagonal_mul]

/-- The two-zone link of conductance `1`. -/
private def linkOne : Fin 2 → Fin 2 → ℝ := fun i j => if i = j then 0 else 1

-- steady state: `T = (9, 9)` at `Tout = 5` with heater power `4` in the envelope zone is
-- at rest.
example : ∀ t, HasDerivAt (fun s (i : Fin 2) => (fun (_ : Fin 2) (_ : ℝ) => (9 : ℝ)) i s)
    (thermalA ![2, 3] linkOne ![1, 0] *ᵥ (fun i => (fun (_ : Fin 2) (_ : ℝ) => (9 : ℝ)) i t) +
      thermalB ![2, 3] ![1, 0] *ᵥ Sum.elim (fun _ => (fun _ => (5 : ℝ)) t)
        (fun i => (![fun _ => 4, fun _ => 0] : Fin 2 → ℝ → ℝ) i t)) t := by
  refine (thermal_trajectory_iff (C := ![2, 3]) (G := linkOne) (g0 := ![1, 0])
    (by intro i; fin_cases i <;> norm_num) (fun _ _ => 9) (fun _ => 5)
    ![fun _ => 4, fun _ => 0]).mpr ?_
  intro t i
  refine ⟨0, hasDerivAt_const t 9, ?_⟩
  fin_cases i <;> norm_num [linkOne, Fin.sum_univ_two]

-- Uniform rest (universal): any network with no heating at a constant outside temperature
-- equal to the uniform zone temperature is at rest.
example {ι : Type*} [Fintype ι] [DecidableEq ι] {C : ι → ℝ} (G : ι → ι → ℝ)
    (g0 : ι → ℝ) (hC : ∀ i, 0 < C i) (c : ℝ) :
    ∀ t, HasDerivAt (fun s (i : ι) => (fun (_ : ι) (_ : ℝ) => c) i s)
      (thermalA C G g0 *ᵥ (fun i => (fun (_ : ι) (_ : ℝ) => c) i t) +
        thermalB C g0 *ᵥ Sum.elim (fun _ => (fun _ => c) t)
          (fun i => (fun (_ : ι) (_ : ℝ) => (0 : ℝ)) i t)) t :=
  (thermal_trajectory_iff hC (fun _ _ => c) (fun _ => c) (fun _ _ => 0)).mpr fun t _ =>
    ⟨0, hasDerivAt_const t c, by simp⟩

-- Insulated uniform mode: with no envelope paths and no heating, a uniform state rests for
-- every outside temperature.
example {ι : Type*} [Fintype ι] [DecidableEq ι] {C : ι → ℝ}
    (G : ι → ι → ℝ) (hC : ∀ i, 0 < C i) (c : ℝ) (Tout : ℝ → ℝ) :
    ∀ t, HasDerivAt (fun s (i : ι) => (fun (_ : ι) (_ : ℝ) => c) i s)
      (thermalA C G 0 *ᵥ (fun i => (fun (_ : ι) (_ : ℝ) => c) i t) +
        thermalB C 0 *ᵥ Sum.elim (fun _ => Tout t)
          (fun i => (fun (_ : ι) (_ : ℝ) => (0 : ℝ)) i t)) t :=
  (thermal_trajectory_iff hC (fun _ _ => c) Tout (fun _ _ => 0)).mpr fun t _ =>
    ⟨0, hasDerivAt_const t c, by simp⟩

-- Wrong-sign control: with the outside column negated, the uniform state at the outside
-- temperature is no longer at rest (one zone, `C = g0 = 1`, `T = Tout = 1`).
example :
    ¬ ∀ t, HasDerivAt (fun s (_ : Unit) => (fun (_ : ℝ) => (1 : ℝ)) s)
      (thermalA (fun _ => (1 : ℝ)) (fun _ _ => 0) (fun _ => 1) *ᵥ (fun _ => 1) +
        (diagonal (fun _ : Unit => (1 : ℝ) / 1) *
          fromCols (replicateCol Unit (-(fun _ : Unit => (1 : ℝ)))) (1 : Matrix Unit Unit ℝ)) *ᵥ
          Sum.elim (fun _ => (1 : ℝ)) (fun _ => 0)) t := by
  intro h
  have hu := (h 0).unique (hasDerivAt_const (0 : ℝ) (fun _ : Unit => (1 : ℝ)))
  have h1 := congrFun hu ()
  simp [thermalA, Matrix.mulVec, dotProduct, Matrix.fromCols, Matrix.replicateCol] at h1

-- Witness with every channel live: unequal capacities, nonzero exchange, a time-varying
-- outside temperature through the envelope zone and a heater in the zone without envelope path.
example : ∀ t, HasDerivAt (fun s i =>
      (![fun s => 2 * s, fun s => 2 * s + 1] : Fin 2 → ℝ → ℝ) i s)
    (thermalA ![1, 2] linkOne ![1, 0] *ᵥ
        (fun i => (![fun s => 2 * s, fun s => 2 * s + 1] : Fin 2 → ℝ → ℝ) i t) +
      thermalB ![1, 2] ![1, 0] *ᵥ Sum.elim (fun _ => (fun s : ℝ => 2 * s + 1) t)
        (fun i => (![fun _ => 0, fun _ => 5] : Fin 2 → ℝ → ℝ) i t)) t := by
  refine (thermal_trajectory_iff (C := ![1, 2]) (G := linkOne) (g0 := ![1, 0])
    (by intro i; fin_cases i <;> norm_num) ![fun s => 2 * s, fun s => 2 * s + 1]
    (fun s => 2 * s + 1) ![fun _ => 0, fun _ => 5]).mpr ?_
  intro t i
  fin_cases i
  · refine ⟨2, ?_, ?_⟩
    · simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
    · simp [linkOne, Fin.sum_univ_two]
      ring
  · refine ⟨2, ?_, ?_⟩
    · simpa using ((hasDerivAt_id t).const_mul (2 : ℝ)).add_const 1
    · simp [linkOne, Fin.sum_univ_two]
      ring

/-- Agreement without self-links: the inner matrix of `thermalA` is `-stiffnessMatrix G g0`. -/
private lemma inner_eq_neg_stiffness {ι : Type*} [Fintype ι] [DecidableEq ι] (G : ι → ι → ℝ)
    (g0 : ι → ℝ) (hG0 : ∀ i, G i i = 0) :
    (of G - diagonal fun i => (∑ j, G i j) + g0 i) = -stiffnessMatrix G g0 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [stiffnessMatrix, hG0]
  · simp [stiffnessMatrix, h]

-- Hence `thermalA C G g0 = diagonal (1 / C) * -stiffnessMatrix G g0` without self-links.
example {ι : Type*} [Fintype ι] [DecidableEq ι] (C : ι → ℝ)
    (G : ι → ι → ℝ) (g0 : ι → ℝ) (hG0 : ∀ i, G i i = 0) :
    thermalA C G g0 = diagonal (fun i => 1 / C i) * -stiffnessMatrix G g0 := by
  rw [thermalA, inner_eq_neg_stiffness G g0 hG0]

-- Control: with a self-link the two encodings differ (`thermalA` cancels `G i i`, the
-- stiffness diagonal keeps it).
example :
    thermalA (fun _ : Unit => (1 : ℝ)) (fun _ _ => 1) (fun _ => 0) ≠
      diagonal (fun _ : Unit => (1 : ℝ) / 1)
        * -stiffnessMatrix (fun _ _ => (1 : ℝ)) (fun _ => 0) := by
  intro h
  have h1 := congrFun (congrFun h ()) ()
  simp [thermalA, stiffnessMatrix] at h1

#print axioms PhyslibExtTest.Engineering.ZoneThermalPlant.ownerForm_trajectory_iff
#print axioms PhyslibExtTest.Engineering.ZoneThermalPlant.plantTrajectoryStmt_of_ne
#print axioms PhyslibExtTest.Engineering.ZoneThermalPlant.relaxingCurve_trajectory
#print axioms PhyslibExtTest.Engineering.ZoneThermalPlant.inner_eq_neg_stiffness

end PhyslibExtTest.Engineering.ZoneThermalPlant
