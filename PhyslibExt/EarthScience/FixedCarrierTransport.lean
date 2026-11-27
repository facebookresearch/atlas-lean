/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.GroundwaterRetardation
public import MathlibExt.Combinatorics.Graph.ArcNetwork
import MathlibExt.Combinatorics.Graph.NonnegTransferStep
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Fixed-carrier concentration step with linear sorption

## i. Overview

Cells are nodes `V` and water-carrying links are arcs `E`
with `tail head : E → V`. `Q e` is the carrier-water flow
rate along arc `e` (from `tail e` to `head e`), `qin i` and
`qout i` are the external inflow and outflow rates at cell
`i`, `cin i` the external inflow concentration, `c i` the
aqueous concentration, `k i` a first-order loss rate on
stored mass and `dt` the step length. Carrier-water
volumes are fixed, which is `IsCarrierBalanced`: arc net
inflow plus external inflow equals external outflow at
every cell. `C i` is the storage capacity converting
concentration to stored mass `C i * c i`; the physical
capacity is `storedMassCoefficient (vol i) (phi i)
(rho_b i) (Kd i)`. `concentrationStep` is the explicit
mixing form: each inflow (arc or external) displaces an
equal water volume at the cell concentration. Under the
carrier balance, the step read as stored mass is the
shared inventory update; total stored mass changes only
by the external terms; and under the shared transfer-step
budget the updated stored mass and concentration stay
nonnegative. The external outflow `qout` and the loss rate
`k` carry no sign premise in the nonnegativity statement:
the budget then does not cap each fraction at `1`
separately, and the usual nonnegative-loss statement is
the specialization at `0 ≤ qout`, `0 ≤ k`. Variable
carrier volumes and implicit steps are not covered.

## ii. Key results

- `EarthScience.FixedCarrierTransport.IsCarrierBalanced`
  and `concentrationStep`: the fixed-carrier balance and
  the mixing-form step.
- `concentrationStep_inventory`: the step read as stored
  mass is the shared inventory update.
- `concentrationStep_total`: the total stored-mass
  balance.
- `concentrationStep_nonneg` and
  `storedMass_concentrationStep_nonneg`: budget
  nonnegativity, also at the physical sorption capacities.

## iii. Table of contents

- A. Balance and the concentration step
- B. Inventory commutation and total balance
- C. Budget nonnegativity

## iv. References

- `MathlibExt.Combinatorics.Graph.ArcNetwork` for the
  incidence matrix and stock-level balance.
- `MathlibExt.Combinatorics.Graph.NonnegTransferStep` for
  the shared transfer-step budget certificate.
- `PhyslibExt.EarthScience.GroundwaterRetardation` for
  stored mass under linear sorption.
-/

@[expose] public section

open Matrix
open MathlibExt.Combinatorics.Graph.ArcNetwork

namespace EarthScience.FixedCarrierTransport

/-! ## A. Balance and the concentration step -/

/-- Per-cell carrier-water balance including all external
flows (fixed carrier-water volumes): arc net inflow plus
external inflow equals external outflow. -/
def IsCarrierBalanced {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (tail head : E → V) (Q : E → ℝ) (qin qout : V → ℝ) : Prop :=
  ∀ i, (incidenceMatrix tail head *ᵥ Q) i + qin i = qout i

/-- Explicit fixed-carrier concentration step over `dt`
(mixing form): each inflow (arc `e` into `i` at rate
`Q e`, external at `qin i` with concentration `cin i`)
displaces an equal water volume at the cell concentration
`c i`; `C i` is the storage capacity and `k i` a
first-order loss rate on stored mass. -/
noncomputable def concentrationStep {V E : Type*} [DecidableEq V] [Fintype E]
    (tail head : E → V) (C : V → ℝ) (dt : ℝ)
    (Q : E → ℝ) (qin cin k c : V → ℝ) (i : V) : ℝ :=
  c i + dt * ((∑ e ∈ (Finset.univ : Finset E).filter (fun e => head e = i),
      Q e * (c (tail e) - c i)) + qin i * (cin i - c i)) / C i - dt * k i * c i

/-! ## B. Inventory commutation and total balance -/

/-- Conditional form of the inventory commutation, given
the canonical incidence characterization. -/
private theorem concentrationStep_inventory_of {V E : Type*} [Fintype V]
    [DecidableEq V] [Fintype E] [DecidableEq E]
    (hinc : ∀ (tail head : E → V) (f : E → ℝ) (v : V),
      (incidenceMatrix tail head).mulVec f v =
        (∑ e ∈ (Finset.univ : Finset E).filter (fun e => head e = v), f e) -
        (∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = v), f e))
    (tail head : E → V) {C : V → ℝ}
    (hC : ∀ i, C i ≠ 0) {dt : ℝ} {Q : E → ℝ} {qin cin qout k c : V → ℝ}
    (hbal : IsCarrierBalanced tail head Q qin qout) :
    (fun i => C i * concentrationStep tail head C dt Q qin cin k c i) =
      (fun i => C i * c i)
        + incidenceMatrix tail head *ᵥ (fun e => dt * Q e * c (tail e))
        + (fun i => dt * qin i * cin i)
        - (fun i => dt * (qout i / C i + k i) * (C i * c i)) := by
  funext i
  simp only [Pi.add_apply, Pi.sub_apply]
  have hCi : C i ≠ 0 := hC i
  have hQ' : (incidenceMatrix tail head *ᵥ Q) i =
      (∑ e ∈ (Finset.univ : Finset E).filter (fun e => head e = i), Q e) -
      (∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = i), Q e) :=
    hinc tail head Q i
  have hF' : (incidenceMatrix tail head *ᵥ
        (fun e => dt * Q e * c (tail e))) i =
      (∑ e ∈ (Finset.univ : Finset E).filter (fun e => head e = i),
        dt * Q e * c (tail e)) -
      (∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = i),
        dt * Q e * c (tail e)) :=
    hinc tail head _ i
  have hbal' := hbal i
  rw [hQ'] at hbal'
  rw [hF']
  have hfield : C i * concentrationStep tail head C dt Q qin cin k c i
      = C i * c i + dt * ((∑ e ∈ (Finset.univ : Finset E).filter
          (fun e => head e = i), Q e * (c (tail e) - c i))
          + qin i * (cin i - c i))
        - C i * dt * k i * c i := by
    unfold concentrationStep
    field_simp
  rw [hfield]
  have hret : dt * (qout i / C i + k i) * (C i * c i)
      = dt * qout i * c i + dt * k i * C i * c i := by
    field_simp
  rw [hret]
  have hS1 : (∑ e ∈ (Finset.univ : Finset E).filter (fun e => head e = i),
        Q e * (c (tail e) - c i))
      = (∑ e ∈ (Finset.univ : Finset E).filter (fun e => head e = i),
          Q e * c (tail e))
        - (∑ e ∈ (Finset.univ : Finset E).filter (fun e => head e = i), Q e)
          * c i := by
    trans ∑ e ∈ (Finset.univ : Finset E).filter (fun e => head e = i),
      (Q e * c (tail e) - Q e * c i)
    · apply Finset.sum_congr rfl
      intro e _
      ring
    · rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hS1]
  have hS2 : (∑ e ∈ (Finset.univ : Finset E).filter (fun e => head e = i),
        dt * Q e * c (tail e))
      = dt * (∑ e ∈ (Finset.univ : Finset E).filter (fun e => head e = i),
        Q e * c (tail e)) := by
    trans ∑ e ∈ (Finset.univ : Finset E).filter (fun e => head e = i),
      dt * (Q e * c (tail e))
    · apply Finset.sum_congr rfl
      intro e _
      ring
    · rw [← Finset.mul_sum]
  rw [hS2]
  have hS3 : (∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = i),
        dt * Q e * c (tail e))
      = dt * c i * (∑ e ∈ (Finset.univ : Finset E).filter
        (fun e => tail e = i), Q e) := by
    trans ∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = i),
      (dt * c i) * Q e
    · apply Finset.sum_congr rfl
      intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
      rw [he]
      ring
    · rw [← Finset.mul_sum]
  rw [hS3]
  linear_combination -dt * c i * hbal'

/-- Commutation: under the carrier-water balance, the
concentration step read as stored mass `C * c` is the
shared inventory update with `F e = dt * Q e * c (tail e)`,
source `dt * qin * cin` and retirement `δ * m`,
`δ = dt * (qout / C + k)`. -/
theorem concentrationStep_inventory {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (tail head : E → V) {C : V → ℝ}
    (hC : ∀ i, C i ≠ 0) {dt : ℝ} {Q : E → ℝ} {qin cin qout k c : V → ℝ}
    (hbal : IsCarrierBalanced tail head Q qin qout) :
    (fun i => C i * concentrationStep tail head C dt Q qin cin k c i) =
      (fun i => C i * c i)
        + incidenceMatrix tail head *ᵥ (fun e => dt * Q e * c (tail e))
        + (fun i => dt * qin i * cin i)
        - (fun i => dt * (qout i / C i + k i) * (C i * c i)) :=
  concentrationStep_inventory_of incidence_mulVec tail head hC hbal

/-- Conditional form of the total balance, given the
canonical incidence and stock-level balance statements. -/
private theorem concentrationStep_total_of {V E : Type*} [Fintype V]
    [DecidableEq V] [Fintype E] [DecidableEq E]
    (hinc : ∀ (tail head : E → V) (f : E → ℝ) (v : V),
      (incidenceMatrix tail head).mulVec f v =
        (∑ e ∈ (Finset.univ : Finset E).filter (fun e => head e = v), f e) -
        (∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = v), f e))
    (hbalance : ∀ (tail head : E → V) (F : E → ℝ) {m m' s r : V → ℝ},
      m' = m + (incidenceMatrix tail head).mulVec F + s - r →
      ∑ v, m' v = ∑ v, m v + ∑ v, s v - ∑ v, r v)
    (tail head : E → V) {C : V → ℝ}
    (hC : ∀ i, C i ≠ 0) {dt : ℝ} {Q : E → ℝ} {qin cin qout k c : V → ℝ}
    (hbal : IsCarrierBalanced tail head Q qin qout) :
    ∑ i, C i * concentrationStep tail head C dt Q qin cin k c i
      = ∑ i, C i * c i + ∑ i, dt * qin i * cin i
        - ∑ i, dt * (qout i / C i + k i) * (C i * c i) := by
  have hinv : (fun i => C i * concentrationStep tail head C dt Q qin cin k c i) =
      (fun i => C i * c i)
        + incidenceMatrix tail head *ᵥ (fun e => dt * Q e * c (tail e))
        + (fun i => dt * qin i * cin i)
        - (fun i => dt * (qout i / C i + k i) * (C i * c i)) :=
    concentrationStep_inventory_of hinc tail head hC hbal
  exact hbalance tail head _ hinv

/-- Total stored mass after the step (via
`stock_level_arc_balance`): initial total plus external
source minus the retirement total. -/
theorem concentrationStep_total {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (tail head : E → V) {C : V → ℝ}
    (hC : ∀ i, C i ≠ 0) {dt : ℝ} {Q : E → ℝ} {qin cin qout k c : V → ℝ}
    (hbal : IsCarrierBalanced tail head Q qin qout) :
    ∑ i, C i * concentrationStep tail head C dt Q qin cin k c i
      = ∑ i, C i * c i + ∑ i, dt * qin i * cin i
        - ∑ i, dt * (qout i / C i + k i) * (C i * c i) :=
  concentrationStep_total_of incidence_mulVec stock_level_arc_balance
    tail head hC hbal

/-! ## C. Budget nonnegativity -/

/-- Conditional form of budget nonnegativity, given the
canonical incidence and transfer-step statements. -/
private theorem concentrationStep_nonneg_of {V E : Type*} [Fintype V]
    [DecidableEq V] [Fintype E] [DecidableEq E]
    (hinc : ∀ (tail head : E → V) (f : E → ℝ) (v : V),
      (incidenceMatrix tail head).mulVec f v =
        (∑ e ∈ (Finset.univ : Finset E).filter (fun e => head e = v), f e) -
        (∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = v), f e))
    (htransfer : ∀ (tail head : E → V) {α F : E → ℝ} {δ m m' s r : V → ℝ},
      (∀ v, 0 ≤ m v) → (∀ v, 0 ≤ s v) →
      (∀ e, 0 ≤ α e) →
      (∀ e, F e = α e * m (tail e)) →
      (∀ v, r v = δ v * m v) →
      (∀ v,
        (∑ e ∈ (Finset.univ : Finset E).filter
            (fun e => tail e = v), α e) + δ v ≤ 1) →
      m' = m + (incidenceMatrix tail head) *ᵥ F + s - r →
      ∀ v, 0 ≤ m' v)
    (tail head : E → V) {C : V → ℝ} (hC : ∀ i, 0 < C i)
    {dt : ℝ} (hdt : 0 ≤ dt) {Q : E → ℝ} (hQ : ∀ e, 0 ≤ Q e)
    {qin cin qout k c : V → ℝ} (hqin : ∀ i, 0 ≤ qin i) (hcin : ∀ i, 0 ≤ cin i)
    (hc : ∀ i, 0 ≤ c i) (hbal : IsCarrierBalanced tail head Q qin qout)
    (hbudget : ∀ i, (∑ e ∈ (Finset.univ : Finset E).filter
        (fun e => tail e = i), dt * Q e / C (tail e))
        + dt * (qout i / C i + k i) ≤ 1) :
    ∀ i, 0 ≤ C i * concentrationStep tail head C dt Q qin cin k c i ∧
      0 ≤ concentrationStep tail head C dt Q qin cin k c i := by
  have hCne : ∀ i, C i ≠ 0 := fun i => ne_of_gt (hC i)
  have hinv : (fun i => C i * concentrationStep tail head C dt Q qin cin k c i) =
      (fun i => C i * c i)
        + incidenceMatrix tail head *ᵥ (fun e => dt * Q e * c (tail e))
        + (fun i => dt * qin i * cin i)
        - (fun i => dt * (qout i / C i + k i) * (C i * c i)) :=
    concentrationStep_inventory_of hinc tail head hCne hbal
  have h1 : ∀ v, 0 ≤ (fun i => C i * c i) v :=
    fun v => mul_nonneg (le_of_lt (hC v)) (hc v)
  have h2 : ∀ v, 0 ≤ (fun i => dt * qin i * cin i) v :=
    fun v => mul_nonneg (mul_nonneg hdt (hqin v)) (hcin v)
  have h3 : ∀ e, 0 ≤ (fun e => dt * Q e / C (tail e)) e :=
    fun e => div_nonneg (mul_nonneg hdt (hQ e)) (le_of_lt (hC (tail e)))
  have h4 : ∀ e, (fun e => dt * Q e * c (tail e)) e
      = (fun e => dt * Q e / C (tail e)) e * (fun i => C i * c i) (tail e) := by
    intro e
    change dt * Q e * c (tail e)
      = dt * Q e / C (tail e) * (C (tail e) * c (tail e))
    have hCne' : C (tail e) ≠ 0 := hCne (tail e)
    field_simp
  have h5 : ∀ v, (fun i => dt * (qout i / C i + k i) * (C i * c i)) v
      = (fun i => dt * (qout i / C i + k i)) v * (fun i => C i * c i) v := by
    intro v
    rfl
  have h6 : ∀ v, (∑ e ∈ (Finset.univ : Finset E).filter
        (fun e => tail e = v), (fun e => dt * Q e / C (tail e)) e)
        + (fun i => dt * (qout i / C i + k i)) v ≤ 1 := by
    intro v
    change (∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = v),
      dt * Q e / C (tail e)) + dt * (qout v / C v + k v) ≤ 1
    exact hbudget v
  have hm' := htransfer tail head h1 h2 h3 h4 h5 h6 hinv
  intro i
  constructor
  · exact hm' i
  · exact nonneg_of_mul_nonneg_right (hm' i) (hC i)

/-- Nonnegativity under `α e = dt * Q e / C (tail e)` and
the shared transfer-step outgoing/loss budget, for mass
and concentration. No sign premise on `qout` or `k` is
needed (or taken): the budget is on the combined
fractions, and the usual nonnegative-loss case is the
specialization. -/
theorem concentrationStep_nonneg {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (tail head : E → V) {C : V → ℝ} (hC : ∀ i, 0 < C i)
    {dt : ℝ} (hdt : 0 ≤ dt) {Q : E → ℝ} (hQ : ∀ e, 0 ≤ Q e)
    {qin cin qout k c : V → ℝ} (hqin : ∀ i, 0 ≤ qin i) (hcin : ∀ i, 0 ≤ cin i)
    (hc : ∀ i, 0 ≤ c i) (hbal : IsCarrierBalanced tail head Q qin qout)
    (hbudget : ∀ i, (∑ e ∈ (Finset.univ : Finset E).filter
        (fun e => tail e = i), dt * Q e / C (tail e))
        + dt * (qout i / C i + k i) ≤ 1) :
    ∀ i, 0 ≤ C i * concentrationStep tail head C dt Q qin cin k c i ∧
      0 ≤ concentrationStep tail head C dt Q qin cin k c i :=
  concentrationStep_nonneg_of incidence_mulVec nonneg_transfer_step
    tail head hC hdt hQ hqin hcin hc hbal hbudget

/-- Conditional form of the physical-capacity statement,
given the canonical incidence, transfer-step, and
stored-mass statements. -/
private theorem storedMass_concentrationStep_nonneg_of {V E : Type*}
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hinc : ∀ (tail head : E → V) (f : E → ℝ) (v : V),
      (incidenceMatrix tail head).mulVec f v =
        (∑ e ∈ (Finset.univ : Finset E).filter (fun e => head e = v), f e) -
        (∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = v), f e))
    (htransfer : ∀ (tail head : E → V) {α F : E → ℝ} {δ m m' s r : V → ℝ},
      (∀ v, 0 ≤ m v) → (∀ v, 0 ≤ s v) →
      (∀ e, 0 ≤ α e) →
      (∀ e, F e = α e * m (tail e)) →
      (∀ v, r v = δ v * m v) →
      (∀ v,
        (∑ e ∈ (Finset.univ : Finset E).filter
            (fun e => tail e = v), α e) + δ v ≤ 1) →
      m' = m + (incidenceMatrix tail head) *ᵥ F + s - r →
      ∀ v, 0 ≤ m' v)
    (hmass : ∀ (vol phi rho_b Kd c : ℝ),
      storedMass vol phi rho_b Kd c
        = storedMassCoefficient vol phi rho_b Kd * c)
    (hcoeff_pos : ∀ {vol phi rho_b Kd : ℝ},
      0 < vol → 0 < phi → 0 ≤ rho_b → 0 ≤ Kd →
      0 < storedMassCoefficient vol phi rho_b Kd)
    (tail head : E → V)
    {vol phi rho_b Kd : V → ℝ} (hvol : ∀ i, 0 < vol i) (hphi : ∀ i, 0 < phi i)
    (hrho : ∀ i, 0 ≤ rho_b i) (hKd : ∀ i, 0 ≤ Kd i)
    {dt : ℝ} (hdt : 0 ≤ dt) {Q : E → ℝ} (hQ : ∀ e, 0 ≤ Q e)
    {qin cin qout k c : V → ℝ} (hqin : ∀ i, 0 ≤ qin i) (hcin : ∀ i, 0 ≤ cin i)
    (hc : ∀ i, 0 ≤ c i) (hbal : IsCarrierBalanced tail head Q qin qout)
    (hbudget : ∀ i, (∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = i),
        dt * Q e / storedMassCoefficient (vol (tail e)) (phi (tail e))
          (rho_b (tail e)) (Kd (tail e)))
        + dt * (qout i / storedMassCoefficient (vol i) (phi i) (rho_b i) (Kd i)
          + k i) ≤ 1) :
    ∀ i, 0 ≤ storedMass (vol i) (phi i) (rho_b i) (Kd i)
        (concentrationStep tail head
          (fun j => storedMassCoefficient (vol j) (phi j) (rho_b j) (Kd j))
          dt Q qin cin k c i) ∧
      0 ≤ concentrationStep tail head
          (fun j => storedMassCoefficient (vol j) (phi j) (rho_b j) (Kd j))
          dt Q qin cin k c i := by
  have hC : ∀ i, 0 < (fun j => storedMassCoefficient (vol j) (phi j) (rho_b j)
      (Kd j)) i :=
    fun i => hcoeff_pos (hvol i) (hphi i) (hrho i) (hKd i)
  have h := concentrationStep_nonneg_of hinc htransfer tail head hC hdt hQ
    hqin hcin hc hbal hbudget
  intro i
  obtain ⟨hm, hc'⟩ := h i
  constructor
  · rw [hmass]
    exact hm
  · exact hc'

/-- Physical headline: capacities are the
`storedMassCoefficient` and the mass is `storedMass`. -/
theorem storedMass_concentrationStep_nonneg {V E : Type*} [Fintype V]
    [DecidableEq V] [Fintype E] [DecidableEq E]
    (tail head : E → V)
    {vol phi rho_b Kd : V → ℝ} (hvol : ∀ i, 0 < vol i) (hphi : ∀ i, 0 < phi i)
    (hrho : ∀ i, 0 ≤ rho_b i) (hKd : ∀ i, 0 ≤ Kd i)
    {dt : ℝ} (hdt : 0 ≤ dt) {Q : E → ℝ} (hQ : ∀ e, 0 ≤ Q e)
    {qin cin qout k c : V → ℝ} (hqin : ∀ i, 0 ≤ qin i) (hcin : ∀ i, 0 ≤ cin i)
    (hc : ∀ i, 0 ≤ c i) (hbal : IsCarrierBalanced tail head Q qin qout)
    (hbudget : ∀ i, (∑ e ∈ (Finset.univ : Finset E).filter (fun e => tail e = i),
        dt * Q e / storedMassCoefficient (vol (tail e)) (phi (tail e))
          (rho_b (tail e)) (Kd (tail e)))
        + dt * (qout i / storedMassCoefficient (vol i) (phi i) (rho_b i) (Kd i)
          + k i) ≤ 1) :
    ∀ i, 0 ≤ storedMass (vol i) (phi i) (rho_b i) (Kd i)
        (concentrationStep tail head
          (fun j => storedMassCoefficient (vol j) (phi j) (rho_b j) (Kd j))
          dt Q qin cin k c i) ∧
      0 ≤ concentrationStep tail head
          (fun j => storedMassCoefficient (vol j) (phi j) (rho_b j) (Kd j))
          dt Q qin cin k c i :=
  storedMass_concentrationStep_nonneg_of incidence_mulVec
    nonneg_transfer_step storedMass_eq_coefficient_mul
    storedMassCoefficient_pos tail head hvol hphi hrho hKd hdt hQ hqin hcin hc
    hbal hbudget

end EarthScience.FixedCarrierTransport
