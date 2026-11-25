/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import PhyslibExt.Circuits.NetworkStorageBalance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Ideal buck converter stored-energy balance

## i. Overview

An ideal two-state synchronous buck converter, before any
averaging: positive inductance `L`, capacitance `C` and load
resistance `R`, constant input voltage `Vin`, a switching
function `s` that is constant with a binary value (`0` or `1`) on
each open interval between finitely many switching instants, and
inductor-current and capacitor-voltage states `i` and `v` that are
continuous on the whole closed horizon, differentiable between
switches, and satisfy the inductor voltage law
`L * i' = s * Vin - v` and the capacitor current law
`C * v' = i - v / R` at every non-switching time. The switch node
is always driven to `Vin` or to `0`, so the inductor current may
take either sign: this is the bidirectional switched-voltage model
of a synchronous buck, and no sign condition on `i` is assumed,
because no proof step uses one. The diode buck in continuous
conduction is the special case in which `i` stays positive on the
horizon; the results apply to it unchanged. The stored energy is
the canonical network stored energy
`NetworkStorageBalance.storedEnergy` on the four-branch embedding
in source, inductor, capacitor, resistor order, specialized to the
single capacitor branch `2` and the single inductor branch `1`;
by `buckStoredEnergy_eq` it is `L * i^2 / 2 + C * v^2 / 2`. Its
derivative between switches is the switched input power delivered
minus the resistive loss, `s * Vin * i - v^2 / R`. Continuity of
the state at the switching instants carries the balance across
switches with no jump term, so the integrated balance sums the
interval contributions. Over a closed horizon `[0, T]` whose
endpoint states agree the net stored-energy change is zero; one
period `T > 0` of a periodic steady state is the intended
instance, but periodicity enters only through the endpoint
equality, and the degenerate horizon `T = 0` is admitted. The
source branch carries the switched input voltage at current `-i`
(passive sign), so the source delivers `s * Vin * i` exactly when
its absorbed power is subtracted. No averaged duty-cycle model,
discontinuous conduction mode (an idle interval with the inductor
current held at zero would need the non-binary switch value
`v / Vin`), dead time or switching loss is claimed.

The pointwise balance is proved directly from the two state laws:
the derivative of each quadratic energy term is computed from the
differentiability hypotheses, and the two laws are combined by
linear combination. The integrated balance applies the fundamental
theorem of calculus on each closed subinterval between consecutive
breakpoints, sums the adjacent interval integrals, and telescopes
the resulting sum of energy differences. The endpoint-return
statement is the integrated balance evaluated at endpoints with
equal state.

## ii. Key results

- `buckStoredEnergy_eq`: the stored energy is
  `L * i^2 / 2 + C * v^2 / 2`.
- `buckStoredEnergy_nonneg`: stored energy is nonnegative for
  nonnegative inductance and capacitance.
- `outputNode_current_balance_of_capacitorLaw` and
  `buckEmbedding_current_balance`: output-node and four-branch
  current balance from the capacitor law.
- `buckStoredEnergy_hasDerivAt_eq_supplied_sub_loss`: the pointwise
  balance `E' = s * Vin * i - v^2 / R` between switches.
- `buckStoredEnergy_sub_eq_integral_supplied_sub_loss`: the
  integrated balance over finitely many switching intervals.
- `buckStoredEnergy_periodic_net_change_eq_zero`: zero net
  stored-energy change over a horizon `[0, T]` whose endpoint
  states agree, such as one period of a periodic state.

## iii. Table of contents

- A. Stored energy and the four-branch embedding
- B. Pointwise and integrated storage balance

## iv. References

- R. W. Erickson and D. Maksimovic, *Fundamentals of Power
  Electronics*, second edition, Springer, 2001: the buck converter,
  inductor and capacitor stored energy, and switched power balance.

## A. Stored energy and the four-branch embedding

The stored energy is the canonical `storedEnergy` with capacitor
class `{2}` and inductor class `{1}` on four branches. Only the
capacitor voltage entry at branch `2` and the inductor current
entry at branch `1` enter the two singleton sums; the remaining
entries of the value and state vectors are zero and are never read.

## B. Pointwise and integrated storage balance

Between switches the energy derivative is the delivered source
power minus the resistive loss. Across finitely many switches the
same integrand integrates to the total energy change, because the
state, and hence the energy, is continuous at every breakpoint.
-/

@[expose] public section

namespace PhyslibExt.Circuits.IdealBuckEnergy

/-! ### A. Stored energy and the four-branch embedding -/

/-- Stored energy of the two-state converter, as the canonical
network stored energy on the four-branch embedding in source,
inductor, capacitor, resistor order: the single capacitor branch
is `2` with capacitance `C` at voltage `v t`, and the single
inductor branch is `1` with inductance `L` at current `i t`. The
unread vector entries are zero. -/
noncomputable def buckStoredEnergy (L C : ℝ) (i v : ℝ → ℝ) (t : ℝ) : ℝ :=
  PhyslibExt.Circuits.NetworkStorageBalance.storedEnergy 4 {2} {1}
    ![0, 0, C, 0] ![0, L, 0, 0] ![0, 0, v t, 0] ![0, i t, 0, 0]

/-- The stored energy is the inductor part plus the capacitor part:
`L * (i t)^2 / 2 + C * (v t)^2 / 2`. The two singleton sums of the
canonical stored energy evaluate to the two quadratic terms. -/
lemma buckStoredEnergy_eq (L C : ℝ) (i v : ℝ → ℝ) (t : ℝ) :
    buckStoredEnergy L C i v t = L * (i t) ^ 2 / 2 + C * (v t) ^ 2 / 2 := by
  have hval : buckStoredEnergy L C i v t
      = C * (v t) ^ 2 / 2 + L * (i t) ^ 2 / 2 := by
    norm_num [buckStoredEnergy,
      PhyslibExt.Circuits.NetworkStorageBalance.storedEnergy,
      Finset.sum_singleton]
  rw [hval]
  ring

/-- Voltages of the four network branches in the order source,
inductor, capacitor, resistor: switched input voltage,
input-minus-output drop, output voltage, output voltage. -/
def buckBranchVoltage (s Vin v : ℝ) : Fin 4 → ℝ :=
  ![s * Vin, s * Vin - v, v, v]

/-- Currents of the four network branches in the same order: source
current opposite to the inductor current, inductor current,
capacitor current, resistor current. The passive source sign is
the negative entry. -/
noncomputable def buckBranchCurrent (R C : ℝ) (cur capDeriv volt : ℝ) :
    Fin 4 → ℝ :=
  ![-cur, cur, C * capDeriv, volt / R]

/-- Stored energy is nonnegative for nonnegative inductance and
capacitance, at every state: each quadratic term is nonnegative. -/
lemma buckStoredEnergy_nonneg (L C : ℝ) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (i v : ℝ → ℝ) (t : ℝ) :
    0 ≤ buckStoredEnergy L C i v t := by
  rw [buckStoredEnergy_eq]
  have h1 : 0 ≤ L * (i t) ^ 2 / 2 := by positivity
  have h2 : 0 ≤ C * (v t) ^ 2 / 2 := by positivity
  linarith

/-- Output-node current balance follows from the capacitor law
alone: the capacitor current plus the resistor current equals the
inductor current entering the output node. -/
lemma outputNode_current_balance_of_capacitorLaw (C R : ℝ)
    (i v : ℝ → ℝ) (t : ℝ) (hClaw : C * deriv v t = i t - v t / R) :
    C * deriv v t + v t / R = i t := by
  linarith

/-- The four-branch embedding satisfies node current balance: at
the output node the capacitor and resistor branch currents sum to
the inductor branch current, and at the input node the source and
inductor branch currents cancel, under the capacitor law at that
time. -/
lemma buckEmbedding_current_balance (R C : ℝ) (i v : ℝ → ℝ) (t : ℝ)
    (hClaw : C * deriv v t = i t - v t / R) :
    buckBranchCurrent R C (i t) (deriv v t) (v t) 2 +
        buckBranchCurrent R C (i t) (deriv v t) (v t) 3 =
        buckBranchCurrent R C (i t) (deriv v t) (v t) 1 ∧
      buckBranchCurrent R C (i t) (deriv v t) (v t) 0 +
        buckBranchCurrent R C (i t) (deriv v t) (v t) 1 = 0 := by
  have h0 : buckBranchCurrent R C (i t) (deriv v t) (v t) 0 = -(i t) := rfl
  have h1 : buckBranchCurrent R C (i t) (deriv v t) (v t) 1 = i t := rfl
  have h2 : buckBranchCurrent R C (i t) (deriv v t) (v t) 2
      = C * deriv v t := rfl
  have h3 : buckBranchCurrent R C (i t) (deriv v t) (v t) 3 = v t / R := rfl
  rw [h2, h3, h1, h0]
  constructor
  · exact outputNode_current_balance_of_capacitorLaw C R i v t hClaw
  · ring

/-! ### B. Pointwise and integrated storage balance -/

private theorem tau_le_of_lt_succ (τ : ℕ → ℝ) (n : ℕ)
    (hτinc : ∀ k : ℕ, k < n → τ k < τ (k + 1)) :
    ∀ j k : ℕ, j ≤ k → k ≤ n → τ j ≤ τ k := by
  intro j k
  induction k generalizing j with
  | zero =>
    intro hjk hkn
    have hj0 : j = 0 := by omega
    rw [hj0]
  | succ k ih =>
    intro hjk hkn
    rcases eq_or_lt_of_le hjk with rfl | hlt
    · exact le_rfl
    · have hjk' : j ≤ k := by omega
      have hkn' : k ≤ n := by omega
      exact le_trans (ih j hjk' hkn') (le_of_lt (hτinc k (by omega)))

private theorem continuousOn_buckStoredEnergy (L C : ℝ) (i v : ℝ → ℝ)
    (a b : ℝ) (hicont : ContinuousOn i (Set.Icc a b))
    (hvcont : ContinuousOn v (Set.Icc a b)) :
    ContinuousOn (fun t : ℝ => buckStoredEnergy L C i v t) (Set.Icc a b) := by
  have hi2 : ContinuousOn (fun t : ℝ => (i t) ^ 2) (Set.Icc a b) := hicont.pow 2
  have hv2 : ContinuousOn (fun t : ℝ => (v t) ^ 2) (Set.Icc a b) := hvcont.pow 2
  have hiE : ContinuousOn (fun t : ℝ => L * (i t) ^ 2 / 2) (Set.Icc a b) :=
    (continuousOn_const.mul hi2).div_const 2
  have hvE : ContinuousOn (fun t : ℝ => C * (v t) ^ 2 / 2) (Set.Icc a b) :=
    (continuousOn_const.mul hv2).div_const 2
  have hadd := ContinuousOn.add hiE hvE
  have hfun : (fun t : ℝ => L * (i t) ^ 2 / 2) +
      (fun t : ℝ => C * (v t) ^ 2 / 2)
      = fun t : ℝ => buckStoredEnergy L C i v t := by
    funext t
    simp only [Pi.add_apply, buckStoredEnergy_eq]
  rw [hfun] at hadd
  exact hadd

/-- Pointwise storage balance between switches: under the inductor
and capacitor laws at a non-switching time where both states are
differentiable, the stored energy has derivative equal to switched
input power minus resistive loss. The derivative of each quadratic
term is computed from the differentiability hypotheses, and the
displayed derivative value follows by linear combination of the
two state laws. -/
theorem buckStoredEnergy_hasDerivAt_eq_supplied_sub_loss (L C R Vin : ℝ)
    (hL : 0 < L) (hC : 0 < C) (hR : 0 < R) (s i v : ℝ → ℝ) (t : ℝ)
    (hLlaw : L * deriv i t = s t * Vin - v t)
    (hClaw : C * deriv v t = i t - v t / R)
    (hi : DifferentiableAt ℝ i t) (hv : DifferentiableAt ℝ v t) :
    HasDerivAt (fun τ : ℝ => buckStoredEnergy L C i v τ)
      (s t * Vin * i t - (v t) ^ 2 / R) t := by
  have hi' : HasDerivAt i (deriv i t) t := hi.hasDerivAt
  have hv' : HasDerivAt v (deriv v t) t := hv.hasDerivAt
  have hiE : HasDerivAt (fun x : ℝ => L * (i * i) x / 2)
      (L * (deriv i t * i t + i t * deriv i t) / 2) t :=
    HasDerivAt.div_const (HasDerivAt.const_mul L (HasDerivAt.mul hi' hi')) 2
  have hvE : HasDerivAt (fun x : ℝ => C * (v * v) x / 2)
      (C * (deriv v t * v t + v t * deriv v t) / 2) t :=
    HasDerivAt.div_const (HasDerivAt.const_mul C (HasDerivAt.mul hv' hv')) 2
  have hsum := HasDerivAt.add hiE hvE
  have hfun : (fun x : ℝ => L * (i * i) x / 2) +
      (fun x : ℝ => C * (v * v) x / 2)
      = fun τ : ℝ => buckStoredEnergy L C i v τ := by
    funext τ
    simp only [Pi.add_apply, Pi.mul_apply, buckStoredEnergy_eq, pow_two]
  rw [hfun] at hsum
  have hD : L * (deriv i t * i t + i t * deriv i t) / 2 +
      C * (deriv v t * v t + v t * deriv v t) / 2 =
      s t * Vin * i t - (v t) ^ 2 / R := by
    linear_combination (i t) * hLlaw + (v t) * hClaw
  rw [hD] at hsum
  exact hsum

/-- Headline integrated balance: across finitely many switching
intervals witnessed by consecutive breakpoints, with the state
continuous on the whole horizon, the switching function constant
with a binary value (`0` or `1`) on each open interval, and both
state laws with differentiability on each open interval, the
stored energy change equals the
integral of switched input power minus resistive loss. Continuity
at the breakpoints is the no-impulsive-reset hypothesis; no
derivative at a breakpoint is assumed. On each closed subinterval
the fundamental theorem of calculus gives the energy difference,
and the subinterval contributions sum to the whole integral and
telescope to the total energy change. -/
theorem buckStoredEnergy_sub_eq_integral_supplied_sub_loss (L C R Vin : ℝ)
    (hL : 0 < L) (hC : 0 < C) (hR : 0 < R) (s i v : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (n : ℕ) (τ : ℕ → ℝ) (hτ0 : τ 0 = a) (hτn : τ n = b)
    (hτinc : ∀ k : ℕ, k < n → τ k < τ (k + 1))
    (hicont : ContinuousOn i (Set.Icc a b))
    (hvcont : ContinuousOn v (Set.Icc a b))
    (hsconst : ∀ k : ℕ, k < n → ∃ c : ℝ, (c = 0 ∨ c = 1) ∧
      ∀ t : ℝ, t ∈ Set.Ioo (τ k) (τ (k + 1)) → s t = c)
    (hlaw : ∀ k : ℕ, k < n → ∀ t : ℝ, t ∈ Set.Ioo (τ k) (τ (k + 1)) →
      L * deriv i t = s t * Vin - v t ∧ C * deriv v t = i t - v t / R)
    (hdiff : ∀ k : ℕ, k < n → ∀ t : ℝ, t ∈ Set.Ioo (τ k) (τ (k + 1)) →
      DifferentiableAt ℝ i t ∧ DifferentiableAt ℝ v t)
    (hintegrable : IntervalIntegrable
      (fun t : ℝ => s t * Vin * i t - (v t) ^ 2 / R)
      MeasureTheory.volume a b) :
    buckStoredEnergy L C i v b - buckStoredEnergy L C i v a =
      ∫ t in a..b, s t * Vin * i t - (v t) ^ 2 / R := by
  have hmono := tau_le_of_lt_succ τ n hτinc
  have hlow : ∀ k : ℕ, k ≤ n → a ≤ τ k := by
    intro k hk
    rw [← hτ0]
    exact hmono 0 k (Nat.zero_le k) hk
  have hhigh : ∀ k : ℕ, k ≤ n → τ k ≤ b := by
    intro k hk
    rw [← hτn]
    exact hmono k n hk le_rfl
  have hEcont : ContinuousOn (fun t : ℝ => buckStoredEnergy L C i v t)
      (Set.Icc a b) :=
    continuousOn_buckStoredEnergy L C i v a b hicont hvcont
  have hsubint : ∀ k : ℕ, k < n →
      IntervalIntegrable (fun t : ℝ => s t * Vin * i t - (v t) ^ 2 / R)
        MeasureTheory.volume (τ k) (τ (k + 1)) := by
    intro k hk
    apply hintegrable.mono_set
    have hkk : τ k ≤ τ (k + 1) := le_of_lt (hτinc k hk)
    rw [Set.uIcc_of_le hkk, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc (hlow k (by omega)) (hhigh (k + 1) (by omega))
  have hstep : ∀ k : ℕ, k < n →
      (∫ t in τ k..τ (k + 1), s t * Vin * i t - (v t) ^ 2 / R)
        = buckStoredEnergy L C i v (τ (k + 1)) - buckStoredEnergy L C i v (τ k) := by
    intro k hk
    have hkk : τ k ≤ τ (k + 1) := le_of_lt (hτinc k hk)
    have hsub : Set.Icc (τ k) (τ (k + 1)) ⊆ Set.Icc a b :=
      Set.Icc_subset_Icc (hlow k (by omega)) (hhigh (k + 1) (by omega))
    have hcont : ContinuousOn (fun t : ℝ => buckStoredEnergy L C i v t)
        (Set.Icc (τ k) (τ (k + 1))) := hEcont.mono hsub
    have hderiv : ∀ x : ℝ, x ∈ Set.Ioo (τ k) (τ (k + 1)) →
        HasDerivAt (fun u : ℝ => buckStoredEnergy L C i v u)
          ((fun t : ℝ => s t * Vin * i t - (v t) ^ 2 / R) x) x := by
      intro x hx
      have hl := hlaw k hk x hx
      have hd := hdiff k hk x hx
      exact buckStoredEnergy_hasDerivAt_eq_supplied_sub_loss L C R Vin hL hC hR
        s i v x hl.1 hl.2 hd.1 hd.2
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hkk hcont hderiv
      (hsubint k hk)
  have hsum : (∑ k ∈ Finset.range n,
      ∫ t in τ k..τ (k + 1), s t * Vin * i t - (v t) ^ 2 / R)
      = ∫ t in a..b, s t * Vin * i t - (v t) ^ 2 / R := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (f := fun t : ℝ => s t * Vin * i t - (v t) ^ 2 / R)
      (μ := MeasureTheory.volume) (a := τ) (n := n) (fun k hk => hsubint k hk)
    rw [hτ0, hτn] at h
    exact h
  have htel : (∑ k ∈ Finset.range n,
        (buckStoredEnergy L C i v (τ (k + 1)) - buckStoredEnergy L C i v (τ k)))
      = buckStoredEnergy L C i v b - buckStoredEnergy L C i v a := by
    have h := Finset.sum_range_sub (fun k : ℕ => buckStoredEnergy L C i v (τ k)) n
    simp only [hτn, hτ0] at h
    exact h
  have hcongr : (∑ k ∈ Finset.range n,
      ∫ t in τ k..τ (k + 1), s t * Vin * i t - (v t) ^ 2 / R)
      = ∑ k ∈ Finset.range n,
        (buckStoredEnergy L C i v (τ (k + 1)) - buckStoredEnergy L C i v (τ k)) :=
    Finset.sum_congr rfl (fun k hk => hstep k (Finset.mem_range.mp hk))
  rw [← htel, ← hcongr]
  exact hsum

/-- Endpoint-return corollary: under the same finite-switch
hypotheses on a closed horizon `[0, T]`, a state that returns to
its initial current and voltage at `T` has zero net stored-energy
change over the horizon, and the integrated switched input power
minus resistive loss over the horizon is therefore zero as well.
This is the integrated balance with equal endpoint states. One
period `T > 0` of a periodic steady state is the intended
instance; periodicity of `s`, `i` or `v` is not assumed beyond
the endpoint equality, and the degenerate horizon `T = 0`, with no
switching interval, is admitted. -/
theorem buckStoredEnergy_periodic_net_change_eq_zero (L C R Vin : ℝ)
    (hL : 0 < L) (hC : 0 < C) (hR : 0 < R) (s i v : ℝ → ℝ) (T : ℝ)
    (hT : 0 ≤ T) (n : ℕ) (τ : ℕ → ℝ) (hτ0 : τ 0 = 0) (hτn : τ n = T)
    (hτinc : ∀ k : ℕ, k < n → τ k < τ (k + 1))
    (hicont : ContinuousOn i (Set.Icc 0 T))
    (hvcont : ContinuousOn v (Set.Icc 0 T))
    (hsconst : ∀ k : ℕ, k < n → ∃ c : ℝ, (c = 0 ∨ c = 1) ∧
      ∀ t : ℝ, t ∈ Set.Ioo (τ k) (τ (k + 1)) → s t = c)
    (hlaw : ∀ k : ℕ, k < n → ∀ t : ℝ, t ∈ Set.Ioo (τ k) (τ (k + 1)) →
      L * deriv i t = s t * Vin - v t ∧ C * deriv v t = i t - v t / R)
    (hdiff : ∀ k : ℕ, k < n → ∀ t : ℝ, t ∈ Set.Ioo (τ k) (τ (k + 1)) →
      DifferentiableAt ℝ i t ∧ DifferentiableAt ℝ v t)
    (hintegrable : IntervalIntegrable
      (fun t : ℝ => s t * Vin * i t - (v t) ^ 2 / R)
      MeasureTheory.volume 0 T)
    (hiT : i T = i 0) (hvT : v T = v 0) :
    buckStoredEnergy L C i v T - buckStoredEnergy L C i v 0 = 0 ∧
      (∫ t in (0:ℝ)..T, s t * Vin * i t - (v t) ^ 2 / R) = 0 := by
  have hbal := buckStoredEnergy_sub_eq_integral_supplied_sub_loss L C R Vin hL
    hC hR s i v 0 T hT n τ hτ0 hτn hτinc hicont hvcont hsconst hlaw hdiff
    hintegrable
  have hE0 : buckStoredEnergy L C i v T - buckStoredEnergy L C i v 0 = 0 := by
    have heq : buckStoredEnergy L C i v T = buckStoredEnergy L C i v 0 := by
      simp only [buckStoredEnergy_eq, hiT, hvT]
    rw [heq, sub_self]
  constructor
  · exact hE0
  · rw [← hbal]
    exact hE0

end PhyslibExt.Circuits.IdealBuckEnergy
