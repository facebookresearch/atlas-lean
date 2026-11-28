/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Instances.CantorSet
public import MathlibExt.Topology.SelectionPrinciplesShared
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Pairing
import Mathlib.Topology.UniformSpace.Dini

/-!
# Monotonic versus weak sequence selection in `C_p(X)`

On a compact space, Dini's theorem turns nonincreasing pointwise convergence to zero of each row
of continuous real-valued functions into uniform convergence. The Cantor set has this monotonic
selection property but fails weak sequence selection: any choice of one first-true-bit test from
each row can be encoded in a single point that separates every selected test from zero.

## References

* Marion Scheepers, *A sequential property of Cₚ(X) and a covering property of Hurewicz*,
  Proceedings of the American Mathematical Society 125 (1997), 2789–2795, Problem 2.
* Boaz Tsaban, *Selection principles in mathematics: A milestone of open problems*,
  Note di Matematica 22 (2003/2004), no. 2, 179–208, Problem 48 (Section 15).
* Masami Sakai, *The sequence selection properties of Cₚ(X)*, Topology and its Applications 154
  (2007), no. 3, 552–560. Sakai resolved Scheepers's problem negatively; the proof below instead
  gives a direct counterexample on the Cantor set.
-/

open Filter Set Topology MathlibExt.Topology.SelectionPrinciplesShared

namespace MathlibExt.Topology.MonotonicNotWeakSSPAMR134Problem0041Wanted

@[expose] public section

/-- The monotonic sequence selection property of `C_p(X)` (Scheepers): for every sequence
`(f^n_k)_{k ∈ ℕ}`, `n ∈ ℕ`, of sequences in `C_p(X)` each converging pointwise and monotonically
(non-increasingly) to `𝟎`, there are indices `k_n` with `f^n_{k_n} → 𝟎`. -/
def HasMonotonicSSP (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ f : ℕ → ℕ → Cp X, (∀ n, Tendsto (f n) atTop (nhds (cpZero X))) →
    (∀ n k x, (f n (k + 1)).1 x ≤ (f n k).1 x) →
      ∃ k : ℕ → ℕ, Tendsto (fun n => f n (k n)) atTop (nhds (cpZero X))

/-- Tsaban, Milestone Problem 48 (Scheepers): for every set of reals `X`, the monotonic sequence
selection property of `C_p(X)` implies the weak sequence selection property of `C_p(X)`. -/
def monotonicSSPImpliesWeakSSP : Prop :=
  ∀ X : Set ℝ, HasMonotonicSSP X → HasWeakSSP X

end

/-- The space of continuous real-valued functions on a compact space, with the pointwise topology,
has the monotonic sequence selection property. -/
public theorem hasMonotonicSSP_of_compactSpace (X : Type*) [TopologicalSpace X] [CompactSpace X] :
    HasMonotonicSSP X := by
  intro f hrow hanti
  have huniform (n : ℕ) : TendstoUniformly (fun k => (f n k).1) (fun _ => 0) atTop :=
    Antitone.tendstoUniformly_of_forall_tendsto (fun k => (f n k).2)
      (antitone_nat_of_succ_le (hanti n)) continuous_const
      (tendsto_pi_nhds.mp (tendsto_subtype_rng.mp (hrow n)))
  have hchoose (n : ℕ) : ∃ k, ∀ x, dist ((f n k).1 x) 0 < 1 / ((n : ℝ) + 1) := by
    have hε : 0 < 1 / ((n : ℝ) + 1) := by positivity
    simpa only [dist_comm (0 : ℝ)] using
      ((Metric.tendstoUniformly_iff.mp (huniform n)) _ hε).exists
  choose k hk using hchoose
  refine ⟨k, tendsto_subtype_rng.mpr (tendsto_pi_nhds.mpr fun x => ?_)⟩
  exact tendsto_iff_dist_tendsto_zero.mpr <|
    squeeze_zero (fun _ => dist_nonneg) (fun n => (hk n x).le)
      tendsto_one_div_add_atTop_nhds_zero_nat

-- The output depends on a finite prefix of row `n` in the Boolean coding of the Cantor set.
private noncomputable def cantorPulse (n k : ℕ) : Cp cantorSet :=
  ⟨fun x => if cantorSetHomeomorphNatToBool x (Nat.pair n k) = true ∧
      ∀ j : Fin k, cantorSetHomeomorphNatToBool x (Nat.pair n j) = false then 1 else 0, by
    let bits (x : cantorSet) (j : Fin (k + 1)) :=
      cantorSetHomeomorphNatToBool x (Nat.pair n j)
    have hbits : Continuous bits :=
      continuous_pi fun j => (continuous_apply (Nat.pair n j)).comp
        cantorSetHomeomorphNatToBool.continuous
    exact (continuous_of_discreteTopology (f := fun v : Fin (k + 1) → Bool =>
      if v (Fin.last k) = true ∧ ∀ j : Fin k, v j.castSucc = false then (1 : ℝ) else 0)).comp
      hbits⟩

/-- The space of continuous real-valued functions on the Cantor set, with the pointwise topology,
does not have the weak sequence selection property. -/
public theorem cantorSet_not_hasWeakSSP : ¬ HasWeakSSP cantorSet := by
  intro h
  have hrow (n : ℕ) : Tendsto (cantorPulse n) atTop (𝓝 (cpZero cantorSet)) := by
    refine tendsto_subtype_rng.mpr (tendsto_pi_nhds.mpr fun x => ?_)
    apply tendsto_const_nhds.congr'
    by_cases hx : ∃ j, cantorSetHomeomorphNatToBool x (Nat.pair n j) = true
    · obtain ⟨j, hj⟩ := hx
      filter_upwards [eventually_gt_atTop j] with k hjk
      have hprev : ¬ (∀ i : Fin k, cantorSetHomeomorphNatToBool x (Nat.pair n i) = false) :=
        fun hi => Bool.noConfusion (hj.symm.trans (hi ⟨j, hjk⟩))
      simp [cantorPulse, cpZero, hprev]
    · exact Eventually.of_forall fun k => by
        have hk : cantorSetHomeomorphNatToBool x (Nat.pair n k) ≠ true := fun ht => hx ⟨k, ht⟩
        simp [cantorPulse, cpZero, hk]
  obtain ⟨k, hk⟩ := h cantorPulse hrow
  let bits (i : ℕ) : Bool := decide ((Nat.unpair i).2 = k (Nat.unpair i).1)
  let x := cantorSetHomeomorphNatToBool.symm bits
  have hbit (n j : ℕ) : cantorSetHomeomorphNatToBool x (Nat.pair n j) = decide (j = k n) := by
    simp [x, bits]
  have heval (n : ℕ) : (cantorPulse n (k n)).1 x = 1 := by
    have hprev (j : Fin (k n)) : (j : ℕ) ≠ k n := j.isLt.ne
    simp [cantorPulse, hbit, hprev]
  have hcont : Continuous (fun g : Cp cantorSet => g.1 x) :=
    (continuous_apply x).comp continuous_subtype_val
  have hclosed : IsClosed {g : Cp cantorSet | g.1 x = 1} := isClosed_eq hcont continuous_const
  have hzero : (cpZero cantorSet).1 x = 1 :=
    closure_minimal (by rintro _ ⟨n, rfl⟩; exact heval n) hclosed hk
  exact zero_ne_one hzero

/--
Resolved false: Sakai proved that `C_p(X)` has the weak sequence selection property only when `X` is
zero-dimensional, so `C_p([0, 1])` lacks it, while monotone pointwise convergence to `𝟎` on the
compact space `[0, 1]` is uniform (Dini), which gives the monotonic sequence selection property.
The proof here uses the Cantor set instead of the interval. Source: Boaz Tsaban, *Selection
principles in mathematics: A milestone of open problems*, Note di Matematica 22 (2003/2004),
Problem 48 (Marion Scheepers, Proc. Amer. Math. Soc. 125 (1997), Problem 2);
resolution: Masami Sakai, *The sequence selection properties of Cₚ(X)*, Topology Appl. 154 (2007),
552–560, https://doi.org/10.1016/j.topol.2006.07.008.
-/
public theorem monotonicSSPImpliesWeakSSP_refuted : ¬ monotonicSSPImpliesWeakSSP := by
  intro h
  let _ : CompactSpace cantorSet := isCompact_iff_compactSpace.mp isCompact_cantorSet
  exact cantorSet_not_hasWeakSSP (h cantorSet (hasMonotonicSSP_of_compactSpace cantorSet))

end MathlibExt.Topology.MonotonicNotWeakSSPAMR134Problem0041Wanted
