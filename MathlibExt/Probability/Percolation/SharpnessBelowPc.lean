/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.SharpnessTheorem
public import MathlibExt.Probability.Percolation.ConnectionsInsideSet
public import MathlibExt.Probability.CorrelationInequalities.InfiniteBK

/-!
# Exponential decay at every density below `p_c`

`StatMech.Percolation.sharp_phase_transition` proves exponential decay of the one-arm probability
on `tildePcSet d`, the densities `p` for which some finite `S ∋ 0` has `φ_p(S) < 1`. This file
proves that `p ↦ φ_p(S)` is nondecreasing, so `tildePcSet d` is a down-set, and deduces the
statement in the form taught in H. Duminil-Copin, *Introduction to Bernoulli percolation*, lecture
notes (version of 7 October 2018), Theorem 3.3: exponential decay for every `p < p_c`, and the
mean-field lower bound `θ(p) ≥ (p - p_c)/(p(1 - p_c))` for `p_c < p < 1`.

## Main results

* `StatMech.Percolation.connWithinProb_mono`, `StatMech.Percolation.phi_mono`: monotonicity in `p`.
* `StatMech.Percolation.mem_tildePcSet_of_lt_tildePc`: every `p < p̃_c` lies in `tildePcSet d`.
* `StatMech.Percolation.crossProb_exp_decay_of_lt_pc`: exponential decay for every `p < p_c`.
* `StatMech.Percolation.theta_eq_zero_of_lt_pc`: `θ(p) = 0` for every `p < p_c`.
* `StatMech.Percolation.sharp_phase_transition_pc`: both regimes, stated with `p_c`.

## References

* H. Duminil-Copin, *Introduction to Bernoulli percolation*, lecture notes, IHÉS (version of
  7 October 2018), Theorem 3.3 and its proof, equations (3.4)-(3.8).
* H. Duminil-Copin, V. Tassion, *A new proof of the sharpness of the phase transition for Bernoulli
  percolation and the Ising model*, Comm. Math. Phys. 343 (2016), 725–745, Theorem 1.1 and §1.2.
-/

@[expose] public section

open MeasureTheory Set Filter Finset
open scoped NNReal ENNReal Topology

namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}

/-- **Connection inside a set is an increasing event.** The event `{o ↔ x inside S}` is
increasing: opening edges keeps an open path open. -/
theorem isIncreasing_withinConnEvent (S : Set (Site d)) (o x : Site d) :
    IsIncreasing (withinConnEvent d S o x) := by
  intro ω ω' hle hω
  obtain ⟨ho, hx, hconn⟩ := hω
  refine ⟨ho, hx, hconn.mono ?_⟩
  intro u v huv
  simp only [openSubgraphInduce_adj, openSubgraph_adj] at huv ⊢
  refine ⟨huv.1, ?_⟩
  have h := hle s((u : Site d), (v : Site d))
  rw [huv.2] at h
  exact le_antisymm (Bool.le_true _) h

/-- **Connection inside a finite set depends on finitely many edges.** The event
`{o ↔ x inside S}` for a finite `S` depends only on the edges with both endpoints in `S`. -/
theorem withinConnEvent_dependsOn (S : Finset (Site d)) (o x : Site d) :
    StatMech.DependsOn (withinConnEvent d (S : Set (Site d)) o x)
      (edgesWithinFinset S : Set (Sym2 (Site d))) := by
  intro ω ω' hagree
  exact withinConn_congr S o x (fun e he => (hagree e he).symm)

/-- **Monotonicity of connection probabilities inside a finite set.** For `p ≤ q`,
`ℙ_p(0 ↔ x inside S) ≤ ℙ_q(0 ↔ x inside S)` (H. Duminil-Copin, *Introduction to Bernoulli
percolation*, lecture notes, 2018, Corollary 2.2, applied to the increasing event
`{0 ↔ x inside S}`). -/
theorem connWithinProb_mono {p q : ℝ≥0} (hp : p ≤ 1) (hq : q ≤ 1) (hpq : p ≤ q)
    (S : Finset (Site d)) (x : Site d) :
    connWithinProb d p hp S x ≤ connWithinProb d q hq S x := by
  by_cases h0 : origin d ∈ (S : Set (Site d))
  · by_cases hx : x ∈ (S : Set (Site d))
    · rw [connWithinProb_eq p hp S x h0 hx, connWithinProb_eq q hq S x h0 hx]
      exact ibk_measure_mono_parameter hp hq hpq (edgesWithinFinset S)
        (withinConnEvent_dependsOn S (origin d) x)
        (isIncreasing_withinConnEvent (S : Set (Site d)) (origin d) x)
    · have hx' : x ∉ S := by simpa using hx
      simp [connWithinProb, hx']
  · have h0' : origin d ∉ S := by simpa using h0
    simp [connWithinProb, h0']

/-- **Monotonicity of the Duminil-Copin–Tassion quantity.** For every finite `S` and `p ≤ q`,
`φ_p(S) ≤ φ_q(S)`, where `φ_p(S) = p ∑_{xy ∈ ΔS} ℙ_p(0 ↔ x inside S)` (H. Duminil-Copin,
*Introduction to Bernoulli percolation*, lecture notes, 2018, equation (3.4)). Both factors are
nondecreasing in `p`: the prefactor trivially, and each connection probability by
`connWithinProb_mono`. -/
theorem phi_mono {p q : ℝ≥0} (hp : p ≤ 1) (hq : q ≤ 1) (hpq : p ≤ q) (S : Finset (Site d)) :
    phi d p hp S ≤ phi d q hq S := by
  unfold phi
  apply mul_le_mul (by exact_mod_cast hpq)
    (Finset.sum_le_sum fun e _ => connWithinProb_mono hp hq hpq S e.1)
    (Finset.sum_nonneg fun e _ => connWithinProb_nonneg d p hp S e.1) q.coe_nonneg

/-- **The densities with `φ_p(S) < 1` for some `S` form a down-set.** If some finite `S ∋ 0`
has `φ_q(S) < 1` and `p ≤ q`, the same `S` has `φ_p(S) < 1`. -/
theorem mem_tildePcSet_of_le {p q : ℝ≥0} (hq : q ∈ tildePcSet d) (hpq : p ≤ q) :
    p ∈ tildePcSet d := by
  obtain ⟨hq1, S, h0S, hphi⟩ := mem_tildePcSet.mp hq
  have hp1 : p ≤ 1 := hpq.trans hq1
  exact mem_tildePcSet.mpr ⟨hp1, S, h0S, lt_of_le_of_lt (phi_mono hp1 hq1 hpq S) hphi⟩

/-- **Every density below `p̃_c` admits a finite set with `φ_p(S) < 1`.** Every density strictly
below `p̃_c(d) = sup tildePcSet d` lies in `tildePcSet d`. -/
theorem mem_tildePcSet_of_lt_tildePc {p : ℝ≥0} (hp : p < tildePc d) : p ∈ tildePcSet d := by
  obtain ⟨q, hq, hpq⟩ := exists_lt_of_lt_csSup' hp
  exact mem_tildePcSet_of_le hq hpq.le

/-- **Exponential decay below `p_c`** for Bernoulli bond percolation on `ℤ^d`, `d ≥ 1`: for every
`p < p_c(d)` there are `c, C > 0` with `ℙ_p(0 ↔ ℤ^d \ Λ_{n-1}) ≤ C e^{-cn}` for all `n`
(H. Duminil-Copin, *Introduction to Bernoulli percolation*, lecture notes, 2018, Theorem 3.3, first
assertion; Duminil-Copin and Tassion, Comm. Math. Phys. 343 (2016), Theorem 1.1, item 3). The
lecture notes state the bound as `exp(-c_p n)` for `n ≥ 1`; here it carries a prefactor `C`. -/
theorem crossProb_exp_decay_of_lt_pc (hd : 0 < d) {p : ℝ≥0} (hp : p ≤ 1) (hlt : p < pc d) :
    ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n) := by
  have hmem : p ∈ tildePcSet d := by
    apply mem_tildePcSet_of_lt_tildePc
    rwa [(sharp_phase_transition hd).1]
  exact crossProb_exp_decay_of_mem_tildePcSet p hmem hp

/-- **No percolation below `p_c`**: `θ_d(p) = 0` for every `p < p_c(d)`, `d ≥ 1`. The definition
`p_c = sup {p : θ(p) = 0}` gives this only together with monotonicity of `θ`; here it follows from
exponential decay (`crossProb_exp_decay_of_lt_pc`). -/
theorem theta_eq_zero_of_lt_pc (hd : 0 < d) {p : ℝ≥0} (hp : p ≤ 1) (hlt : p < pc d) :
    theta d p hp = 0 :=
  theta_eq_zero_of_crossProb_decay p hp (crossProb_exp_decay_of_lt_pc hd hp hlt)

/-- **Sharpness of the phase transition, stated with `p_c`** (H. Duminil-Copin, *Introduction to
Bernoulli percolation*, lecture notes, 2018, Theorem 3.3; Duminil-Copin and Tassion, Comm. Math.
Phys. 343 (2016), Theorem 1.1 and the nearest-neighbour bound of §1.2). For Bernoulli bond
percolation on `ℤ^d`, `d ≥ 1`:

1. for every `p < p_c`, `ℙ_p(0 ↔ ℤ^d \ Λ_{n-1}) ≤ C e^{-cn}` for some `c, C > 0`;
2. for every `p_c < p < 1`, `θ(p) ≥ (p - p_c)/(p(1 - p_c))`.

The lecture notes state item 1 as `ℙ_p(0 ↔ ∂Λ_n) ≤ exp(-c_p n)` for every `n ≥ 1`; with the
prefactor `C` the statement here is weaker than that form. Item 2 is vacuous when `p_c = 1`, as for
`d = 1`; for `d ≥ 2`, `p_c < 1` is proved in PhyslibExt
(`StatMech.Percolation.pc_lt_one_of_two_le_via_fk`), so item 2 is informative there. -/
theorem sharp_phase_transition_pc (hd : 0 < d) :
    (∀ p : ℝ≥0, ∀ hp : p ≤ 1, p < pc d →
        ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n)) ∧
      (∀ p : ℝ≥0, ∀ hp : p ≤ 1, pc d < p → (p : ℝ) < 1 →
        theta d p hp ≥ ((p : ℝ) - (pc d : ℝ)) / ((p : ℝ) * (1 - (pc d : ℝ)))) := by
  obtain ⟨heq, -, hmf⟩ := sharp_phase_transition hd
  refine ⟨fun p hp hlt => crossProb_exp_decay_of_lt_pc hd hp hlt, fun p hp hgt hp1 => ?_⟩
  rw [← heq] at hgt ⊢
  exact hmf p hp hgt hp1

end Percolation

end StatMech
