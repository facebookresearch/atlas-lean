/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.SharpnessFromInputs
public import MathlibExt.Probability.Percolation.SurfaceReassembly
public import MathlibExt.Probability.Percolation.DifferentialInequality
public import MathlibExt.Probability.Percolation.PcNontrivial

/-!
# Sharpness of the phase transition for Bernoulli bond percolation on `ℤ^d`

The Duminil-Copin–Tassion theorem: for `d ≥ 1`, `p̃_c = p_c`; for every density `p` admitting a
finite `S ∋ 0` with `φ_p(S) < 1`, the one-arm probability `ℙ_p(0 ↔ ℤ^d \ Λ_{n-1})` decays
exponentially in `n`; and `θ(p) ≥ (p - p_c)/(p(1 - p_c))` for `p_c < p < 1`. This file discharges
the hypotheses of `StatMech.Percolation.sharpness`: `p̃_c > 0` (using `S = {0}`), `θ(1) = 1`,
exponential decay (`StatMech.Percolation.crossProb_exp_decay_of_phi_lt_one`) and the differential
inequality (`StatMech.Percolation.dct_diffineq_crossProbReal`).

## Main results

* `StatMech.Percolation.tildePc_pos`: `p̃_c(d) ≥ 1/(4d + 1) > 0`.
* `StatMech.Percolation.theta_one_eq_one`: `θ_d(1) = 1` for `d ≥ 1`.
* `StatMech.Percolation.crossProb_exp_decay_of_mem_tildePcSet`: exponential decay on `tildePcSet`.
* `StatMech.Percolation.sharp_phase_transition`: the theorem.

## References

* H. Duminil-Copin, V. Tassion, *A new proof of the sharpness of the phase transition for Bernoulli
  percolation and the Ising model*, Comm. Math. Phys. 343 (2016), 725–745.
* M. Aizenman, D. J. Barsky, *Sharpness of the phase transition in percolation models*, Comm. Math.
  Phys. 108 (1987), 489–526.
* M. V. Menshikov, *Coincidence of critical points in percolation problems*, Soviet Math. Dokl. 33
  (1986), 856–859.
-/

@[expose] public section

open MeasureTheory Set Filter Finset SimpleGraph
open scoped NNReal ENNReal Topology

namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}

theorem connWithinProb_le_one (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d)) (x : Site d) :
    connWithinProb d p hp S x ≤ 1 := by
  classical
  unfold connWithinProb
  split
  · split
    · exact measureReal_le_one
    · norm_num
  · norm_num

theorem phi_le_mul_card (p : ℝ≥0) (hp : p ≤ 1) (S : Finset (Site d)) :
    phi d p hp S ≤ (p : ℝ) * (boundaryEdges d S).card := by
  unfold phi
  apply mul_le_mul_of_nonneg_left _ p.coe_nonneg
  calc ∑ e ∈ boundaryEdges d S, connWithinProb d p hp S e.1
      ≤ ∑ _e ∈ boundaryEdges d S, (1 : ℝ) :=
        Finset.sum_le_sum (fun e _ => connWithinProb_le_one p hp S e.1)
    _ = (boundaryEdges d S).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- `p̃_c(d) > 0` for `d ≥ 1`: at `p = 1/(4d + 1)`, `φ_p({0}) ≤ 2dp < 1`. -/
theorem tildePc_pos (hd : 0 < d) : 0 < (tildePc d : ℝ) := by
  classical
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set p : ℝ≥0 := 1 / (4 * d + 1) with hp_def
  have hpos : 0 < p := by rw [hp_def]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp_def, div_le_one (by positivity)]
    have h4d : (0 : ℝ≥0) ≤ 4 * d := by positivity
    linarith
  set S : Finset (Site d) := {origin d} with hS_def
  have h0S : origin d ∈ S := by rw [hS_def]; exact Finset.mem_singleton_self _
  have hcard : (boundaryEdges d S).card ≤ 2 * d := by
    have := card_boundaryEdges_le S
    rwa [hS_def, Finset.card_singleton, one_mul] at this
  have hphi : phi d p hp1 S < 1 := by
    have hb := phi_le_mul_card p hp1 S
    have hcardR : ((boundaryEdges d S).card : ℝ) ≤ 2 * d := by exact_mod_cast hcard
    have hpR : (p : ℝ) = 1 / (4 * d + 1) := by rw [hp_def]; push_cast; ring
    calc phi d p hp1 S ≤ (p : ℝ) * (boundaryEdges d S).card := hb
      _ ≤ (p : ℝ) * (2 * d) := mul_le_mul_of_nonneg_left hcardR p.coe_nonneg
      _ = (1 / (4 * d + 1)) * (2 * d) := by rw [hpR]
      _ < 1 := by rw [div_mul_eq_mul_div, div_lt_one (by positivity)]; linarith
  have hmem : p ∈ tildePcSet d := ⟨hp1, S, h0S, hphi⟩
  have hle : p ≤ tildePc d := le_csSup ⟨1, fun q hq => (mem_tildePcSet.mp hq).1⟩ hmem
  have : (0 : ℝ≥0) < tildePc d := lt_of_lt_of_le hpos hle
  exact_mod_cast this

theorem wordEvent_adj (g : ℕ → Fin d × Bool) (n : ℕ) {ω : ConfigSpace (Sym2 (Site d))}
    (hω : ω ∈ wordEvent g n) (k : ℕ) (hk : k < n) :
    (openSubgraph d ω).Adj (vertOf g k) (vertOf g (k + 1)) := by
  rw [openSubgraph_adj]
  refine ⟨by rw [vertOf_succ]; exact adj_coordShift _ _ _, ?_⟩
  have := hω k (by simp [hk])
  unfold edgeOf at this
  rw [vertOf_succ] at this ⊢
  exact this

theorem wordEvent_connected (g : ℕ → Fin d × Bool) (n : ℕ)
    {ω : ConfigSpace (Sym2 (Site d))} (hω : ω ∈ wordEvent g n) :
    Connected d ω (origin d) (vertOf g n) := by
  induction n with
  | zero => simp only [vertOf]; exact connected_refl ω _
  | succ k ih =>
    have hωk : ω ∈ wordEvent g k :=
      fun j hj => hω j (by simp only [Finset.mem_range] at hj ⊢; omega)
    exact (ih hωk).trans (SimpleGraph.Adj.reachable (wordEvent_adj g (k + 1) hω k (by omega)))

/-- The direction sequence of the straight path from the origin along the first coordinate axis. -/
noncomputable def lineWord (hd : 0 < d) : ℕ → Fin d × Bool := fun _ => (⟨0, hd⟩, true)

theorem lineWord_coord0 (hd : 0 < d) (k : ℕ) :
    (vertOf (lineWord hd) k) ⟨0, hd⟩ = (k : ℤ) := by
  induction k with
  | zero => simp [vertOf, origin]
  | succ j ih =>
    rw [vertOf_succ, lineWord]
    simp only [coordShift, stepSign, ite_true, Function.update_self, ih]
    push_cast; ring

theorem wordEvent_measure_one (g : ℕ → Fin d × Bool) (n : ℕ) (h1 : (1 : ℝ≥0) ≤ 1) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) 1 h1) (wordEvent g n) = 1 := by
  rw [wordEvent_eq_pi, cylinder_all_open]; simp

theorem crossProb_one (hd : 0 < d) (h1 : (1 : ℝ≥0) ≤ 1) (n : ℕ) :
    crossProb d 1 h1 (n + 1) = 1 := by
  refine le_antisymm (crossProb_le_one d 1 h1 (n + 1)) ?_
  have hsub : wordEvent (lineWord hd) (n + 1) ⊆ crossingEvent d (n + 1) := by
    intro ω hω
    refine ⟨vertOf (lineWord hd) (n + 1), wordEvent_connected _ _ hω, ?_⟩
    rw [mem_box]; push Not
    refine ⟨⟨0, hd⟩, ?_⟩
    rw [lineWord_coord0 hd (n + 1)]
    have : (((n + 1 : ℕ) : ℤ)).natAbs = n + 1 := by omega
    omega
  unfold crossProb
  have hwe : (bernoulliProductMeasure (E := Sym2 (Site d)) 1 h1).real
      (wordEvent (lineWord hd) (n + 1)) = 1 := by
    rw [Measure.real, wordEvent_measure_one]; simp
  calc (1 : ℝ) = (bernoulliProductMeasure (E := Sym2 (Site d)) 1 h1).real
              (wordEvent (lineWord hd) (n + 1)) := hwe.symm
    _ ≤ (bernoulliProductMeasure (E := Sym2 (Site d)) 1 h1).real (crossingEvent d (n + 1)) :=
        measureReal_mono hsub (measure_ne_top _ _)

theorem theta_one_eq_one (hd : 0 < d) (h1 : (1 : ℝ≥0) ≤ 1) : theta d 1 h1 = 1 := by
  have htend := tendsto_crossProb_theta (d := d) 1 h1
  have heq : (fun n => crossProb d 1 h1 (n + 1)) = (fun _ => (1 : ℝ)) := by
    funext n; exact crossProb_one hd h1 n
  rw [heq] at htend
  exact tendsto_nhds_unique htend tendsto_const_nhds

theorem theta_one_ne_zero (hd : 0 < d) : ∀ h1 : (1 : ℝ≥0) ≤ 1, theta d 1 h1 ≠ 0 := by
  intro h1; rw [theta_one_eq_one hd h1]; norm_num

/-- Exponential decay of the one-arm probability for every `p ∈ tildePcSet d`, i.e. every `p`
admitting a finite `S ∋ 0` with `φ_p(S) < 1`. -/
theorem crossProb_exp_decay_of_mem_tildePcSet :
    ∀ p ∈ tildePcSet d, ∀ hp : p ≤ 1,
      ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n) := by
  intro p hpmem hp
  obtain ⟨hp', S, h0S, hphi⟩ := (mem_tildePcSet.mp hpmem)
  obtain ⟨N, hSN⟩ := Lattice.finite_subset_box (S : Set (Site d)) S.finite_toSet
  have hSbox : (S : Set (Site d)) ⊆ box d ((N + 1) - 1) := by
    rw [Nat.add_sub_cancel]; exact hSN
  exact crossProb_exp_decay_of_phi_lt_one p hp S h0S (by rwa [Subsingleton.elim hp hp'])
    (N + 1) (by omega) hSbox

/-- **Sharpness of the phase transition** for Bernoulli bond percolation on `ℤ^d`, `d ≥ 1`
(Duminil-Copin–Tassion 2016; Aizenman–Barsky 1987; Menshikov 1986):

1. `p̃_c = p_c`;
2. for every `p ∈ tildePcSet d` (a finite `S ∋ 0` has `φ_p(S) < 1`),
   `ℙ_p(0 ↔ ℤ^d \ Λ_{n-1}) ≤ C e^{-cn}` for some `c, C > 0`;
3. `θ(q) ≥ (q - p̃_c)/(q(1 - p̃_c))` for `p̃_c < q < 1`.

Scope of the items:
* Item 2 is stated on `tildePcSet d`, not on `[0, p_c)`: passing from `p < p̃_c` to
  `p ∈ tildePcSet d` needs monotonicity of `p ↦ φ_p(S)`, and passing from `p < p_c` to `θ(p) = 0`
  needs monotonicity of `θ`; neither is proved in MathlibExt (θ monotonicity is
  `theta_mono_parameter` in PhyslibExt `RandomCluster/PcUpperViaFK`).
* Item 3 is informative only when `p̃_c < 1`. This file does not prove that for any `d`; at `d = 1`
  it fails (`p̃_c = p_c = 1`) and item 3 is vacuous. For `d = 2`, `p_c < 1` is proved in PhyslibExt
  (`StatMech.Percolation.pc_two_lt_one_via_fk`), which with item 1 makes item 3 non-vacuous
  there. -/
theorem sharp_phase_transition (hd : 0 < d) :
    tildePc d = pc d ∧
      (∀ p ∈ tildePcSet d, ∀ hp : p ≤ 1,
        ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n)) ∧
      (∀ q : ℝ≥0, ∀ hq : q ≤ 1, tildePc d < q → (q : ℝ) < 1 →
        theta d q hq ≥ ((q : ℝ) - (tildePc d : ℝ)) / ((q : ℝ) * (1 - (tildePc d : ℝ)))) :=
  sharpness (tildePc_pos hd) (theta_one_ne_zero hd) crossProb_exp_decay_of_mem_tildePcSet
    (fun n _ t => deriv (crossPoly d n) t)
    (fun _q _hgt hq1 n => continuousOn_crossProbReal n (le_of_lt (tildePc_pos hd)) (le_of_lt hq1))
    (fun _q _hgt hq1 n _t ht =>
      hasDerivAt_crossProbReal n (lt_trans (tildePc_pos hd) ht.1) (lt_trans ht.2 hq1))
    (fun _q _hgt hq1 n _t ht => dct_diffineq_crossProbReal hq1 (tildePc_pos hd) n ht)

end Percolation

end StatMech
