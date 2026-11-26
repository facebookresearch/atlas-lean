/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Percolation.SharpnessBelowPc
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Finite susceptibility below `p_c`

For Bernoulli bond percolation on `ℤ^d`, `d ≥ 1`, and every `p < p_c(d)`, the susceptibility
`χ(p) = ∑_{x ∈ ℤ^d} ℙ_p(0 ↔ x)`, the expected size of the cluster of the origin, is finite. This
is item 2 of Theorem 1.1 of Duminil-Copin and Tassion (2016). Here it is deduced from exponential
decay of the one-arm probability (`StatMech.Percolation.crossProb_exp_decay_of_lt_pc`): a site at
sup-norm distance `k ≥ 1` from the origin lies outside `Λ_{k-1}`, so `ℙ_p(0 ↔ x) ≤ C e^{-ck}`,
and `Λ_k` has `(2k + 1)^d` sites.

## Main results

* `StatMech.Percolation.card_boxFinset`: `|Λ_n| = (2n + 1)^d`, a restatement of
  `StatMech.Lattice.boxSV_card_boxF`.
* `StatMech.Percolation.connProb_le_crossProb`: `ℙ_p(0 ↔ x) ≤ ℙ_p(0 ↔ ℤ^d \ Λ_{‖x‖_∞ - 1})`.
* `StatMech.Percolation.summable_connProb_of_lt_pc`: finite susceptibility below `p_c`.

## References

* H. Duminil-Copin, V. Tassion, *A new proof of the sharpness of the phase transition for Bernoulli
  percolation and the Ising model*, Comm. Math. Phys. 343 (2016), 725–745 (arXiv:1502.03050v3),
  Theorem 1.1, item 2.
-/

@[expose] public section

open MeasureTheory Set Filter Finset
open scoped NNReal ENNReal Topology

namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}

/-- **Sup-norm of a lattice site.** The sup-norm `‖x‖_∞ = max_i |x_i|` of a site, as a natural
number. -/
def supNorm (x : Site d) : ℕ := Finset.univ.sup fun i => (x i).natAbs

theorem supNorm_le_iff {x : Site d} {n : ℕ} : supNorm x ≤ n ↔ x ∈ box d n := by
  simp [supNorm, Finset.sup_le_iff, mem_box]

/-- **Number of sites of a box.** The box `Λ_n = [-n, n]^d` has `(2n + 1)^d` sites. This restates
`StatMech.Lattice.boxSV_card_boxF` for `boxFinset`, which equals `boxSV_boxF` by
`boxSV_boxF_eq_toFinset`. -/
theorem card_boxFinset (d n : ℕ) : (boxFinset d n).card = (2 * n + 1) ^ d := by
  rw [show boxFinset d n = boxSV_boxF d n from (boxSV_boxF_eq_toFinset d n).symm,
    boxSV_card_boxF]

/-- **Connection probabilities are bounded by one-arm probabilities.** For every site `x`,
`ℙ_p(0 ↔ x) ≤ ℙ_p(0 ↔ ℤ^d \ Λ_{‖x‖_∞ - 1})` once `‖x‖_∞ ≥ 1`: the site `x` itself lies outside
`Λ_{‖x‖_∞ - 1}`. -/
theorem connProb_le_crossProb (hd : 0 < d) (p : ℝ≥0) (hp : p ≤ 1) {x : Site d}
    (hx : 1 ≤ supNorm x) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real {ω | Connected d ω (origin d) x} ≤
      crossProb d p hp (supNorm x) := by
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hd⟩⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup _ hne fun i => (x i).natAbs
  have hxout : x ∉ box d (supNorm x - 1) := by
    intro hmem
    have := (mem_box.mp hmem) i
    rw [← hi] at this
    change supNorm x ≤ supNorm x - 1 at this
    omega
  exact measureReal_mono (fun ω hω => ⟨x, hω, hxout⟩)

/-- **Summability of polynomially weighted exponentials.** For `c > 0` the sequence
`k ↦ (2k + 1)^d e^{-ck}` is summable. -/
theorem summable_card_mul_exp {c : ℝ} (hc : 0 < c) (d : ℕ) :
    Summable fun k : ℕ => ((2 * k + 1 : ℕ) : ℝ) ^ d * Real.exp (-c * k) := by
  have h1 := Real.summable_pow_mul_exp_neg_nat_mul d hc
  have h2 : Summable fun k : ℕ => Real.exp (-c * k) := by
    simpa using Real.summable_pow_mul_exp_neg_nat_mul 0 hc
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((h1.mul_left (3 ^ d)).add h2)
  have hexp := Real.exp_pos (-c * k)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hle : ((2 * k + 1 : ℕ) : ℝ) ^ d ≤ 3 ^ d * (k : ℝ) ^ d := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      push_cast; linarith
    have : ((2 * k + 1 : ℕ) : ℝ) ^ d * Real.exp (-c * k) ≤
        3 ^ d * ((k : ℝ) ^ d * Real.exp (-c * k)) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hle hexp.le
    linarith

/-- **Finite susceptibility below `p_c`** (Duminil-Copin and Tassion, Comm. Math. Phys. 343
(2016), Theorem 1.1, item 2). For Bernoulli bond percolation on `ℤ^d`, `d ≥ 1`, and every
`p < p_c(d)`, the susceptibility `∑_{x ∈ ℤ^d} ℙ_p(0 ↔ x)` is finite: the family
`x ↦ ℙ_p(0 ↔ x)` is summable. -/
theorem summable_connProb_of_lt_pc (hd : 0 < d) {p : ℝ≥0} (hp : p ≤ 1) (hlt : p < pc d) :
    Summable fun x : Site d =>
      (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        {ω | Connected d ω (origin d) x} := by
  obtain ⟨c, hc, C, hC, hdecay⟩ := crossProb_exp_decay_of_lt_pc hd hp hlt
  set μ := bernoulliProductMeasure (E := Sym2 (Site d)) p hp
  set f : Site d → ℝ := fun x => μ.real {ω | Connected d ω (origin d) x}
  set C' : ℝ := max C 1
  set g : ℕ → ℝ := fun k => C' * Real.exp (-c * k)
  have hf0 : ∀ x, 0 ≤ f x := fun x => measureReal_nonneg
  have hfg : ∀ x, f x ≤ g (supNorm x) := by
    intro x
    rcases Nat.eq_zero_or_pos (supNorm x) with h0 | hpos
    · have hle1 : f x ≤ 1 := measureReal_le_one
      simp only [g, h0, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
      exact hle1.trans (le_max_right _ _)
    · calc f x ≤ crossProb d p hp (supNorm x) := connProb_le_crossProb hd p hp hpos
        _ ≤ C * Real.exp (-c * supNorm x) := hdecay _
        _ ≤ g (supNorm x) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  have hsum := (summable_card_mul_exp hc d).mul_left C'
  refine summable_of_sum_le hf0 (c := ∑' k : ℕ, C' * (((2 * k + 1 : ℕ) : ℝ) ^ d *
    Real.exp (-c * k))) fun u => ?_
  have hterm : ∀ k : ℕ, 0 ≤ C' * (((2 * k + 1 : ℕ) : ℝ) ^ d * Real.exp (-c * k)) := fun k => by
    have : (0 : ℝ) ≤ C' := le_trans zero_le_one (le_max_right _ _)
    positivity
  calc ∑ x ∈ u, f x ≤ ∑ x ∈ u, g (supNorm x) := Finset.sum_le_sum fun x _ => hfg x
    _ = ∑ k ∈ u.image supNorm, (u.filter fun x => supNorm x = k).card • g k :=
        Finset.sum_comp g supNorm
    _ ≤ ∑ k ∈ u.image supNorm, C' * (((2 * k + 1 : ℕ) : ℝ) ^ d * Real.exp (-c * k)) := by
        apply Finset.sum_le_sum
        intro k _
        rw [nsmul_eq_mul]
        have hcard : (u.filter fun x => supNorm x = k).card ≤ (2 * k + 1) ^ d := by
          rw [← card_boxFinset d k]
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_filter] at hx
          rw [mem_boxFinset, ← supNorm_le_iff, hx.2]
        have hcard' : ((u.filter fun x => supNorm x = k).card : ℝ) ≤
            ((2 * k + 1 : ℕ) : ℝ) ^ d := by exact_mod_cast hcard
        have hg0 : 0 ≤ g k := by
          have : (0 : ℝ) ≤ C' := le_trans zero_le_one (le_max_right _ _)
          positivity
        calc ((u.filter fun x => supNorm x = k).card : ℝ) * g k
            ≤ ((2 * k + 1 : ℕ) : ℝ) ^ d * g k := mul_le_mul_of_nonneg_right hcard' hg0
          _ = C' * (((2 * k + 1 : ℕ) : ℝ) ^ d * Real.exp (-c * k)) := by simp only [g]; ring
    _ ≤ ∑' k : ℕ, C' * (((2 * k + 1 : ℕ) : ℝ) ^ d * Real.exp (-c * k)) :=
        hsum.sum_le_tsum _ fun k _ => hterm k

end Percolation

end StatMech
