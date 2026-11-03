/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.RussoDerivative
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint
public import CSLibExt.Complexity.BooleanFunctions.SharpnessFK

/-!
# Sharp threshold estimates for the `q = 2` random-cluster model

A Russo-type differential inequality for FK probabilities at `q = 2`, its integrated form giving
exponential decay of crossing probabilities, and the resulting vanishing of the percolation
probability below the critical point, each from explicit covariance inputs.

## i. Overview

Russo's formula writes `d/dp φ_p(A)` as `1 / (p (1 - p))` times the sum of the covariances of `1_A`
with the edge states, and `1 / (p (1 - p)) ≥ 4`. An OSSS-type lower bound on that covariance sum by
`n c₀ θ (1 - θ) / D` then gives `θ' ≥ (4 n c₀ κ / D) θ` whenever `θ ≤ 1 - κ`; integrating over `[a,
b]` gives `θ(a) ≤ exp(-(4 n c₀ κ / D)(b - a))`. All three results are conditional.
`pointwise_di_fk_q2` takes the covariance lower bound `hFKcov` and the bound `hθub`.
`fk_q2_crossing_decay` takes `hdiff` (differentiability in `p`), `hFKcov` and `hθub` on all of `[a,
b]`. `fkTheta_subcritical_eq_zero` takes the family input `hFKcovFam` (the same three premises for
the box crossing events) and `hBridge`, which asserts that the crossing-decay bounds imply `θ(p) =
0` for `p ≤ p_c`; the conclusion follows from `hBridge` once the decay is established, so the step
from crossing decay to `θ = 0` is assumed, not proved.

## ii. Key results

- `pointwise_di_fk_q2` : the differential inequality `θ' ≥ (4 n c₀ κ / D) θ`.
- `fk_q2_crossing_decay` : exponential decay of `φ_a(A)` in `n`.
- `fkTheta_subcritical_eq_zero` : `θ(p) = 0` for `p ≤ p_c`, given `hFKcovFam` and `hBridge`.

## iii. Table of contents

- A. Elementary bounds
- B. FK event probabilities lie in `[0, 1]`
- C. The differential inequality and its integration
- D. Vanishing of the percolation probability

## iv. References

- L. Russo, *On the critical percolation probabilities*, Z. Wahrsch. Verw. Gebiete 56 (1981).
- H. Duminil-Copin, *Lectures on the Ising and Potts models on the hypercubic lattice*, lecture
  notes (2017).
- G. Grimmett, *The Random-Cluster Model*, Springer (2006).
-/

@[expose] public section

open scoped BigOperators
open Finset Real Set

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

/-! ## A. Elementary bounds -/

lemma mul_one_sub_le_quarter (x : ℝ) : x * (1 - x) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (x - 1 / 2)]

lemma russoPrefactor_ge_four {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    (4 : ℝ) ≤ russoPrefactor x := by
  unfold russoPrefactor
  have hxx : 0 < x * (1 - x) := mul_pos hx0 (by linarith)
  have hle : x * (1 - x) ≤ 1 / 4 := mul_one_sub_le_quarter x
  rw [one_div, le_inv_comm₀ (by norm_num) hxx]
  linarith [hle]

/-! ## B. FK event probabilities lie in `[0, 1]` -/

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma fkProbOf_nonneg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace (Sym2 V))) : 0 ≤ fkProbOf G p q A := by
  classical
  unfold fkProbOf fkMean
  apply Finset.sum_nonneg
  intro ω _
  apply mul_nonneg
  · rw [Set.indicator_apply]; split_ifs <;> norm_num
  · exact fkProb_nonneg G hp hp1 hq ω

lemma fkProbOf_le_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace (Sym2 V))) : fkProbOf G p q A ≤ 1 := by
  classical
  unfold fkProbOf fkMean
  calc ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * fkProb G p q ω
      ≤ ∑ ω, fkProb G p q ω := by
        apply Finset.sum_le_sum
        intro ω _
        rw [Set.indicator_apply]
        split_ifs
        · rw [one_mul]
        · rw [zero_mul]; exact fkProb_nonneg G hp hp1 hq ω
    _ = 1 := fkProb_sum_eq_one G hp hp1 hq

/-! ## C. The differential inequality and its integration -/

/-- Russo-type differential inequality at `q = 2`: under the covariance lower bound `hFKcov` and
`θ ≤ 1 - κ`, the derivative of `p ↦ φ_p(A)` is at least `(4 n c₀ κ / D) φ_p(A)`. -/
lemma pointwise_di_fk_q2 {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (A : Set (ConfigSpace (Sym2 V)))
    (c₀ D κ : ℝ) (hc₀ : 0 < c₀) (hD : 0 < D) (hκ : 0 < κ)
    (hFKcov : (n : ℝ) * c₀
        * (fkProbOf G p 2 A * (1 - fkProbOf G p 2 A))
      ≤ D * ∑ e ∈ G.edgeFinset,
          fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (coord e))
    (hθub : fkProbOf G p 2 A ≤ 1 - κ) :
    (4 * (n : ℝ) * c₀ * κ / D) * fkProbOf G p 2 A
      ≤ deriv (fun p => fkProbOf G p 2 A) p := by
  set θ := fkProbOf G p 2 A with hθdef
  set S := ∑ e ∈ G.edgeFinset,
      fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (coord e) with hSdef
  set θ' := deriv (fun p => fkProbOf G p 2 A) p with hθ'def
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hθnn : 0 ≤ θ := fkProbOf_nonneg G hp hp1 (by norm_num) A
  have hRussoEq : θ' = russoPrefactor p * S := by
    rw [hθ'def, hSdef, deriv_fkProbOf G hp hp1 (by norm_num : (0:ℝ) < 2) A]
    unfold russoPrefactor
    rw [one_div, div_eq_inv_mul]
  have hcR : (4 : ℝ) ≤ russoPrefactor p := russoPrefactor_ge_four hp hp1
  have hfac : θ * κ ≤ θ * (1 - θ) := mul_le_mul_of_nonneg_left (by linarith [hθub]) hθnn
  have hSlb : (n : ℝ) * c₀ * (θ * κ) / D ≤ S := by
    rw [div_le_iff₀ hD]
    have habs : (n : ℝ) * c₀ * (θ * κ) ≤ (n : ℝ) * c₀ * (θ * (1 - θ)) :=
      mul_le_mul_of_nonneg_left hfac (by positivity)
    linarith [habs, hFKcov]
  have hSnn : 0 ≤ S := le_trans (by positivity) hSlb
  have h4S : 4 * S ≤ θ' := by rw [hRussoEq]; nlinarith [hcR, hSnn]
  calc (4 * (n : ℝ) * c₀ * κ / D) * θ
      = 4 * ((n : ℝ) * c₀ * (θ * κ) / D) := by ring
    _ ≤ 4 * S := mul_le_mul_of_nonneg_left hSlb (by norm_num)
    _ ≤ θ' := h4S

/-- Integrated form at `q = 2`: if the hypotheses of the differential inequality hold on `[a,
b]`, then `φ_a(A) ≤ exp(-(4 n c₀ κ / D)(b - a))`. -/
theorem fk_q2_crossing_decay {n : ℕ} (hn : 1 ≤ n)
    (A : Set (ConfigSpace (Sym2 V)))
    (c₀ D κ : ℝ) (hc₀ : 0 < c₀) (hD : 0 < D) (hκ : 0 < κ)
    (a b : ℝ) (hab : a < b) (ha0 : 0 < a) (hb1 : b < 1)
    (hdiff : ∀ p ∈ Icc a b,
      HasDerivAt (fun p => fkProbOf G p 2 A)
        (deriv (fun p => fkProbOf G p 2 A) p) p)
    (hFKcov : ∀ p ∈ Icc a b, (n : ℝ) * c₀
        * (fkProbOf G p 2 A * (1 - fkProbOf G p 2 A))
      ≤ D * ∑ e ∈ G.edgeFinset,
          fkCov G p 2 (A.indicator (fun _ => (1 : ℝ))) (coord e))
    (hθub : ∀ p ∈ Icc a b, fkProbOf G p 2 A ≤ 1 - κ) :
    fkProbOf G a 2 A
      ≤ Real.exp (-(4 * (n : ℝ) * c₀ * κ / D * (b - a))) := by
  set rate : ℝ := 4 * (n : ℝ) * c₀ * κ / D with hratedef
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hrate : 0 < rate := by
    rw [hratedef]; positivity
  have hpbounds : ∀ p ∈ Icc a b, 0 < p ∧ p < 1 := by
    intro p hp
    rw [Set.mem_Icc] at hp
    exact ⟨lt_of_lt_of_le ha0 hp.1, lt_of_le_of_lt hp.2 hb1⟩
  have hineq : ∀ p ∈ Icc a b,
      rate * fkProbOf G p 2 A ≤ deriv (fun p => fkProbOf G p 2 A) p := by
    intro p hp
    obtain ⟨hp0, hp1⟩ := hpbounds p hp
    rw [hratedef]
    exact pointwise_di_fk_q2 G hn hp0 hp1 A c₀ D κ hc₀ hD hκ (hFKcov p hp) (hθub p hp)
  have hθa : 0 ≤ fkProbOf G a 2 A := by
    obtain ⟨ha0', _⟩ := hpbounds a (left_mem_Icc.2 hab.le)
    exact fkProbOf_nonneg G ha0' (lt_trans hab (hpbounds b (right_mem_Icc.2 hab.le)).2)
      (by norm_num) A
  have hθb : fkProbOf G b 2 A ≤ 1 := by
    obtain ⟨hb0', hb1'⟩ := hpbounds b (right_mem_Icc.2 hab.le)
    exact fkProbOf_le_one G hb0' hb1' (by norm_num) A
  have hfin := OSSS.SharpnessFK.subcritical_decay a b rate hab hrate
    (fun p => fkProbOf G p 2 A) (fun p => deriv (fun p => fkProbOf G p 2 A) p)
    hdiff hineq hθa hθb
  exact hfin.2.1

/-! ## D. Vanishing of the percolation probability -/

/-- Conditional vanishing of the `q = 2` percolation probability for `p ≤ p_c`, from the box
covariance inputs `hFKcovFam` and the assumed step `hBridge` from crossing decay to `θ = 0`. -/
theorem fkTheta_subcritical_eq_zero (d : ℕ)
    (c₀ D κ : ℝ) (hc₀ : 0 < c₀) (hD : 0 < D) (hκ : 0 < κ)
    (a b : ℝ) (hab : a < b) (ha0 : 0 < a) (hb1 : b < 1)
    (Across : ∀ N : ℕ, Set (ConfigSpace (Sym2 (boxVerts d N))))
    (hFKcovFam : ∀ (N : ℕ), 1 ≤ N → ∀ p ∈ Icc a b,
        HasDerivAt (fun p => fkProbOf (boxGraph d N) p 2 (Across N))
          (deriv (fun p => fkProbOf (boxGraph d N) p 2 (Across N)) p) p
      ∧ ((N : ℝ) * c₀
            * (fkProbOf (boxGraph d N) p 2 (Across N)
                * (1 - fkProbOf (boxGraph d N) p 2 (Across N)))
          ≤ D * ∑ e ∈ (boxGraph d N).edgeFinset,
              fkCov (boxGraph d N) p 2 ((Across N).indicator (fun _ => (1 : ℝ))) (coord e))
      ∧ fkProbOf (boxGraph d N) p 2 (Across N) ≤ 1 - κ)
    (hBridge : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
        (∀ N : ℕ, 1 ≤ N →
          fkProbOf (boxGraph d N) a 2 (Across N)
            ≤ Real.exp (-(4 * (N : ℝ) * c₀ * κ / D * (b - a)))) →
        FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0) :
    ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0 := by
  intro p hp hp1 hple
  have hdecay : ∀ N : ℕ, 1 ≤ N →
      fkProbOf (boxGraph d N) a 2 (Across N)
        ≤ Real.exp (-(4 * (N : ℝ) * c₀ * κ / D * (b - a))) := by
    intro N hN
    have hfam := hFKcovFam N hN
    exact fk_q2_crossing_decay (boxGraph d N) hN (Across N) c₀ D κ hc₀ hD hκ
      a b hab ha0 hb1
      (fun p hp' => (hfam p hp').1)
      (fun p hp' => (hfam p hp').2.1)
      (fun p hp' => (hfam p hp').2.2)
  exact hBridge p hp hp1 hple hdecay

end FK

end StatMech
