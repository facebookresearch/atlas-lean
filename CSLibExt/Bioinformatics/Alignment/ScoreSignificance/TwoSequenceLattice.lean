/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Alignment.ScoreSignificance.TwoSequence

/-!
# Two-sequence alignment: the lattice case

**Gumbel approximation with a periodic correction, and liminf/limsup bounds, for lattice scores**
(conditional on a lattice one-sequence tail and asymptotic independence of diagonals).

`TwoSequence` (T187) proves `P(M_{m,n} ≤ log (m n) / θ + x) → exp (-K e^{-θ x})` from the
one-sequence tail `OneSequenceTail`, whose intended regime is nonlattice scores with `K > 0`. For
scores on a lattice `hℤ` (for example any integer scoring matrix) that tail fails whenever the
lattice constant is nonzero: the maximal segment score `M_L` lies on `hℤ`
(`maxSegScore_mem_lattice`), so `P(M_L > t)` depends on `t` only through `⌊t / h⌋`
(`scoreProb_lt_maxSegScore_eq`) and the ratio `P(M_L > t) / (L e^{-θ t})` oscillates with the
fractional part of `t / h`. The classical lattice tail (Karlin and Dembo 1992) reads instead
`P(M_L > t) = (K + o(1)) L e^{-θ t⁺}`, where `t⁺ = (⌊t / h⌋ + 1) h` (`latticeAbove h t`) is the
first lattice point above `t`.

## Main results

* `tendsto_twoProb_maxAlignScore_le_sub_lattice`: **Gumbel limit with periodic correction.** With
  `t_N = log (m_N n_N) / θ + x`,
  `P(M_{m_N, n_N} ≤ t_N) - exp (-K e^{-θ x} φ(t_N)) → 0`, where
  `φ(t) = e^{-θ (t⁺ - t)} = e^{-θ h (1 - {t / h})}` (`latticeCorr`) is `h`-periodic in `t`
  (`latticeCorr_add`) with values in `[e^{-θ h}, 1)` (`latticeCorr_mem_Icc`, `latticeCorr_lt_one`).
  The approximating sequence itself need not converge.
* `eventually_lattice_bounds`: **liminf/limsup bounds**: for `K ≥ 0` and every `ε > 0`, eventually
  `exp (-K e^{-θ x}) - ε ≤ P(M_{m,n} ≤ t_N) ≤ exp (-K e^{-θ (x + h)}) + ε`, the two-sequence
  analogue of `GumbelTail.LadderInput.eventually_lattice_bounds`.
* `tendsto_sum_exceedProb_sub_lattice`: the marginal step,
  `∑_d P(M_d > t_N) - K e^{-θ x} φ(t_N) → 0`.
* `scoreProb_lt_maxSegScore_eq`: for scores on `hℤ`, `P(M_L > t) = P(M_L ≥ t⁺)`, the reason the
  tail is stated at `t⁺`.

## Proof

The finite-size machinery of `TwoSequence` is reused unchanged: the Bonferroni sandwiches
(`twoProb_maxAlignScore_le_le`, `le_twoProb_maxAlignScore_le`), the dependence coefficients
`crossDep`, the finite-size marginal estimate `abs_sum_exceedProb_sub_le` (applied with the
threshold-dependent constant `K φ(t)`, since `e^{-θ t⁺} = φ(t) e^{-θ t}`), `tendsto_elemSymm` and
`tendsto_of_bonferroni`. Because `φ(t_N)` oscillates, the Poisson step runs along subsequences:
`φ(t_N)` lies in the compact `[e^{-θ h}, 1]`, so every subsequence has a further subsequence along
which `φ(t_N) → c`; along it `∑_d p_d → K e^{-θ x} c`, so the probabilities tend to
`exp (-K e^{-θ x} c)`, which is also the limit of the correction term.

## What is assumed, weakened and deferred

* `OneSequenceLatticeTail` is a **hypothesis**, as `OneSequenceTail` is in `TwoSequence`: the
  same uniform statement with `e^{-θ t}` replaced by `e^{-θ t⁺}` on the right. It is not derived
  from the lattice renewal theorem here, and no instance with `K ≠ 0` is constructed (the test
  file checks the degenerate zero score with `K = 0`, as `TwoSequence` does for its tail).
* `Δ_k → 0` (asymptotic independence of diagonals) is a hypothesis, exactly as in
  `tendsto_twoProb_maxAlignScore_le`.
* The theorems do not assume the scores lie on `hℤ`; only the tail hypothesis refers to `h`.
  `scoreProb_lt_maxSegScore_eq` records why that hypothesis is the natural one for lattice scores.
* **Not proved**: that the probabilities fail to converge when `K > 0`. Along a growth sequence
  where `log (m_N n_N) / θ` stays in one residue class mod `h` the probabilities do converge, so
  non-convergence needs an extra density condition on `log (m_N n_N)` (for example increments
  tending to `0`, as `GumbelTail.LadderInput.not_tendsto_lattice` has for one sequence). Also not
  covered: identifying `K` for lattice scores, edge corrections and gapped alignment.

## References

* S. Karlin and A. Dembo, *Limit distributions of maximal segmental score among Markov-dependent
  partial sums*, Adv. Appl. Probab. 24 (1992), 113–140 (lattice case of Theorem 1).
* A. Dembo, S. Karlin and O. Zeitouni, *Limit distribution of maximal non-aligned two-sequence
  segmental score*, Ann. Probab. 22 (1994), 2022–2039.
* S. Karlin and S. F. Altschul, *Methods for assessing the statistical significance of molecular
  sequence features by using general scoring schemes*, PNAS 87 (1990), 2264–2268.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Alignment.ScoreSignificance.TwoSequenceLattice

open Real Finset Filter Topology
open Cslib.Bioinformatics.Motifs.PWM Cslib.MachineLearning.LatentVariable.ExpectationMaximization
open Cslib.Bioinformatics.Alignment.ScoreSignificance.SingleSequence
open Cslib.Bioinformatics.Alignment.ScoreSignificance.TwoSequence

/-! ## The lattice point above a threshold and the periodic correction -/

section Lattice

/-- The first point `(⌊t / h⌋ + 1) h` of the lattice `hℤ` strictly above `t`. -/
noncomputable def latticeAbove (h t : ℝ) : ℝ := (⌊t / h⌋ + 1) * h

/-- The **periodic correction** `φ(t) = e^{-θ (t⁺ - t)}`, `t⁺ = latticeAbove h t`: the factor
with `e^{-θ t⁺} = φ(t) e^{-θ t}`. It equals `e^{-θ h (1 - {t / h})}`. -/
noncomputable def latticeCorr (θ h t : ℝ) : ℝ := exp (-θ * (latticeAbove h t - t))

variable {h : ℝ}

theorem lt_latticeAbove (hh : 0 < h) (t : ℝ) : t < latticeAbove h t :=
  (div_lt_iff₀ hh).1 (Int.lt_floor_add_one (t / h))

theorem latticeAbove_sub_le (hh : 0 < h) (t : ℝ) : latticeAbove h t - t ≤ h := by
  have h1 : (⌊t / h⌋ : ℝ) * h ≤ t := (le_div_iff₀ hh).1 (Int.floor_le (t / h))
  have h2 : latticeAbove h t = (⌊t / h⌋ : ℝ) * h + h := by rw [latticeAbove]; ring
  linarith

/-- `t⁺` is `h`-equivariant. -/
theorem latticeAbove_add (hh : h ≠ 0) (t : ℝ) : latticeAbove h (t + h) = latticeAbove h t + h := by
  simp only [latticeAbove]
  rw [add_div, div_self hh, Int.floor_add_one]
  push_cast; ring

/-- **The correction is `h`-periodic.** -/
theorem latticeCorr_add (θ : ℝ) (hh : h ≠ 0) (t : ℝ) :
    latticeCorr θ h (t + h) = latticeCorr θ h t := by
  simp only [latticeCorr]
  rw [latticeAbove_add hh]; congr 1; ring

theorem latticeCorr_mem_Icc {θ : ℝ} (hθ : 0 ≤ θ) (hh : 0 < h) (t : ℝ) :
    latticeCorr θ h t ∈ Set.Icc (exp (-θ * h)) 1 := by
  have h1 := latticeAbove_sub_le hh t
  have h2 := lt_latticeAbove hh t
  unfold latticeCorr
  refine ⟨exp_le_exp.2 ?_, exp_le_one_iff.2 ?_⟩ <;> nlinarith

theorem latticeCorr_lt_one {θ : ℝ} (hθ : 0 < θ) (hh : 0 < h) (t : ℝ) :
    latticeCorr θ h t < 1 := by
  have h1 := lt_latticeAbove hh t
  unfold latticeCorr
  exact Real.exp_lt_one_iff.2 (by nlinarith)

theorem exp_neg_mul_latticeAbove (θ h t : ℝ) :
    exp (-θ * latticeAbove h t) = latticeCorr θ h t * exp (-θ * t) := by
  rw [latticeCorr, ← exp_add]; congr 1; ring

/-- For `y` on the lattice `hℤ`, `t < y` iff `t⁺ ≤ y`. -/
theorem lt_iff_latticeAbove_le (hh : 0 < h) (t : ℝ) {y : ℝ} (hy : ∃ k : ℤ, y = k * h) :
    t < y ↔ latticeAbove h t ≤ y := by
  obtain ⟨k, rfl⟩ := hy
  refine ⟨fun hlt => ?_, fun hle => (lt_latticeAbove hh t).trans_le hle⟩
  have h1 : t / h < k := (div_lt_iff₀ hh).2 hlt
  have h2 : ⌊t / h⌋ + 1 ≤ k := Int.add_one_le_iff.2 (Int.floor_lt.2 h1)
  have h3 : (⌊t / h⌋ : ℝ) + 1 ≤ k := by exact_mod_cast h2
  exact mul_le_mul_of_nonneg_right h3 hh.le

theorem sum_mem_lattice : ∀ w : List ℝ, (∀ x ∈ w, ∃ k : ℤ, x = k * h) →
    ∃ k : ℤ, w.sum = k * h
  | [], _ => ⟨0, by simp⟩
  | a :: w, hw => by
      obtain ⟨i, hi⟩ := hw a (List.mem_cons_self ..)
      obtain ⟨j, hj⟩ := sum_mem_lattice w fun x hx => hw x (List.mem_cons_of_mem a hx)
      exact ⟨i + j, by rw [List.sum_cons, hi, hj]; push_cast; ring⟩

/-- **The maximal segment score of lattice scores is on the lattice.** -/
theorem maxSegScore_mem_lattice {l : List ℝ} (hl : ∀ x ∈ l, ∃ k : ℤ, x = k * h) :
    ∃ k : ℤ, maxSegScore l = k * h := by
  obtain ⟨w, hw, hsum⟩ := exists_infix_sum_eq_maxSegScore l
  rw [← hsum]
  exact sum_mem_lattice w fun x hx => hl x (hw.subset hx)

/-- **Why the lattice tail is stated at `t⁺`**: for scores on `hℤ`, `P(M_L > t) = P(M_L ≥ t⁺)`, so
the tail probability depends on `t` only through `⌊t / h⌋`. -/
theorem scoreProb_lt_maxSegScore_eq {γ : Type*} [Fintype γ] (q f : γ → ℝ) (hh : 0 < h)
    (hf : ∀ a, ∃ k : ℤ, f a = k * h) (L : ℕ) (t : ℝ) :
    scoreProb q f L (fun l => t < maxSegScore l) =
      scoreProb q f L (fun l => latticeAbove h t ≤ maxSegScore l) := by
  classical
  simp only [scoreProb, scoreExpect]
  refine sum_congr rfl fun w _ => ?_
  congr 1
  refine if_congr (lt_iff_latticeAbove_le hh t (maxSegScore_mem_lattice fun y hy => ?_)) rfl rfl
  simp only [List.mem_ofFn] at hy
  obtain ⟨i, rfl⟩ := hy
  exact hf _

end Lattice

/-- **Lattice one-sequence tail input** for the maximal segment score `M_L` of `L` iid scores with
law `(q, f)` and lattice span `h`: `P(M_L > t) = (K + o(1)) L e^{-θ t⁺}`, `t⁺ = latticeAbove h t`,
uniformly as `L → ∞` and `L e^{-θ t} → 0` over thresholds `t ≤ η L`. This is `OneSequenceTail`
with `e^{-θ t}` replaced by `e^{-θ t⁺}` on the right, the form of the lattice case of
Karlin–Dembo (1992); it is a hypothesis here, not derived. -/
def OneSequenceLatticeTail {γ : Type*} [Fintype γ] (q f : γ → ℝ) (θ K h : ℝ) : Prop :=
  ∀ ε > 0, ∃ L₀ : ℕ, ∃ δ > 0, ∃ η > 0, ∀ L : ℕ, L₀ ≤ L → ∀ t : ℝ,
    (L : ℝ) * exp (-θ * t) ≤ δ → t ≤ η * L →
      |scoreProb q f L (fun l => t < maxSegScore l) - K * L * exp (-θ * latticeAbove h t)| ≤
        ε * L * exp (-θ * latticeAbove h t)

section Gumbel

variable {β : Type*} [Fintype β] {p q : β → ℝ} (s : β → β → ℝ)

/-- **The expected number of exceeding diagonals, lattice case**: at
`t_N = log (m_N n_N) / θ + x`, `∑_d P(M_d > t_N) - K e^{-θ x} φ(t_N) → 0`. -/
theorem tendsto_sum_exceedProb_sub_lattice (hp : IsDist p) (hq : IsDist q) {θ K h : ℝ}
    (hθ : 0 < θ) (hh : 0 < h) (hroot : scoreMGF (pairLaw p q) (pairScore s) θ = 1)
    (htail : OneSequenceLatticeTail (pairLaw p q) (pairScore s) θ K h) {m n : ℕ → ℕ}
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    (hnm : Tendsto (fun N => log (n N) / m N) atTop (𝓝 0))
    (hmn' : Tendsto (fun N => log (m N) / n N) atTop (𝓝 0)) (x : ℝ) :
    Tendsto (fun N => ∑ d ∈ offsets (m N) (n N),
        exceedProb p q s (m N) (n N) (log (m N * n N) / θ + x) d -
          K * exp (-θ * x) * latticeCorr θ h (log (m N * n N) / θ + x)) atTop (𝓝 0) := by
  set A := exp (-θ * x) with hA
  have hA0 : 0 < A := exp_pos _
  have hmR : Tendsto (fun N => (m N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hm
  have hnR : Tendsto (fun N => (n N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hmn : Tendsto (fun N => (m N : ℝ) * n N) atTop atTop := hmR.atTop_mul_atTop₀ hnR
  have htm := tendsto_threshold_div (θ := θ) hm hn hnm x
  have htn : Tendsto (fun N => (log (m N * n N) / θ + x) / n N) atTop (𝓝 0) := by
    simpa only [mul_comm (m _ : ℝ)] using tendsto_threshold_div (θ := θ) hn hm hmn' x
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨L₀, δ, hδ, η, hη, hL⟩ := htail (ε / (2 * A)) (by positivity)
  set c := 2 * (1 + |K|) * A with hc
  have hc0 : 0 < c := by positivity
  set ρ := min 1 (ε / (4 * c)) with hρ
  have hρ0 : 0 < ρ := lt_min one_pos (by positivity)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hcρ : c * ρ ^ 2 < ε / 2 := by
    have h1 : ρ ^ 2 ≤ ρ := by nlinarith
    have h2 : c * ρ ≤ ε / 4 :=
      (mul_le_mul_of_nonneg_left (min_le_right 1 (ε / (4 * c))) hc0.le).trans_eq
        (by field_simp)
    nlinarith
  have hr : ∀ k : ℕ → ℕ, Tendsto (fun N => (k N : ℝ)) atTop atTop →
      Tendsto (fun N => (log (m N * n N) / θ + x) / k N) atTop (𝓝 0) →
      Tendsto (fun N => (L₀ + 1 + (log (m N * n N) / θ + x) / η) / k N) atTop (𝓝 0) := by
    intro k hk hkt
    have := (hk.inv_tendsto_atTop.const_mul ((L₀ : ℝ) + 1)).add (hkt.div_const η)
    simp only [mul_zero, zero_div, add_zero] at this
    refine this.congr fun N => ?_
    simp only [Pi.inv_apply]; ring
  have hev : ∀ᶠ N in atTop, A / δ ≤ m N ∧ A + 1 ≤ (m N : ℝ) * n N ∧
      (L₀ + 1 + (log (m N * n N) / θ + x) / η) / m N < ρ ∧
      (L₀ + 1 + (log (m N * n N) / θ + x) / η) / n N < ρ ∧ (0 : ℝ) < m N ∧ (0 : ℝ) < n N :=
    (hmR.eventually_ge_atTop _).and ((hmn.eventually_ge_atTop _).and
      (((hr m hmR htm).eventually (gt_mem_nhds hρ0)).and
        (((hr n hnR htn).eventually (gt_mem_nhds hρ0)).and
          ((hmR.eventually_gt_atTop 0).and (hnR.eventually_gt_atTop 0)))))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨h3, h4, hrm, hrn, hmpos, hnpos⟩ := hN₀ N hN
  set M := (m N : ℝ) * n N with hM
  have hM0 : 0 < M := mul_pos hmpos hnpos
  set t := log M / θ + x with ht
  have hEt : exp (-θ * t) = A / M := exp_neg_mul_threshold hθ.ne' hM0 x
  have htpos : 0 < t := by
    have : -θ * t < 0 := by
      rw [← Real.exp_lt_one_iff, hEt, div_lt_one hM0]; linarith
    nlinarith
  set r := (L₀ : ℝ) + 1 + t / η with hr_def
  have hrm' : r < ρ * m N := (div_lt_iff₀ hmpos).1 hrm
  have hrn' : r < ρ * n N := (div_lt_iff₀ hnpos).1 hrn
  set ℓ := max L₀ ⌈t / η⌉₊ with hℓ
  have htη : 0 ≤ t / η := by positivity
  have hℓr : (ℓ : ℝ) ≤ r := by
    rw [hℓ, Nat.cast_max]
    refine max_le (by linarith) ?_
    linarith [Nat.ceil_lt_add_one htη]
  have hℓm : ℓ ≤ m N := by
    have : (ℓ : ℝ) ≤ m N := by nlinarith
    exact_mod_cast this
  have hℓn : ℓ ≤ n N := by
    have : (ℓ : ℝ) ≤ n N := by nlinarith
    exact_mod_cast this
  have hnδ : (n N : ℝ) * exp (-θ * t) ≤ δ := by
    have hnA : (n N : ℝ) * (A / M) = A / m N := by rw [hM]; field_simp
    rw [hEt, hnA, div_le_iff₀ hmpos]
    rw [div_le_iff₀ hδ] at h3; linarith
  set φ := latticeCorr θ h t with hφ
  have hφ0 : 0 < φ := exp_pos _
  have hφ1 : φ ≤ 1 := (latticeCorr_mem_Icc hθ.le hh t).2
  have htail' : ∀ L : ℕ, ℓ ≤ L → L ≤ n N →
      |scoreProb (pairLaw p q) (pairScore s) L (fun l => t < maxSegScore l) -
        K * φ * L * exp (-θ * t)| ≤ ε / (2 * A) * φ * L * exp (-θ * t) := by
    intro L hLℓ hLn
    have h1 := hL L ((le_max_left _ _).trans hLℓ) t
      (le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hLn) (exp_pos _).le) hnδ)
      (by
        have h1 : t / η ≤ L :=
          (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hLℓ)
        rwa [div_le_iff₀ hη, mul_comm] at h1)
    rw [exp_neg_mul_latticeAbove] at h1
    rw [show K * φ * L * exp (-θ * t) = K * L * (φ * exp (-θ * t)) by ring,
      show ε / (2 * A) * φ * L * exp (-θ * t) = ε / (2 * A) * L * (φ * exp (-θ * t)) by ring]
    exact h1
  have key := abs_sum_exceedProb_sub_le s hp hq hθ.le hroot htail' (by positivity) hℓm hℓn htpos
  rw [hEt] at key
  rw [Real.dist_eq, sub_zero]
  have e1 : K * φ * M * (A / M) = K * A * φ := by field_simp
  have e2 : ε / (2 * A) * φ * M * (A / M) = ε / 2 * φ := by field_simp
  rw [e1, e2] at key
  have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
  have e3 : 2 * (1 + |K * φ|) * (ℓ : ℝ) ^ 2 * (A / M) ≤ c * ((ℓ : ℝ) ^ 2 / M) := by
    rw [hc, abs_mul, abs_of_pos hφ0]
    have hKφ : |K| * φ ≤ |K| := mul_le_of_le_one_right (abs_nonneg K) hφ1
    have hq0 : 0 ≤ (ℓ : ℝ) ^ 2 * (A / M) := by positivity
    calc 2 * (1 + |K| * φ) * (ℓ : ℝ) ^ 2 * (A / M)
        = 2 * (1 + |K| * φ) * ((ℓ : ℝ) ^ 2 * (A / M)) := by ring
      _ ≤ 2 * (1 + |K|) * ((ℓ : ℝ) ^ 2 * (A / M)) :=
        mul_le_mul_of_nonneg_right (by linarith) hq0
      _ = 2 * (1 + |K|) * A * ((ℓ : ℝ) ^ 2 / M) := by ring
  have hsq : (ℓ : ℝ) ^ 2 / M ≤ ρ ^ 2 := by
    rw [div_le_iff₀ hM0]
    have h1 : (ℓ : ℝ) ≤ ρ * m N := by linarith
    have h2 : (ℓ : ℝ) ≤ ρ * n N := by linarith
    calc (ℓ : ℝ) ^ 2 = ℓ * ℓ := sq _
      _ ≤ ρ * m N * (ρ * n N) := mul_le_mul h1 h2 hℓ0 (mul_pos hρ0 hmpos).le
      _ = ρ ^ 2 * M := by rw [hM]; ring
  have h5 : c * ((ℓ : ℝ) ^ 2 / M) ≤ c * ρ ^ 2 := mul_le_mul_of_nonneg_left hsq hc0.le
  have h6 : ε / 2 * φ ≤ ε / 2 := mul_le_of_le_one_right (by positivity) hφ1
  linarith

/-- **Gumbel approximation with periodic correction for lattice scores**, conditional on the
lattice one-sequence tail and asymptotic independence of diagonals.

Two independent iid sequences of lengths `m_N, n_N → ∞`, with `log n_N / m_N → 0` and
`log m_N / n_N → 0`, are scored by `s`, `θ > 0` is a Cramér root of the pair score, and the pair
score satisfies the lattice tail `OneSequenceLatticeTail … θ K h` with span `h > 0`. If the
cross-diagonal dependence coefficients vanish (`Δ_k → 0` for every `k`), then at
`t_N = log (m_N n_N) / θ + x`,
`P(M_{m_N, n_N} ≤ t_N) - exp (-K e^{-θ x} φ(t_N)) → 0`, with the `h`-periodic correction
`φ(t) = e^{-θ (t⁺ - t)} ∈ [e^{-θ h}, 1)` (`latticeCorr`). -/
theorem tendsto_twoProb_maxAlignScore_le_sub_lattice (hp : IsDist p) (hq : IsDist q)
    {θ K h : ℝ} (hθ : 0 < θ) (hh : 0 < h) (hroot : scoreMGF (pairLaw p q) (pairScore s) θ = 1)
    (htail : OneSequenceLatticeTail (pairLaw p q) (pairScore s) θ K h) {m n : ℕ → ℕ}
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    (hnm : Tendsto (fun N => log (n N) / m N) atTop (𝓝 0))
    (hmn' : Tendsto (fun N => log (m N) / n N) atTop (𝓝 0)) (x : ℝ)
    (hdep : ∀ k, Tendsto (fun N => crossDep p q s (m N) (n N) (log (m N * n N) / θ + x) k)
      atTop (𝓝 0)) :
    Tendsto (fun N => twoProb p q (m N) (n N)
        (fun u v => maxAlignScore s u v ≤ log (m N * n N) / θ + x) -
          exp (-(K * exp (-θ * x) * latticeCorr θ h (log (m N * n N) / θ + x)))) atTop
      (𝓝 0) := by
  set A := exp (-θ * x) with hA
  have hmR : Tendsto (fun N => (m N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hm
  have hnR : Tendsto (fun N => (n N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hn
  have hmn : Tendsto (fun N => (m N : ℝ) * n N) atTop atTop := hmR.atTop_mul_atTop₀ hnR
  have hpos : ∀ᶠ N in atTop, 0 < (m N : ℝ) ∧ 0 < (n N : ℝ) ∧ A + 1 ≤ (m N : ℝ) * n N :=
    (hmR.eventually_gt_atTop 0).and ((hnR.eventually_gt_atTop 0).and
      (hmn.eventually_ge_atTop _))
  have hthr : ∀ᶠ N in atTop, 0 < log (m N * n N) / θ + x ∧
      exp (-θ * (log (m N * n N) / θ + x)) = A / (m N * n N) := by
    filter_upwards [hpos] with N ⟨hm0, hn0, hA1⟩
    have hM0 : (0 : ℝ) < m N * n N := mul_pos hm0 hn0
    have hEt := exp_neg_mul_threshold hθ.ne' hM0 x
    refine ⟨?_, hEt⟩
    have : -θ * (log (m N * n N) / θ + x) < 0 := by
      rw [← Real.exp_lt_one_iff, hEt, div_lt_one hM0]; linarith
    nlinarith
  -- every diagonal's exceedance probability is at most `A / m`
  have hbound : ∀ᶠ N in atTop, ∀ d ∈ offsets (m N) (n N),
      exceedProb p q s (m N) (n N) (log (m N * n N) / θ + x) d ≤ A / m N := by
    filter_upwards [hpos, hthr] with N ⟨hm0, hn0, _⟩ ⟨ht, hEt⟩ d _
    refine (exceedProb_le s _ _ hp hq hθ.le hroot ht d).trans ?_
    rw [hEt]
    have hL : (diagLen (m N) (n N) d : ℝ) ≤ n N := by
      exact_mod_cast (min_le_right _ _).trans (Nat.sub_le _ _)
    calc (diagLen (m N) (n N) d : ℝ) * (A / (m N * n N)) ≤ n N * (A / (m N * n N)) :=
          mul_le_mul_of_nonneg_right hL (by positivity)
      _ = A / m N := by field_simp
  have hμ : Tendsto (fun N => A / m N) atTop (𝓝 0) := by
    have h := hmR.inv_tendsto_atTop.const_mul A
    rw [mul_zero] at h
    exact h.congr fun N => (div_eq_mul_inv _ _).symm
  have hmarg := tendsto_sum_exceedProb_sub_lattice s hp hq hθ hh hroot htail hm hn hnm hmn' x
  rw [← hA] at hmarg
  have hφ : ∀ N, latticeCorr θ h (log (m N * n N) / θ + x) ∈ Set.Icc (exp (-θ * h)) 1 :=
    fun N => latticeCorr_mem_Icc hθ.le hh _
  -- subsequence argument: along a subsequence on which the correction converges to `c`, the
  -- Poisson step of `TwoSequence` applies with mean `K A c`
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨c, -, ψ, hψ, hc⟩ := isCompact_Icc.tendsto_subseq fun k => hφ (ns k)
  refine ⟨ψ, ?_⟩
  have hν : Tendsto (fun j => ns (ψ j)) atTop atTop := hns.comp hψ.tendsto_atTop
  have hc' : Tendsto (fun j => latticeCorr θ h (log (m (ns (ψ j)) * n (ns (ψ j))) / θ + x))
      atTop (𝓝 c) := hc
  have hsum : Tendsto (fun j => ∑ d ∈ offsets (m (ns (ψ j))) (n (ns (ψ j))),
      exceedProb p q s (m (ns (ψ j))) (n (ns (ψ j)))
        (log (m (ns (ψ j)) * n (ns (ψ j))) / θ + x) d) atTop (𝓝 (K * A * c)) := by
    have hmarg' : Tendsto (fun j => ∑ d ∈ offsets (m (ns (ψ j))) (n (ns (ψ j))),
        exceedProb p q s (m (ns (ψ j))) (n (ns (ψ j)))
          (log (m (ns (ψ j)) * n (ns (ψ j))) / θ + x) d -
        K * A * latticeCorr θ h (log (m (ns (ψ j)) * n (ns (ψ j))) / θ + x)) atTop (𝓝 0) :=
      hmarg.comp hν
    have h1 := hmarg'.add (hc'.const_mul (K * A))
    rw [zero_add] at h1
    exact h1.congr fun j => by ring
  have he : ∀ k, Tendsto (fun j => elemSymm (offsets (m (ns (ψ j))) (n (ns (ψ j))))
      (exceedProb p q s (m (ns (ψ j))) (n (ns (ψ j)))
        (log (m (ns (ψ j)) * n (ns (ψ j))) / θ + x)) k) atTop
      (𝓝 ((K * A * c) ^ k / k.factorial)) := fun k =>
    tendsto_elemSymm (μ := fun j => A / m (ns (ψ j)))
      (fun j d _ => exceedProb_nonneg s _ _ _ hp hq d) (hν.eventually hbound) (hμ.comp hν)
      hsum k
  have hS : ∀ k, Tendsto (fun j => exceedMoment p q s (m (ns (ψ j))) (n (ns (ψ j)))
      (log (m (ns (ψ j)) * n (ns (ψ j))) / θ + x) k) atTop
      (𝓝 ((K * A * c) ^ k / k.factorial)) := fun k => by
    have hdep' : Tendsto (fun j => crossDep p q s (m (ns (ψ j))) (n (ns (ψ j)))
        (log (m (ns (ψ j)) * n (ns (ψ j))) / θ + x) k) atTop (𝓝 0) := (hdep k).comp hν
    simpa [crossDep] using (he k).add hdep'
  have hthr' := hν.eventually hthr
  have hP : Tendsto (fun j => twoProb p q (m (ns (ψ j))) (n (ns (ψ j)))
      (fun u v => maxAlignScore s u v ≤ log (m (ns (ψ j)) * n (ns (ψ j))) / θ + x)) atTop
      (𝓝 (exp (-(K * A * c)))) :=
    tendsto_of_bonferroni
      (fun r => hthr'.mono fun j hj => twoProb_maxAlignScore_le_le s _ _ hp hq hj.1.le r)
      (fun r => hthr'.mono fun j hj => le_twoProb_maxAlignScore_le s _ _ hp hq hj.1.le r) hS
  have hE : Tendsto (fun j => exp (-(K * A *
      latticeCorr θ h (log (m (ns (ψ j)) * n (ns (ψ j))) / θ + x)))) atTop
      (𝓝 (exp (-(K * A * c)))) :=
    (Real.continuous_exp.tendsto _).comp (hc'.const_mul (K * A)).neg
  have hlim := hP.sub hE
  rw [sub_self] at hlim
  exact hlim

/-- **Lattice liminf/limsup bounds** for two sequences (the two-sequence analogue of
`GumbelTail.LadderInput.eventually_lattice_bounds`): under the hypotheses of
`tendsto_twoProb_maxAlignScore_le_sub_lattice` and `K ≥ 0`, for every `ε > 0`, eventually
`exp (-K e^{-θ x}) - ε ≤ P(M_{m,n} ≤ log (m n) / θ + x) ≤ exp (-K e^{-θ (x + h)}) + ε`. -/
theorem eventually_lattice_bounds (hp : IsDist p) (hq : IsDist q) {θ K h : ℝ} (hθ : 0 < θ)
    (hh : 0 < h) (hK : 0 ≤ K) (hroot : scoreMGF (pairLaw p q) (pairScore s) θ = 1)
    (htail : OneSequenceLatticeTail (pairLaw p q) (pairScore s) θ K h) {m n : ℕ → ℕ}
    (hm : Tendsto m atTop atTop) (hn : Tendsto n atTop atTop)
    (hnm : Tendsto (fun N => log (n N) / m N) atTop (𝓝 0))
    (hmn' : Tendsto (fun N => log (m N) / n N) atTop (𝓝 0)) (x : ℝ)
    (hdep : ∀ k, Tendsto (fun N => crossDep p q s (m N) (n N) (log (m N * n N) / θ + x) k)
      atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, exp (-(K * exp (-θ * x))) - ε ≤
        twoProb p q (m N) (n N) (fun u v => maxAlignScore s u v ≤ log (m N * n N) / θ + x) ∧
      twoProb p q (m N) (n N) (fun u v => maxAlignScore s u v ≤ log (m N * n N) / θ + x) ≤
        exp (-(K * exp (-θ * (x + h)))) + ε := by
  have hmain := tendsto_twoProb_maxAlignScore_le_sub_lattice s hp hq hθ hh hroot htail hm hn hnm
    hmn' x hdep
  filter_upwards [Metric.tendsto_nhds.1 hmain ε hε] with N hN
  rw [Real.dist_eq, sub_zero, abs_lt] at hN
  have hKA : 0 ≤ K * exp (-θ * x) := mul_nonneg hK (exp_pos _).le
  obtain ⟨hlo, hhi⟩ := latticeCorr_mem_Icc hθ.le hh (log (m N * n N) / θ + x)
  have h1 : exp (-(K * exp (-θ * x))) ≤
      exp (-(K * exp (-θ * x) * latticeCorr θ h (log (m N * n N) / θ + x))) :=
    exp_le_exp.2 (neg_le_neg (mul_le_of_le_one_right hKA hhi))
  have e : K * exp (-θ * (x + h)) = K * exp (-θ * x) * exp (-θ * h) := by
    rw [mul_assoc, ← exp_add]; congr 2; ring
  have h2 : exp (-(K * exp (-θ * x) * latticeCorr θ h (log (m N * n N) / θ + x))) ≤
      exp (-(K * exp (-θ * (x + h)))) := by
    rw [e]; exact exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hlo hKA))
  constructor <;> linarith

end Gumbel

end Cslib.Bioinformatics.Alignment.ScoreSignificance.TwoSequenceLattice
