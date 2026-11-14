/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Alignment.ScoreSignificance.TwoSequence

/-!
# The one-sequence tail forces `K = 0` for lattice scores

`TwoSequence.OneSequenceTail q f θ K` is the uniform one-sequence tail
`P(M_L > t) = (K + o(1)) L e^{-θ t}` (as `L → ∞`, `L e^{-θ t} → 0`, `t ≤ η L`) that the
two-sequence Gumbel limit takes as a hypothesis. The only instance constructed so far is the zero
score with `K = 0`. This file shows that no lattice score can do better: if every score `f b` lies
on a lattice `hℤ` (`h > 0`) and `θ > 0`, then `OneSequenceTail q f θ K` forces `K = 0`
(`OneSequenceTail.eq_zero_of_lattice`).

## Why

Every segment sum of lattice scores lies on `hℤ`, hence so does the maximal segment score
(`exists_int_maxSegScore_eq_mul`). So `P(M_L > t)` is constant for `t` in each open lattice cell:
at `t₁ = k h + h / 4` and `t₂ = k h + 3 h / 4` it takes the same value
(`scoreProb_lt_maxSegScore_eq_of_lattice`), while the target `K L e^{-θ t}` drops by the factor
`e^{-θ h / 2} < 1` between them. The relative error `ε` of `OneSequenceTail` must absorb that drop:
`|K| (1 - e^{-θ h / 2}) ≤ 2 ε` for every `ε > 0`, so `K = 0`. Both thresholds lie in the window of
the definition for large `L`, since `L e^{-θ (η L - 2 h)} → 0`.

## Relation to renewal theory

This is the uniform, finite-`L` form of the lattice oscillation of the renewal limit: on a lattice
the renewal theorem only gives convergence along `hℤ`, and `e^{θ t} P(M > t)` oscillates
(`MathlibExt.Probability.Renewal.LatticeConstants`, `not_tendsto_scaled_tail`; compare
`LatticeRenewalInput` in `GumbelTail`). The lattice case is the only one where the library proves
a key renewal theorem (`tendsto_exp_mul_maxTail`), so it cannot supply an instance of
`OneSequenceTail` with `K ≠ 0`. Such an instance needs a nonlattice score, hence the nonlattice key
renewal theorem for its tilted ladder-height law (the hypothesis `hKRT` of `RenewalDerivation`),
together with a tail estimate that is uniform in `L` over `t ≤ η L`. Neither is proved here.

## Main results

* `exists_int_sum_eq_mul`, `exists_int_maxSegScore_eq_mul`: segment sums and the maximal segment
  score of lattice scores are lattice values.
* `scoreProb_lt_maxSegScore_eq_of_lattice`: `P(M_L > t)` is constant on each open lattice cell.
* `OneSequenceTail.eq_zero_of_lattice`: lattice scores and `θ > 0` force `K = 0`.
* `not_oneSequenceTail_of_lattice`: equivalently, no lattice score has a one-sequence tail with
  `K ≠ 0` and `θ > 0`.

## Scope

Only the obstruction is proved; no instance with `K ≠ 0` is constructed. No hypothesis on `q` is
needed: the argument uses only that `P(M_L > t)` is the same at the two thresholds.

Reuse search (base `219463bef6`): `OneSequenceTail`, `maxSegScore`, `scoreProb`,
`exists_infix_sum_eq_maxSegScore` and `tendsto_pow_mul_exp_neg_atTop_nhds_zero` are reused. The
lattice statements of `GumbelTail` and `LatticeConstants` concern infinite-horizon or fixed-`x`
limits on a measure space, not the finite-product `scoreProb` model, so they are not applicable.

## References

* D. L. Iglehart, *Extreme values in the GI/G/1 queue*, Ann. Math. Statist. 43 (1972),
  627–635.
* S. Karlin and A. Dembo, *Limit distributions of maximal segmental score among Markov-dependent
  partial sums*, Adv. Appl. Probab. 24 (1992), 113–140.
* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. II, 2nd ed.,
  Wiley, 1971, §XI.1 (renewal theorem, lattice and nonlattice cases).
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.Alignment.ScoreSignificance.TwoSequence

open Real Finset Filter Topology
open Cslib.Bioinformatics.Alignment.ScoreSignificance.SingleSequence

/-- The sum of a list of lattice values `k h` is a lattice value. -/
theorem exists_int_sum_eq_mul {h : ℝ} {l : List ℝ} (hl : ∀ x ∈ l, ∃ k : ℤ, x = k * h) :
    ∃ k : ℤ, l.sum = k * h := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a l ih =>
    obtain ⟨j, hj⟩ := hl a List.mem_cons_self
    obtain ⟨k, hk⟩ := ih fun x hx => hl x (List.mem_cons_of_mem a hx)
    exact ⟨j + k, by rw [List.sum_cons, hj, hk]; push_cast; ring⟩

/-- The maximal segment score of a list of lattice values `k h` is a lattice value. -/
theorem exists_int_maxSegScore_eq_mul {h : ℝ} {l : List ℝ}
    (hl : ∀ x ∈ l, ∃ k : ℤ, x = k * h) : ∃ k : ℤ, maxSegScore l = k * h := by
  obtain ⟨s, hs, hsum⟩ := exists_infix_sum_eq_maxSegScore l
  rw [← hsum]
  exact exists_int_sum_eq_mul fun x hx => hl x (hs.subset hx)

/-- A threshold strictly inside the lattice cell `(k h, (k + 1) h)` is exceeded by the lattice
value `m h` exactly when `k < m`. -/
private theorem add_lt_int_mul_iff {h a : ℝ} (hh : 0 < h) (ha0 : 0 < a) (ha1 : a < h)
    (k m : ℤ) : (k : ℝ) * h + a < m * h ↔ k < m := by
  constructor
  · intro H
    have : (k : ℝ) < m := by
      by_contra hc
      push Not at hc
      nlinarith [mul_le_mul_of_nonneg_right hc hh.le]
    exact_mod_cast this
  · intro H
    have hk : ((k : ℝ) + 1) ≤ m := by exact_mod_cast Int.lt_iff_add_one_le.mp H
    nlinarith [mul_le_mul_of_nonneg_right hk hh.le]

variable {γ : Type*} [Fintype γ]

/-- For lattice scores, `P(M_L > t)` is constant for `t` in each open lattice cell
`(k h, (k + 1) h)`. -/
theorem scoreProb_lt_maxSegScore_eq_of_lattice {q f : γ → ℝ} {h : ℝ} (hh : 0 < h)
    (hlat : ∀ b, ∃ k : ℤ, f b = k * h) (L : ℕ) (k : ℤ) {a a' : ℝ} (ha0 : 0 < a) (ha1 : a < h)
    (ha0' : 0 < a') (ha1' : a' < h) :
    scoreProb q f L (fun l => k * h + a < maxSegScore l) =
      scoreProb q f L (fun l => k * h + a' < maxSegScore l) := by
  unfold scoreProb scoreExpect
  refine sum_congr rfl fun w _ => ?_
  congr 1
  obtain ⟨m, hm⟩ := exists_int_maxSegScore_eq_mul (h := h)
    (l := List.ofFn fun i => f (w i)) fun x hx => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hlat (w i)
  refine if_congr ?_ rfl rfl
  beta_reduce
  rw [hm, add_lt_int_mul_iff hh ha0 ha1, add_lt_int_mul_iff hh ha0' ha1']

/-- `L e^{-θ (η L - 2 h)} → 0` as `L → ∞`, for `θ η > 0`. -/
private theorem tendsto_natCast_mul_exp_neg {θ η h : ℝ} (hc : 0 < θ * η) :
    Tendsto (fun L : ℕ => (L : ℝ) * exp (-θ * (η * L - 2 * h))) atTop (𝓝 0) := by
  have h0 : Tendsto (fun x : ℝ => (θ * η * x) ^ 1 * exp (-(θ * η * x))) atTop (𝓝 0) :=
    (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp (tendsto_id.const_mul_atTop hc)
  have h1 := (h0.const_mul (exp (2 * θ * h) / (θ * η))).comp tendsto_natCast_atTop_atTop
  rw [mul_zero] at h1
  refine h1.congr fun L => ?_
  simp only [Function.comp_apply, pow_one]
  rw [show -θ * (η * L - 2 * h) = 2 * θ * h + -(θ * η * L) by ring, exp_add,
    div_mul_eq_mul_div, div_eq_iff hc.ne']
  ring

/-- **The one-sequence tail forces `K = 0` for lattice scores.** If every score lies on the lattice
`hℤ` with `h > 0` and `θ > 0`, then `OneSequenceTail q f θ K` implies `K = 0`: `P(M_L > t)` is
constant on each lattice cell while `K L e^{-θ t}` drops by `e^{-θ h / 2}` across half a cell. -/
theorem OneSequenceTail.eq_zero_of_lattice {q f : γ → ℝ} {θ K h : ℝ}
    (htail : OneSequenceTail q f θ K) (hθ : 0 < θ) (hh : 0 < h)
    (hlat : ∀ b, ∃ k : ℤ, f b = k * h) : K = 0 := by
  set r := exp (-θ * (h / 2)) with hr
  have hr1 : r < 1 := by
    rw [hr, ← exp_zero]; exact exp_lt_exp.2 (by nlinarith)
  have key : ∀ ε > 0, |K| * (1 - r) ≤ 2 * ε := by
    intro ε hε
    obtain ⟨L₀, δ, hδ, η, hη, H⟩ := htail ε hε
    obtain ⟨L, hLδ, hL⟩ :=
      (((tendsto_natCast_mul_exp_neg (h := h) (mul_pos hθ hη)).eventually
        (ge_mem_nhds hδ)).and (eventually_ge_atTop (max L₀ 1))).exists
    have hL₀ : L₀ ≤ L := le_of_max_le_left hL
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast le_of_max_le_right hL
    have hfl1 := (le_div_iff₀ hh).1 (Int.floor_le (η * L / h))
    have hfl2 := (div_lt_iff₀ hh).1 (Int.lt_floor_add_one (η * L / h))
    obtain ⟨k, hk1, hk2⟩ : ∃ k : ℤ, (k : ℝ) * h ≤ η * L - h ∧ η * L - 2 * h < k * h :=
      ⟨⌊η * L / h⌋ - 1, by push_cast; linarith, by push_cast; linarith⟩
    have hE : exp (-θ * (k * h + 3 * h / 4)) = exp (-θ * (k * h + h / 4)) * r := by
      rw [hr, ← exp_add]; congr 1; ring
    have hexp : exp (-θ * (k * h + h / 4)) ≤ exp (-θ * (η * L - 2 * h)) :=
      exp_le_exp.2 (by nlinarith [mul_pos hθ (show 0 < k * h + h / 4 - (η * L - 2 * h) by
        linarith)])
    have hE1 : (L : ℝ) * exp (-θ * (k * h + h / 4)) ≤ δ :=
      (mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg _)).trans hLδ
    have hE2 : (L : ℝ) * exp (-θ * (k * h + 3 * h / 4)) ≤ δ := by
      rw [hE]
      exact (mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (exp_pos _).le hr1.le)
        (Nat.cast_nonneg _)).trans hE1
    have h1 := H L hL₀ _ hE1 (by linarith)
    have h2 := H L hL₀ _ hE2 (by linarith)
    rw [scoreProb_lt_maxSegScore_eq_of_lattice hh hlat L k (a' := 3 * h / 4) (by positivity)
      (by linarith) (by positivity) (by linarith)] at h1
    rw [hE] at h2
    obtain ⟨a1, a2⟩ := abs_le.1 h1
    obtain ⟨b1, b2⟩ := abs_le.1 h2
    have hX : 0 < (L : ℝ) * exp (-θ * (k * h + h / 4)) :=
      mul_pos (by linarith) (exp_pos _)
    have hK : |K| * (1 - r) * ((L : ℝ) * exp (-θ * (k * h + h / 4))) ≤
        ε * (1 + r) * ((L : ℝ) * exp (-θ * (k * h + h / 4))) := by
      rcases abs_cases K with ⟨hK, _⟩ | ⟨hK, _⟩ <;> rw [hK] <;> linarith
    have := le_of_mul_le_mul_right hK hX
    nlinarith
  by_contra hK
  have hpos : 0 < |K| * (1 - r) := mul_pos (abs_pos.2 hK) (by linarith)
  have := key (|K| * (1 - r) / 4) (by positivity)
  linarith

/-- No lattice score has a one-sequence tail with `K ≠ 0` and `θ > 0`. -/
theorem not_oneSequenceTail_of_lattice {q f : γ → ℝ} {θ K h : ℝ} (hθ : 0 < θ) (hh : 0 < h)
    (hlat : ∀ b, ∃ k : ℤ, f b = k * h) (hK : K ≠ 0) : ¬ OneSequenceTail q f θ K :=
  fun htail => hK (htail.eq_zero_of_lattice hθ hh hlat)

end Cslib.Bioinformatics.Alignment.ScoreSignificance.TwoSequence
