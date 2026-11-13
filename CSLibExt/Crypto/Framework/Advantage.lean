/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Probability.PMF
public import Cslib.Probability.StatisticalDistance

/-!
# Games and advantages

A **game** (security experiment) is a distribution `PMF Bool` on its outcome: `true` means the
experiment outputs `1` (the adversary wins, or the distinguisher outputs `1`). All security
notions of the framework are phrased with one vocabulary:

* `winProb G = Pr[G = 1]`, as a real number.
* `advantage G₀ G₁ = |Pr[G₀ = 1] - Pr[G₁ = 1]|`: the **distinguishing** shape, e.g. the PRF
  advantage `|Pr[D^{F_k} = 1] - Pr[D^f = 1]|` (Katz and Lindell, Definition 3.25).
* `guessAdvantage G = |Pr[G = 1] - 1/2|`: the **guessing** shape of the indistinguishability
  experiments `PrivK` and `PubK` (Katz and Lindell, Definitions 3.8, 3.22, 11.2).
  `guessAdvantage_eq_advantage_fairCoin`: it is the distinguishing advantage against a fair coin.
* `bitGame G` samples a uniform bit `b`, runs the left-or-right experiment `G b` (which outputs the
  adversary's guess `b'`) and outputs `b' == b`. `guessAdvantage_bitGame`: its guessing advantage
  is half the distinguishing advantage between `G true` and `G false`, so the two shapes agree up
  to the usual factor `2`.

Reusable lemmas:
* `advantage_triangle` (triangle inequality), `advantage_le_sum` and `advantage_le_mul`
  (the hybrid argument, which Katz and Lindell use throughout Chapters 3 and 7;
  Shoup),
  `advantage_hybrid_uniform` (the **hybrid step**: a distinguisher that picks the hybrid index
  uniformly has exactly `1/n` of the end-to-end advantage);
* `advantage_le_winProb_of_eq_of_not_bad` (the **difference lemma**, "identical until bad":
  Shoup, Lemma 1; Boneh and Shoup, Theorem 4.7);
* `advantage_eq_dist`, `advantage_map_le_dist` (statistical distance bounds every
  distinguishing advantage; Boneh and Shoup, Theorem 3.13).

The existing games in `CSLibExt/Crypto` (`Cslib.Crypto.PublicKey.ElGamal.eavAdvantage`,
`Cslib.Crypto.PRF.prfAdvantage`, `Cslib.Crypto.Signatures.Lamport.forgeGame`) are literally of
these shapes (`|(G true).toReal - 1/2|`, `|(G₀ true).toReal - (G₁ true).toReal|`,
`(G true).toReal`); migrating them onto `winProb`/`advantage` is a Wave-2 step.

## References

* J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Sections 3.2, 3.4, 3.5 and Chapter 7.
* V. Shoup, *Sequences of games: a tool for taming complexity in security proofs*, IACR ePrint
  2004/332.
* D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6.
-/

@[expose] public section

namespace Cslib.Crypto.Framework

open Finset
open scoped Cslib.Probability.PMF

/-! ### Success probability and the two advantage shapes -/

/-- The probability `Pr[G = 1]` that a game outputs `1`, as a real number. -/
noncomputable def winProb (G : PMF Bool) : ℝ := (G true).toReal

/-- The distinguishing advantage `|Pr[G₀ = 1] - Pr[G₁ = 1]|` (the shape of the PRF advantage of
Katz and Lindell, Definition 3.25, and of the DDH advantage of their Section 8.3.2). -/
noncomputable def advantage (G₀ G₁ : PMF Bool) : ℝ := |winProb G₀ - winProb G₁|

/-- The guessing advantage `|Pr[G = 1] - 1/2|` of an indistinguishability experiment (Katz and
Lindell, Definitions 3.8, 3.22 and 11.2 in the "`≤ 1/2 + negl`" form). -/
noncomputable def guessAdvantage (G : PMF Bool) : ℝ := |winProb G - 1 / 2|

/-- A uniformly random bit. -/
noncomputable def fairCoin : PMF Bool := Cslib.Probability.PMF.uniformOfFintype Bool

/-- The left-or-right game: sample `b` uniformly, run the experiment `G b`, which outputs the
adversary's guess, and output whether the guess is `b` (the shape of Katz and Lindell's
`PrivK` and `PubK` experiments). -/
noncomputable def bitGame (G : Bool → PMF Bool) : PMF Bool :=
  fairCoin.bind fun b => (G b).map (· == b)

theorem winProb_nonneg (G : PMF Bool) : 0 ≤ winProb G := ENNReal.toReal_nonneg

/-- The two outcomes of a game have probabilities summing to `1`. -/
theorem apply_true_add_apply_false (G : PMF Bool) : G true + G false = 1 := by
  simpa [tsum_fintype, Fintype.sum_bool] using G.tsum_coe

/-- `Pr[G = 0] = 1 - Pr[G = 1]`. -/
theorem toReal_apply_false (G : PMF Bool) : (G false).toReal = 1 - winProb G := by
  have h := congrArg ENNReal.toReal (apply_true_add_apply_false G)
  rw [ENNReal.toReal_add (G.apply_ne_top _) (G.apply_ne_top _), ENNReal.toReal_one] at h
  rw [winProb]
  linarith

theorem winProb_le_one (G : PMF Bool) : winProb G ≤ 1 := by
  have := toReal_apply_false G
  have : 0 ≤ (G false).toReal := ENNReal.toReal_nonneg
  linarith

@[simp] theorem winProb_pure (b : Bool) : winProb (PMF.pure b) = if b then 1 else 0 := by
  cases b <;> simp [winProb, PMF.pure_apply]

/-- A fair coin outputs `1` with probability `1/2`. -/
@[simp] theorem winProb_fairCoin : winProb fairCoin = 1 / 2 := by
  simp [winProb, fairCoin, Cslib.Probability.PMF.uniformOfFintype_apply]

/-- The success probability of a deterministic test applied to a uniform sample is the fraction of
samples passing it. -/
theorem winProb_map_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω] (g : Ω → Bool) :
    winProb ((Cslib.Probability.PMF.uniformOfFintype Ω).map g) =
      (univ.filter fun ω => g ω = true).card / Fintype.card Ω := by
  classical
  rw [winProb, PMF.map_apply, tsum_fintype,
    ENNReal.toReal_sum fun ω _ => by split_ifs <;> simp, div_eq_mul_inv, ← sum_boole, sum_mul]
  refine sum_congr rfl fun ω _ => ?_
  by_cases hg : g ω = true <;> simp [hg, eq_comm (a := true)]

theorem advantage_nonneg (G₀ G₁ : PMF Bool) : 0 ≤ advantage G₀ G₁ := abs_nonneg _

theorem advantage_comm (G₀ G₁ : PMF Bool) : advantage G₀ G₁ = advantage G₁ G₀ := abs_sub_comm _ _

@[simp] theorem advantage_self (G : PMF Bool) : advantage G G = 0 := by simp [advantage]

/-- An advantage is at most `1`. -/
theorem advantage_le_one (G₀ G₁ : PMF Bool) : advantage G₀ G₁ ≤ 1 := by
  have := winProb_nonneg G₀; have := winProb_nonneg G₁
  have := winProb_le_one G₀; have := winProb_le_one G₁
  rw [advantage, abs_le]
  constructor <;> linarith

/-- The guessing advantage is the distinguishing advantage against a fair coin. -/
theorem guessAdvantage_eq_advantage_fairCoin (G : PMF Bool) :
    guessAdvantage G = advantage G fairCoin := by
  rw [guessAdvantage, advantage, winProb_fairCoin]

/-- A guessing advantage is at most `1/2`. -/
theorem guessAdvantage_le_half (G : PMF Bool) : guessAdvantage G ≤ 1 / 2 := by
  have := winProb_nonneg G; have := winProb_le_one G
  rw [guessAdvantage, abs_le]
  constructor <;> linarith

/-- `Pr[bitGame G = 1] = (Pr[G true = 1] + Pr[G false = 0]) / 2`. -/
theorem winProb_bitGame (G : Bool → PMF Bool) :
    winProb (bitGame G) = (winProb (G true) + (1 - winProb (G false))) / 2 := by
  have hmap : ∀ b, ((G b).map (· == b)) true = G b b := by
    intro b
    rw [PMF.map_apply, tsum_fintype, Fintype.sum_bool]
    cases b <;> simp
  rw [winProb, bitGame, PMF.bind_apply, tsum_fintype, Fintype.sum_bool, hmap, hmap]
  simp only [fairCoin, Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_bool]
  rw [ENNReal.toReal_add (by simp [ENNReal.mul_eq_top, PMF.apply_ne_top])
      (by simp [ENNReal.mul_eq_top, PMF.apply_ne_top]),
    ENNReal.toReal_mul, ENNReal.toReal_mul, toReal_apply_false, winProb]
  simp only [Nat.cast_ofNat, ENNReal.toReal_inv, ENNReal.toReal_ofNat, winProb]
  ring

/-- **Guessing versus distinguishing**: the guessing advantage of the left-or-right game is half
the distinguishing advantage between its two worlds. -/
theorem guessAdvantage_bitGame (G : Bool → PMF Bool) :
    guessAdvantage (bitGame G) = advantage (G true) (G false) / 2 := by
  rw [guessAdvantage, winProb_bitGame, advantage,
    show (winProb (G true) + (1 - winProb (G false))) / 2 - 1 / 2 =
      (winProb (G true) - winProb (G false)) / 2 by ring,
    abs_div, abs_two]

/-! ### Hybrid arguments -/

/-- **Triangle inequality** for advantages. -/
theorem advantage_triangle (G₀ G₁ G₂ : PMF Bool) :
    advantage G₀ G₂ ≤ advantage G₀ G₁ + advantage G₁ G₂ :=
  abs_sub_le _ _ _

/-- **Hybrid argument**: the end-to-end advantage over a sequence of hybrids is at most the sum
of the advantages between consecutive hybrids. -/
theorem advantage_le_sum (H : ℕ → PMF Bool) :
    ∀ n : ℕ, advantage (H 0) (H n) ≤ ∑ i ∈ range n, advantage (H i) (H (i + 1))
  | 0 => by simp
  | n + 1 => by
    rw [sum_range_succ]
    have := advantage_le_sum H n
    have := advantage_triangle (H 0) (H n) (H (n + 1))
    linarith

/-- **Hybrid argument, uniform form**: if consecutive hybrids are `ε`-close, the end points are
`n ε`-close. -/
theorem advantage_le_mul (H : ℕ → PMF Bool) (n : ℕ) {ε : ℝ}
    (h : ∀ i < n, advantage (H i) (H (i + 1)) ≤ ε) : advantage (H 0) (H n) ≤ n * ε := by
  refine (advantage_le_sum H n).trans ?_
  have := sum_le_sum fun i (hi : i ∈ range n) => h i (mem_range.mp hi)
  simpa using this

/-- Choosing the hybrid index uniformly: `Pr[mix = 1]` is the average of the `Pr[H i = 1]`. -/
private theorem winProb_uniform_bind {n : ℕ} [NeZero n] (H : Fin n → PMF Bool) :
    winProb ((Cslib.Probability.PMF.uniformOfFintype (Fin n)).bind H) =
      (∑ i, winProb (H i)) / n := by
  rw [winProb, PMF.bind_apply, tsum_fintype,
    ENNReal.toReal_sum fun i _ => ENNReal.mul_ne_top (by simp [NeZero.ne n]) (PMF.apply_ne_top _ _)]
  simp only [Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, winProb]
  rw [← mul_sum, inv_mul_eq_div]

/-- **The hybrid step** (the averaging step of Katz and Lindell's hybrid arguments, Chapters 3
and 7): a distinguisher that picks the hybrid index `i` uniformly
among `n` and is then given hybrid `i` or hybrid `i + 1` has exactly `1/n` of the end-to-end
advantage. -/
theorem advantage_hybrid_uniform (H : ℕ → PMF Bool) {n : ℕ} [NeZero n] :
    advantage ((Cslib.Probability.PMF.uniformOfFintype (Fin n)).bind fun i => H i)
        ((Cslib.Probability.PMF.uniformOfFintype (Fin n)).bind fun i => H (i + 1)) =
      advantage (H 0) (H n) / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [advantage, winProb_uniform_bind, winProb_uniform_bind, ← sub_div,
    Fin.sum_univ_eq_sum_range (fun i => winProb (H i)),
    Fin.sum_univ_eq_sum_range (fun i => winProb (H (i + 1))), ← sum_sub_distrib,
    sum_range_sub' (fun i => winProb (H i)), abs_div, abs_of_pos hn, advantage]

/-! ### Identical until bad -/

/-- **The difference lemma** ("identical until bad"; Shoup, Lemma 1; Boneh and Shoup,
Theorem 4.7). Two games `μ.map A` and `μ.map B` coupled on one probability space `μ`, whose
outcomes agree whenever the bad event `F` does not occur, have advantage at most `Pr[F]`. -/
theorem advantage_le_winProb_of_eq_of_not_bad {Ω : Type*} (μ : PMF Ω) (A B F : Ω → Bool)
    (h : ∀ ω, F ω = false → A ω = B ω) :
    advantage (μ.map A) (μ.map B) ≤ winProb (μ.map F) := by
  -- `Pr[A] ≤ Pr[B] + Pr[F]` in `ENNReal`, for any two outcome maps agreeing off `F`
  have key : ∀ A B : Ω → Bool, (∀ ω, F ω = false → A ω = B ω) →
      (μ.map A) true ≤ (μ.map B) true + (μ.map F) true := by
    intro A B h
    simp only [PMF.map_apply]
    rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun ω => ?_
    cases hF : F ω
    · rw [h ω hF]; simp
    · simp only [ite_true]
      exact le_add_left (by split_ifs <;> simp)
  have hle : ∀ A B : Ω → Bool, (∀ ω, F ω = false → A ω = B ω) →
      winProb (μ.map A) ≤ winProb (μ.map B) + winProb (μ.map F) := by
    intro A B h
    rw [winProb, winProb, winProb, ← ENNReal.toReal_add (PMF.apply_ne_top _ _)
      (PMF.apply_ne_top _ _)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _,
      PMF.apply_ne_top _ _⟩) (key A B h)
  have h1 := hle A B h
  have h2 := hle B A fun ω hω => (h ω hω).symm
  rw [advantage, abs_sub_le_iff]
  constructor <;> linarith

/-! ### Statistical distance -/

/-- On `Bool`, the statistical distance (CSLib's `dist` on `PMF`) is exactly the distinguishing
advantage. -/
theorem advantage_eq_dist (G₀ G₁ : PMF Bool) : advantage G₀ G₁ = dist G₀ G₁ := by
  rw [Cslib.Probability.PMF.dist_eq, Fintype.sum_bool, toReal_apply_false, toReal_apply_false,
    advantage, show 1 - winProb G₀ - (1 - winProb G₁) = -(winProb G₀ - winProb G₁) by ring,
    abs_neg, winProb, winProb]
  ring

/-- **Statistical distance bounds advantage**: any distinguisher `D` applied to samples from `p`
and `q` has advantage at most the statistical distance between `p` and `q`. -/
theorem advantage_map_le_dist {Ω : Type*} [Fintype Ω] (p q : PMF Ω) (D : Ω → Bool) :
    advantage (p.map D) (q.map D) ≤ dist p q := by
  rw [advantage_eq_dist]
  exact Cslib.Probability.PMF.dist_map_le p q D

end Cslib.Crypto.Framework
