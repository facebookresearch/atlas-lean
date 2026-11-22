/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Games

/-!
# Averaging games

Lemmas for games (distributions on `Bool`) obtained by first drawing a value from a distribution
`μ` and then running a game that depends on it (`μ.bind F`): the success probability is the
average of the success probabilities (`winProb_bind`), and pointwise bounds, affine identities and
identities between sums survive averaging (`winProb_bind_le`, `winProb_bind_affine`,
`apply_true_bind_add_eq`). `twoPoint m m'` is the uniform distribution on two values, and
`winProb_twoPoint_bind` averages a game over it. `eq_pure_of_not_mem_support`: a game that
never outputs `¬ b` is the constant game `b`. These are used by the security reductions of
`CSLibExt.Crypto.PublicKey.SemanticSecurity`, `GoldwasserMicali` and `HardCoreEncryption`.
-/

@[expose] public section

namespace Cslib.Crypto.Framework

/-- **Success probability of an average**: `Pr[μ.bind F = 1] = ∑ₐ μ(a) Pr[F a = 1]`. -/
theorem winProb_bind {α : Type*} (μ : PMF α) (F : α → PMF Bool) :
    winProb (μ.bind F) = ∑' a, (μ a).toReal * winProb (F a) := by
  rw [winProb, PMF.bind_apply, ENNReal.tsum_toReal_eq fun a =>
    ENNReal.mul_ne_top (μ.apply_ne_top a) ((F a).apply_ne_top true)]
  simp only [ENNReal.toReal_mul, winProb]

/-- **Averaging an affine identity**: if `Pr[F a = 1] = 1/2 + (Pr[G a = 1] - Pr[H a = 1]) / 2` for
every `a`, the same identity holds after drawing `a` from `μ`. -/
theorem winProb_bind_affine {α : Type*} (μ : PMF α) (F G H : α → PMF Bool)
    (h : ∀ a, winProb (F a) = 1 / 2 + (winProb (G a) - winProb (H a)) / 2) :
    winProb (μ.bind F) = 1 / 2 + (winProb (μ.bind G) - winProb (μ.bind H)) / 2 := by
  have hμ : Summable fun a => (μ a).toReal := ENNReal.summable_toReal (by simp [μ.tsum_coe])
  have hone : ∑' a, (μ a).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq fun a => μ.apply_ne_top a, μ.tsum_coe, ENNReal.toReal_one]
  have hs : ∀ K : α → PMF Bool, Summable fun a => (μ a).toReal * winProb (K a) := fun K =>
    hμ.of_nonneg_of_le (fun a => mul_nonneg ENNReal.toReal_nonneg (winProb_nonneg _))
      (fun a => mul_le_of_le_one_right ENNReal.toReal_nonneg (winProb_le_one _))
  rw [winProb_bind, winProb_bind, winProb_bind]
  simp_rw [h]
  have : ∀ a, (μ a).toReal * (1 / 2 + (winProb (G a) - winProb (H a)) / 2) =
      (1 / 2) * (μ a).toReal + (1 / 2) * ((μ a).toReal * winProb (G a)) -
        (1 / 2) * ((μ a).toReal * winProb (H a)) := fun a => by ring
  simp_rw [this]
  rw [((hμ.mul_left _).add ((hs G).mul_left _)).tsum_sub ((hs H).mul_left _),
    (hμ.mul_left _).tsum_add ((hs G).mul_left _), tsum_mul_left, tsum_mul_left, tsum_mul_left,
    hone]
  ring

/-- **Averaging a pointwise identity between sums of success probabilities**: if
`Pr[f a = 1] + Pr[g a = 1] = Pr[f' a = 1] + Pr[g' a = 1]` for every `a`, the same identity holds
after drawing `a` from `μ` (linearity of `bind`). -/
theorem apply_true_bind_add_eq {α : Type*} (μ : PMF α) (f g f' g' : α → PMF Bool)
    (h : ∀ a, f a true + g a true = f' a true + g' a true) :
    (μ.bind f) true + (μ.bind g) true = (μ.bind f') true + (μ.bind g') true := by
  simp only [PMF.bind_apply, ← ENNReal.tsum_add, ← mul_add, h]

/-- **Averaging a pointwise bound.** If the success probabilities of two families of games
differ by at most `ε` on the support of `X`, so do their averages over `X`. -/
theorem winProb_bind_le {α : Type*} (X : PMF α) (F G : α → PMF Bool) {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ x ∈ X.support, winProb (F x) ≤ winProb (G x) + ε) :
    winProb (X.bind F) ≤ winProb (X.bind G) + ε := by
  have hle : (X.bind F) true ≤ (X.bind G) true + ENNReal.ofReal ε := by
    rw [PMF.bind_apply, PMF.bind_apply]
    calc ∑' x, X x * F x true ≤ ∑' x, (X x * G x true + X x * ENNReal.ofReal ε) := by
          refine ENNReal.tsum_le_tsum fun x => ?_
          rw [← mul_add]
          by_cases hx : x ∈ X.support
          · gcongr
            have := h x hx
            rw [winProb, winProb] at this
            rw [← ENNReal.ofReal_toReal ((F x).apply_ne_top true),
              ← ENNReal.ofReal_toReal ((G x).apply_ne_top true),
              ← ENNReal.ofReal_add ENNReal.toReal_nonneg hε]
            exact ENNReal.ofReal_le_ofReal this
          · rw [PMF.mem_support_iff, not_not] at hx
            simp [hx]
      _ = ∑' x, X x * G x true + ENNReal.ofReal ε := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, X.tsum_coe, one_mul]
  have := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨(X.bind G).apply_ne_top _, ENNReal.ofReal_ne_top⟩) hle
  rwa [ENNReal.toReal_add ((X.bind G).apply_ne_top _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hε] at this

/-- **The two-point distribution**, uniform on the two values `m` and `m'` (a fair coin picks
one). -/
noncomputable def twoPoint {M : Type*} (m m' : M) : PMF M := fairCoin.map (pick (m, m'))

/-- **Averaging over the two-point distribution**: the success probability is the mean of the
success probabilities on `m` and on `m'`. -/
theorem winProb_twoPoint_bind {M : Type*} (m m' : M) (F : M → PMF Bool) :
    winProb ((twoPoint m m').bind F) = (winProb (F m) + winProb (F m')) / 2 := by
  rw [twoPoint, PMF.bind_map, winProb, PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
  simp only [fairCoin, Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.card_bool,
    Function.comp, pick, ite_true, Bool.false_eq_true, ite_false]
  rw [ENNReal.toReal_add (by simp [ENNReal.mul_eq_top, PMF.apply_ne_top])
      (by simp [ENNReal.mul_eq_top, PMF.apply_ne_top]), ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp only [Nat.cast_ofNat, ENNReal.toReal_inv, ENNReal.toReal_ofNat, winProb]
  ring

/-- **A game that never outputs `¬ b` always outputs `b`.** -/
theorem eq_pure_of_not_mem_support {G : PMF Bool} {b : Bool} (h : (!b) ∉ G.support) :
    G = PMF.pure b := by
  have h0 : G (!b) = 0 := by rwa [PMF.mem_support_iff, not_not] at h
  have hsum := apply_true_add_apply_false G
  ext x
  cases b <;> cases x <;> simp_all [PMF.pure_apply]

end Cslib.Crypto.Framework
