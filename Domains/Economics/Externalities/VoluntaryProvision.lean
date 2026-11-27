/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Economics.Externalities.PublicGoodDemand
public import MathlibExt.GameTheory.StrategicGame
public import Mathlib.Basic.NNReal.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Voluntary contributions and a correcting subsidy

Consumers choose nonnegative contributions; their private numeraire can take any real value.
After substituting the budget equation, utility is common benefit less the contributor's
own variable payment and a lump-sum charge (which can include a fixed endowment with a
minus sign). The charge receives the profile with the player's own contribution set to zero:
it can depend on every rival, but not on a unilateral change by the payer.
-/

@[expose] public section

open Set MathlibExt.GameTheory
open scoped NNReal

namespace MathlibExt.Economics.PublicGood

/-- The public-good total supplied by `n` consumers making nonnegative real contributions. -/
def provision {n : ℕ} (g : Fin n → ℝ≥0) : ℝ := ∑ i, (g i : ℝ)

/-- Voluntary provision at effective unit price `p` with common benefit `v` and real lump-sum
charges `tax`. Player `i` receives `v` of aggregate provision less `p * g i` and `tax i`
of the rivals' profile (represented by zero in slot `i`). Contributions are not capped by
private wealth: the transferable numeraire is unrestricted. -/
noncomputable def contributionGame {n : ℕ} (v : ℝ → ℝ) (p : ℝ)
    (tax : Fin n → (Fin n → ℝ≥0) → ℝ) : StrategicGame (Fin n) (fun _ => ℝ≥0) where
  payoff i g := v (provision g) - p * g i - tax i (Function.update g i 0)
  strategy_nonempty _ := ⟨0⟩

variable {n : ℕ} {v d : ℝ → ℝ} {p : ℝ} {tax : Fin n → (Fin n → ℝ≥0) → ℝ}

private theorem provision_nonneg (g : Fin n → ℝ≥0) : 0 ≤ provision g :=
  Finset.sum_nonneg fun i _ => (g i).coe_nonneg

private theorem provision_update (g : Fin n → ℝ≥0) (i : Fin n) (t : ℝ≥0) :
    provision (Function.update g i t) = provision g - g i + t := by
  classical
  unfold provision
  have h : (fun j => ((Function.update g i t j : ℝ≥0) : ℝ)) =
      Function.update (fun j => (g j : ℝ)) i (t : ℝ) := by
    ext j
    by_cases he : j = i <;> simp [he]
  rw [h, Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  have hs := Finset.sum_erase_add Finset.univ (fun j => (g j : ℝ)) (Finset.mem_univ i)
  linarith

/-- At any real unit price `p` and for any common benefit `v`, a nonnegative contribution
profile is Nash exactly when `v x - p * x` is maximized at its total on each player's
reachable interval: all totals `x` at least as large as the rivals' provision.
Lump-sum charges can be arbitrary functions of the rivals' contributions. -/
theorem contributionGame_isNash_iff {g : Fin n → ℝ≥0} :
    (contributionGame v p tax).IsNash g ↔ ∀ i, IsMaxOn (fun x => v x - p * x)
      (Ici (provision g - g i)) (provision g) := by
  rw [StrategicGame.isNash_iff_update_le]
  have dev (i : Fin n) (t : ℝ≥0) :
      (contributionGame v p tax).payoff i (Function.update g i t) ≤
        (contributionGame v p tax).payoff i g ↔
      v (provision g - g i + t) - p * (provision g - g i + t) ≤
        v (provision g) - p * provision g := by
    simp only [contributionGame, provision_update, Function.update_self, Function.update_idem]
    constructor <;> intro h <;> linarith
  constructor
  · intro h i x hx
    let t : ℝ≥0 := ⟨x - (provision g - g i), sub_nonneg.mpr hx⟩
    have ht : provision g - g i + (t : ℝ) = x := by change _ + (x - _) = _; ring
    change v x - p * x ≤ v (provision g) - p * provision g
    simpa only [ht] using (dev i t).mp (h i t)
  · intro h i t
    exact (dev i t).mpr (h i (show provision g - g i + t ∈ Ici (provision g - g i) by simp))

private theorem demand_deriv {G : ℝ} (h : CommonBenefit v d) (hG : 0 < G) (p : ℝ) :
    HasDerivAt (fun x => v x - p * x) (d G - p) G := by
  have hv := (h.marginal G hG.le).hasDerivAt (Ici_mem_nhds hG)
  simpa using! hv.sub ((hasDerivAt_id' G).const_mul p)

/-- Given at least one consumer and a positive price below the right marginal benefit at
zero, the voluntary-contribution game is in Nash equilibrium exactly when marginal benefit at
the total equals the price. The common benefit is increasing, strictly concave and
differentiable on nonnegative totals with vanishing marginal benefit at infinity; the taxes
are arbitrary functions of rivals' contributions. No contributor faces a wealth constraint. -/
theorem isNash_iff_marginal_eq (hn : 0 < n) (h : CommonBenefit v d) (hp : 0 < p)
    (h0 : p < d 0) (g : Fin n → ℝ≥0) :
    (contributionGame v p tax).IsNash g ↔ d (provision g) = p := by
  obtain ⟨Q, hQ, hprice, hpeak⟩ := h.exists_peak hp h0
  have hG := provision_nonneg g
  rw [contributionGame_isNash_iff]
  constructor
  · intro hmax
    by_cases hactive : ∃ i, 0 < (g i : ℝ)
    · obtain ⟨i, hi⟩ := hactive
      have hGi : (g i : ℝ) ≤ provision g := Finset.single_le_sum
        (fun j _ => (g j).coe_nonneg) (Finset.mem_univ i)
      have hm := (hmax i).isLocalMaxOn.isLocalMax (Ici_mem_nhds (by linarith :
        provision g - g i < provision g))
      exact sub_eq_zero.mp (hm.hasDerivAt_eq_zero (demand_deriv h (hi.trans_le hGi) p))
    · have hz (i : Fin n) : (g i : ℝ) = 0 :=
        le_antisymm (le_of_not_gt fun hi => hactive ⟨i, hi⟩) (g i).coe_nonneg
      have hG0 : provision g = 0 := by simp [provision, hz]
      have him := hmax ⟨0, hn⟩
      simp only [hG0, hz, sub_zero] at him
      exact False.elim ((not_lt_of_ge (him hQ.le)) (hpeak 0 le_rfl (ne_of_lt hQ)))
  · intro hprice' i x hx
    have hEQ := h.strictAntiOn_marginal.injOn hG hQ.le (hprice'.trans hprice.symm)
    have hother : 0 ≤ provision g - g i := sub_nonneg.mpr (Finset.single_le_sum
      (fun j _ => (g j).coe_nonneg) (Finset.mem_univ i))
    have hx0 : 0 ≤ x := hother.trans hx
    rw [hEQ]
    rcases eq_or_ne x Q with rfl | hne
    · exact le_rfl
    · exact (hpeak x hx0 hne).le

private theorem exists_profile {G : ℝ} (hn : 0 < n) (hG : 0 ≤ G) :
    ∃ g : Fin n → ℝ≥0, provision g = G := by
  let i : Fin n := ⟨0, hn⟩
  let t : ℝ≥0 := ⟨G, hG⟩
  refine ⟨Function.update (0 : Fin n → ℝ≥0) i t, ?_⟩
  rw [provision_update]
  simp [provision, t]
  rfl

variable {c : ℝ}

/-- The matching subsidy amount per unit is `c * (1 - 1 / n)`. For `n ≥ 1` consumers and
unit cost `c ≥ 0`, every contributor faces the same net marginal price `c / n`. The subsidy
is positive when `n ≥ 2` and `c > 0`; it need not equalize consumers' total payments. -/
noncomputable def matchingRate (n : ℕ) (c : ℝ) : ℝ := c * (1 - 1 / (n : ℝ))

/-- Each consumer pays the fixed amount `rate * Q / n`, independently of all contributions.
For `n > 0` these charges sum to `rate * Q`. This covers actual subsidy spending when the
total equals the target `Q`, but not in general at other totals. -/
noncomputable def fixedCharge {n : ℕ} (rate Q : ℝ) (_i : Fin n) (_g : Fin n → ℝ≥0) : ℝ :=
  rate * Q / n

/-- With at least one consumer and a strictly positive subsidy rate, the equal fixed charges
calibrated to `Q` exactly cover actual subsidy spending if and only if provision equals `Q`.
This is budget balance at the target, not budget balance after every possible deviation. -/
theorem fixedCharge_balances_iff (hn : 0 < n) {rate Q : ℝ} (hr : 0 < rate) (g : Fin n → ℝ≥0) :
    (∑ i, fixedCharge rate Q i g) = rate * provision g ↔ provision g = Q := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [fixedCharge, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  constructor <;> intro h <;> nlinarith

/-- **Private provision and a matching subsidy.** Let at least two consumers share an
increasing, differentiable, strictly concave public-good benefit on nonnegative totals.
Suppose marginal benefit tends to zero and its right-hand value at zero exceeds positive
unit cost `c`. There are positive private and efficient totals `N < E`: their marginal
benefits are `c` and `c / n`, respectively. Among feasible totals, only `E` satisfies the
Samuelson equation and only `E` maximizes aggregate surplus. At price `c` the Nash profiles
are precisely the profiles with total `N`. Reducing the price by `c * (1 - 1/n)` implements
`E`: for any charges depending only on rivals, the Nash profiles are precisely those with
total `E`. Both games have equilibria. Equal fixed charges calibrated to `E` balance subsidy
spending there, and only there. Numeraire holdings are unrestricted. -/
theorem privateProvision_and_matchingSubsidy (hn : 2 ≤ n) (h : CommonBenefit v d)
    (hc : 0 < c) (h0 : c < d 0) :
    ∃ N E : ℝ, 0 < N ∧ N < E ∧ d N = c ∧ d E = c / n ∧
      (∀ x ∈ Ici (0 : ℝ), (n : ℝ) * d x = c ↔ x = E) ∧
      (∀ x ∈ Ici (0 : ℝ), IsMaxOn (surplus (fun _ : Fin n => v) (c * ·)) (Ici 0) x ↔ x = E) ∧
      (∃ g, (contributionGame (n := n) v c 0).IsNash g) ∧
      (∀ g, (contributionGame (n := n) v c 0).IsNash g ↔ provision g = N) ∧
      c - matchingRate n c = c / n ∧
      (∀ tax : Fin n → (Fin n → ℝ≥0) → ℝ,
        (∃ g, (contributionGame v (c - matchingRate n c) tax).IsNash g) ∧
        ∀ g, (contributionGame v (c - matchingRate n c) tax).IsNash g ↔ provision g = E) ∧
      ∀ g : Fin n → ℝ≥0, (∑ i, fixedCharge (matchingRate n c) E i g) =
        matchingRate n c * provision g ↔ provision g = E := by
  have hn0 : 0 < n := by omega
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hn' : 0 < (n : ℝ) := by positivity
  have hp : 0 < c / n := div_pos hc hn'
  have hpc : c / n < c := div_lt_self hc hn1
  obtain ⟨N, hN, hdN, _⟩ := h.exists_peak hc h0
  obtain ⟨E, hE, hdE, hsam, hopt⟩ := h.exists_efficientTotal hn0 hc (hpc.trans h0)
  have hNE : N < E := by
    by_contra! hle
    have := h.strictAntiOn_marginal.antitoneOn hE.le hN.le hle
    linarith
  have hrate : c - matchingRate n c = c / n := by unfold matchingRate; ring
  have heq (p G : ℝ) (hp' : 0 < p) (hinit : p < d 0) (hG : 0 < G) (hprice : d G = p)
      (tax : Fin n → (Fin n → ℝ≥0) → ℝ) (g : Fin n → ℝ≥0) :
      (contributionGame v p tax).IsNash g ↔ provision g = G := by
    rw [isNash_iff_marginal_eq hn0 h hp' hinit, ← hprice]
    exact ⟨h.strictAntiOn_marginal.injOn (provision_nonneg g) hG.le, congrArg d⟩
  obtain ⟨gN, hgN⟩ := exists_profile hn0 hN.le
  obtain ⟨gE, hgE⟩ := exists_profile hn0 hE.le
  refine ⟨N, E, hN, hNE, hdN, hdE, hsam, hopt, ⟨gN, (heq _ _ hc h0 hN hdN 0 gN).mpr hgN⟩,
    heq _ _ hc h0 hN hdN 0, hrate, ?_, ?_⟩
  · intro tax
    rw [hrate]
    exact ⟨⟨gE, (heq _ _ hp (hpc.trans h0) hE hdE tax gE).mpr hgE⟩,
      heq _ _ hp (hpc.trans h0) hE hdE tax⟩
  · exact fixedCharge_balances_iff hn0 (by linarith : 0 < matchingRate n c)

end MathlibExt.Economics.PublicGood
