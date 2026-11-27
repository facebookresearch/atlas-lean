/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Fourier.BooleanCubeNoiseStability
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Counterexamples to the Majority Is Least Stable conjecture

The theorem `majorityIsLeastStableForSomeOddAtLeastFive_refuted` refutes the conjecture
in each odd dimension at least five. We use the small-noise criterion of Biswas and Sarkar:
two functions with equal means are ordered near zero by their level-one Fourier weights
when those weights differ.

For `n = 2k + 1`, choose a vertex `p` whose coordinates sum to one. The weights
`n - 1 - pᵢ` give a linear threshold function that reverses majority at just `p` and
its antipode. Its level-one Fourier weight is strictly smaller than majority's exactly
when the central binomial coefficient `(2k choose k)` exceeds `n`, which holds for `k ≥ 2`.

## Record carried over from the retired wanted module

From `WantedExt/Combinatorics/MajorityIsLeastStableAMR127Problem0009Wanted.lean`:

Source: R. O'Donnell, Open problems in analysis of Boolean functions, arXiv:1204.6447 (2012),
'Majority Is Least Stable Conjecture' (Benjamini, Kalai, Schramm). UnsolvedMath record UM-00800440
(`AMR-127-0009`), dataset ulamai/UnsolvedMath v1.8.0.

The cube `{-1, 1}ⁿ` and Fourier coefficients are MathlibExt's `BooleanCube` (`true` is `1`,
`boolFourierCoeff n f S = E_x[f(x) χ_S(x)]`). A linear threshold function is `x ↦ sgn(w₀ + Σᵢ wᵢ
xᵢ)` with `sgn z = 1` for `z ≥ 0` and `-1` for `z < 0`, the convention of Biswas and Sarkar (raising
`w₀` slightly gives the same class with nonzero arguments). The noise stability is given by its
Fourier formula `Stab_ρ[f] = Σ_S ρ^{|S|} f̂(S)²` (O'Donnell, Analysis of Boolean Functions, Theorem
2.49; Biswas–Sarkar, §2). Biswas and Sarkar prove the conjecture for `n = 1, 3` and refute it for
every odd `n ≥ 5`, so the target is stated for some odd `n ≥ 5` and refuted, which is stronger than
refuting the conjecture as posed; the cases `n = 1, 3` are not formalized. The list's remarks after
the conjecture (a weaker noise-sensitivity version, the `ρ → 0` consequence) are related questions,
not part of the conjecture.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.MajorityIsLeastStableAMR127Problem0009Wanted

open BooleanCube

/-- **Linear threshold function.** A function $f : \{-1, 1\}^n \to \mathbb{R}$ is a linear
threshold function if there are reals $w_0, w_1, \dots, w_n$ such that for every
$x \in \{-1, 1\}^n$ we have $f(x) = \operatorname{sgn}(w_0 + w_1 x_1 + \dots + w_n x_n)$, where
$x_i \in \{-1, 1\}$ is the $i$-th coordinate of $x$, $\operatorname{sgn} z = 1$ for $z \ge 0$ and
$\operatorname{sgn} z = -1$ for $z < 0$. -/
def IsLinearThresholdFunction {n : ℕ} (f : BoolCube n → ℝ) : Prop :=
  ∃ (w₀ : ℝ) (w : Fin n → ℝ), ∀ x : BoolCube n,
    f x = if 0 ≤ w₀ + ∑ i, w i * cubeVal (x i) then 1 else -1

/-- **Majority function.** For $n \in \mathbb{N}$, the majority function
$\mathrm{Maj}_n : \{-1, 1\}^n \to \mathbb{R}$ is given by $\mathrm{Maj}_n(x) = 1$ if
$x_1 + \dots + x_n \ge 0$ and $\mathrm{Maj}_n(x) = -1$ otherwise, where $x_i \in \{-1, 1\}$ is the
$i$-th coordinate of $x$. -/
noncomputable def majority (n : ℕ) (x : BoolCube n) : ℝ :=
  if 0 ≤ ∑ i, cubeVal (x i) then 1 else -1

/-- **Noise stability.** For a real number $\rho$ and a function $f : \{-1, 1\}^n \to \mathbb{R}$,
the noise stability of $f$ at $\rho$ is
$\mathrm{Stab}_\rho[f] = \sum_{S \subseteq \{1, \dots, n\}} \rho^{|S|} \hat f(S)^2$, where
$\hat f(S)$ is the Fourier coefficient of $f$ at $S$.

For $-1 \le \rho \le 1$ this is the Fourier expansion of $\mathbb{E}[f(x) f(y)]$ for uniform $x$
and a $\rho$-correlated copy $y$ of $x$. -/
noncomputable def noiseStability {n : ℕ} (ρ : ℝ) (f : BoolCube n → ℝ) : ℝ :=
  ∑ S : Finset (Fin n), ρ ^ S.card * boolFourierCoeff n f S ^ 2

/-- **The two noise-stability definitions agree.** For every `f : BoolCube n → ℝ` and real `ρ`,
the Fourier-sum definition `noiseStability ρ f` equals MathlibExt's
`BooleanCube.boolNoiseStab ρ f = 𝔼[f · T_ρ f]` (R. O'Donnell, *Analysis of Boolean Functions*,
2014, Theorem 2.49). -/
theorem noiseStability_eq_boolNoiseStab {n : ℕ} (ρ : ℝ) (f : BoolCube n → ℝ) :
    noiseStability ρ f = boolNoiseStab ρ f :=
  (boolNoiseStab_eq_sum ρ f).symm

/-- **Majority Is Least Stable conjecture in $n$ variables.** For $n \in \mathbb{N}$, this is the
statement that every linear threshold function $f : \{-1, 1\}^n \to \mathbb{R}$ satisfies
$\mathrm{Stab}_\rho[f] \ge \mathrm{Stab}_\rho[\mathrm{Maj}_n]$ for every real $\rho$ with
$0 \le \rho \le 1$, where $\mathrm{Stab}_\rho$ is the noise stability and $\mathrm{Maj}_n$ is the
majority function. -/
def MajorityIsLeastStableFor (n : ℕ) : Prop :=
  ∀ f : BoolCube n → ℝ, IsLinearThresholdFunction f → ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
    noiseStability ρ (majority n) ≤ noiseStability ρ f

/-- **Majority Is Least Stable in some odd dimension at least five.** There is an odd natural
number $n \ge 5$ for which the Majority Is Least Stable conjecture in $n$ variables holds: every
linear threshold function $f : \{-1, 1\}^n \to \mathbb{R}$ satisfies
$\mathrm{Stab}_\rho[f] \ge \mathrm{Stab}_\rho[\mathrm{Maj}_n]$ for every real $\rho$ with
$0 \le \rho \le 1$, where $\mathrm{Stab}_\rho$ is the noise stability and $\mathrm{Maj}_n$ is the
majority function. -/
def majorityIsLeastStableForSomeOddAtLeastFive : Prop :=
  ∃ n : ℕ, Odd n ∧ 5 ≤ n ∧ MajorityIsLeastStableFor n

-- Represent a cube point by the set of its positive coordinates.
private def supportEquiv (n : ℕ) : BoolCube n ≃ Finset (Fin n) where
  toFun x := Finset.univ.filter fun i => x i
  invFun s i := decide (i ∈ s)
  left_inv x := by funext i; simp
  right_inv s := by ext i; simp

private theorem signSum {n : ℕ} (x : BoolCube n) :
    ∑ i, cubeVal (x i) = 2 * ((supportEquiv n x).card : ℝ) - n := by
  have h (i : Fin n) : cubeVal (x i) = 2 * (if x i then 1 else 0 : ℝ) - 1 := by
    cases x i <;> norm_num
  simp_rw [h, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [Finset.sum_boole, supportEquiv]

-- For a fixed coordinate, summing over its two possible values cancels except
-- when the remaining coordinates have equally many positive and negative signs.
private theorem majority_singleton (k : ℕ) (i : Fin (2 * k + 1)) :
    boolFourierCoeff _ (majority _) {i} =
      (2 * k.centralBinom : ℝ) / 2 ^ (2 * k + 1) := by
  classical
  rw [boolFourierCoeff_eq_sum_div_two_pow]
  congr 1
  let e := Fin.insertNthEquiv (fun _ : Fin (2 * k + 1) => Bool) i
  rw [← e.sum_comp]
  simp only [e, Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib,
    Fin.insertNthEquiv_apply, cubeChi_singleton, Fin.insertNth_apply_same, cubeVal_true,
    cubeVal_false, mul_one, mul_neg_one]
  have eval (x : BoolCube (2 * k)) (b : Bool) :
      majority _ (i.insertNth b x) =
        if 0 ≤ cubeVal b + (2 * ((supportEquiv _ x).card : ℝ) - 2 * k) then 1 else -1 := by
    rw [majority, Fin.sum_univ_succAbove _ i]
    simp [signSum]
  have pair (x : BoolCube (2 * k)) :
      majority _ (i.insertNth true x) + -majority _ (i.insertNth false x) =
        2 * (if (supportEquiv _ x).card = k then 1 else 0 : ℝ) := by
    rw [eval, eval, cubeVal_false, cubeVal_true]
    rcases lt_trichotomy (supportEquiv _ x).card k with h | h | h
    · have : ((supportEquiv _ x).card : ℝ) + 1 ≤ k := by exact_mod_cast h
      simp [h.ne, show ¬ 0 ≤ 1 + (2 * ((supportEquiv _ x).card : ℝ) - 2 * k) by linarith,
        show ¬ 0 ≤ -1 + (2 * ((supportEquiv _ x).card : ℝ) - 2 * k) by linarith]
    · norm_num [h]
    · have : (k : ℝ) + 1 ≤ (supportEquiv _ x).card := by exact_mod_cast h
      simp [h.ne', show 0 ≤ 1 + (2 * ((supportEquiv _ x).card : ℝ) - 2 * k) by linarith,
        show 0 ≤ -1 + (2 * ((supportEquiv _ x).card : ℝ) - 2 * k) by linarith]
  simp_rw [pair, ← Finset.mul_sum]
  rw [(supportEquiv _).sum_comp (fun s => if s.card = k then (1 : ℝ) else 0)]
  simp [Finset.sum_boole, ← Finset.powerset_univ, ← Finset.powersetCard_eq_filter,
    Nat.centralBinom]

private theorem centralBinom_gt {k : ℕ} (hk : 2 ≤ k) : 2 * k + 1 < k.centralBinom := by
  have bound := Nat.choose_le_centralBinom 2 k
  have step := Nat.choose_succ_right_eq (2 * k) 1
  norm_num only [Nat.choose_one_right, Nat.reduceAdd] at step
  have hk' : 3 ≤ 2 * k - 1 := by omega
  nlinarith [Nat.mul_le_mul_left (2 * k) hk']

private def antipode {n : ℕ} (p : BoolCube n) : BoolCube n := fun i => !p i

private theorem signSum_antipode {n : ℕ} (p : BoolCube n) :
    ∑ i, cubeVal (antipode p i) = -∑ i, cubeVal (p i) := by
  simp [antipode, Finset.sum_neg_distrib]

private theorem signSum_gap (k : ℕ) (x : BoolCube (2 * k + 1)) :
    (∑ i, cubeVal (x i)) ≤ -1 ∨ 1 ≤ ∑ i, cubeVal (x i) := by
  rw [signSum]
  push_cast
  by_cases h : (supportEquiv _ x).card ≤ k
  · left
    linarith [show ((supportEquiv _ x).card : ℝ) ≤ k by exact_mod_cast h]
  · right
    have : k + 1 ≤ (supportEquiv _ x).card := by omega
    linarith [show (k : ℝ) + 1 ≤ (supportEquiv _ x).card by exact_mod_cast this]

-- Distinct vertices disagree in at least one coordinate, losing two in their dot product.
private theorem dot_le {n : ℕ} {p x : BoolCube n} (hne : x ≠ p) :
    ∑ i, cubeVal (p i) * cubeVal (x i) ≤ (n : ℝ) - 2 := by
  let y : BoolCube n := fun i => decide (x i = p i)
  have hy (i : Fin n) : cubeVal (p i) * cubeVal (x i) = cubeVal (y i) := by
    cases hx : x i <;> cases hp : p i <;> norm_num [y, hx, hp]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
  have hss : supportEquiv n y ⊂ Finset.univ :=
    Finset.filter_ssubset.mpr ⟨j, Finset.mem_univ _, by simpa [y] using hj⟩
  have hcard : (supportEquiv n y).card + 1 ≤ n := by
    simpa using Finset.card_lt_card hss
  simp_rw [hy]
  rw [signSum]
  linarith [show ((supportEquiv n y).card : ℝ) + 1 ≤ n by exact_mod_cast hcard]

-- Reverse majority at a margin-one vertex and at its antipode.
private noncomputable def perturbed {n : ℕ} (p : BoolCube n) (x : BoolCube n) : ℝ :=
  majority n x - (if x = p then 2 else 0) + (if x = antipode p then 2 else 0)

private theorem perturbed_threshold (k : ℕ) (p : BoolCube (2 * k + 1))
    (hp : ∑ i, cubeVal (p i) = 1) :
    IsLinearThresholdFunction (perturbed p) := by
  refine ⟨0, fun i => 2 * (k : ℝ) - cubeVal (p i), ?_⟩
  intro x
  have ha := signSum_antipode p
  rw [hp] at ha
  have hne : p ≠ antipode p := fun h => by rw [← h, hp] at ha; norm_num at ha
  simp only [zero_add, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, perturbed]
  have hself : ∑ i, cubeVal (p i) * cubeVal (p i) = 2 * (k : ℝ) + 1 := by simp
  have hopp : ∑ i, cubeVal (p i) * cubeVal (antipode p i) = -(2 * (k : ℝ) + 1) := by
    simp [antipode]
  by_cases hx : x = p
  · subst x
    norm_num [majority, hp, hne, hself]
  by_cases hx' : x = antipode p
  · subst x
    norm_num [majority, ha, hx, hopp]
  simp only [hx, hx', ite_false, sub_zero, add_zero, majority]
  have upper := dot_le hx
  have lower := dot_le hx'
  simp only [antipode, cubeVal_not, neg_mul, Finset.sum_neg_distrib] at lower
  push_cast at upper lower
  rcases signSum_gap k x with h | h
  · rw [ite_eq_right (by linarith), ite_eq_right]
    nlinarith [mul_nonneg (show 0 ≤ 2 * (k : ℝ) by positivity) (show 0 ≤ -1 - ∑ i, cubeVal (x i)
      by linarith)]
  · rw [ite_eq_left (by linarith), ite_eq_left]
    nlinarith [mul_nonneg (show 0 ≤ 2 * (k : ℝ) by positivity) (sub_nonneg.mpr h)]

private theorem perturbed_coeff {n : ℕ} (p : BoolCube n) (S : Finset (Fin n)) :
    boolFourierCoeff n (perturbed p) S = boolFourierCoeff n (majority n) S +
      (2 * cubeChi n S (antipode p) - 2 * cubeChi n S p) / 2 ^ n := by
  classical
  simp only [boolFourierCoeff_eq_sum_div_two_pow, perturbed, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ite_mul, zero_mul]
  simp
  ring

-- With D = 2^n and B the central binomial coefficient, the singleton
-- coefficients change from 2B/D to (2B - 4pᵢ)/D.
private theorem singleton_gap {k : ℕ} (hk : 2 ≤ k) (p : BoolCube (2 * k + 1))
    (hp : ∑ i, cubeVal (p i) = 1) :
    0 < ∑ i : Fin (2 * k + 1), (boolFourierCoeff _ (majority _) {i} ^ 2 -
      boolFourierCoeff _ (perturbed p) {i} ^ 2) := by
  let D : ℝ := 2 ^ (2 * k + 1)
  have term (i : Fin (2 * k + 1)) :
      boolFourierCoeff _ (majority _) {i} ^ 2 - boolFourierCoeff _ (perturbed p) {i} ^ 2 =
        16 * ((k.centralBinom : ℝ) * cubeVal (p i) - 1) / D ^ 2 := by
    rw [perturbed_coeff, majority_singleton]
    simp only [cubeChi_singleton, antipode, cubeVal_not]
    change (2 * (k.centralBinom : ℝ) / D) ^ 2 -
      (2 * k.centralBinom / D + (2 * -cubeVal (p i) - 2 * cubeVal (p i)) / D) ^ 2 = _
    cases h : p i <;> simp only [cubeVal_true, cubeVal_false] <;> ring
  simp_rw [term]
  rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hp]
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hB : ((2 * k + 1 : ℕ) : ℝ) < k.centralBinom := by exact_mod_cast centralBinom_gt hk
  exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hB)) (by dsimp [D]; positivity)

-- After the equal constant terms cancel, divide the stability difference by ρ.
-- The resulting polynomial extends to zero with value equal to the singleton gap.
private theorem small_noise {n : ℕ} {f g : BoolCube n → ℝ}
    (h₀ : boolFourierCoeff n f ∅ = boolFourierCoeff n g ∅)
    (h₁ : 0 < ∑ i : Fin n, (boolFourierCoeff n f {i} ^ 2 - boolFourierCoeff n g {i} ^ 2)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ noiseStability ρ g < noiseStability ρ f := by
  classical
  let d (S : Finset (Fin n)) := boolFourierCoeff n f S ^ 2 - boolFourierCoeff n g S ^ 2
  let q (ρ : ℝ) := ∑ S : Finset (Fin n), ρ ^ (S.card - 1) * d S
  have hd : d ∅ = 0 := by simp [d, h₀]
  have hq : 0 < q 0 := by
    have term (S : Finset (Fin n)) : (0 : ℝ) ^ (S.card - 1) * d S =
        if S.card = 1 then d S else 0 := by
      rcases S.eq_empty_or_nonempty with rfl | h
      · simp [hd]
      · by_cases hS : S.card = 1
        · simp [hS]
        · have := h.card_pos
          simp [hS, zero_pow (show S.card - 1 ≠ 0 by omega)]
    change 0 < ∑ S, (0 : ℝ) ^ (S.card - 1) * d S
    simp_rw [term]
    rw [← Finset.sum_filter, ← Finset.powerset_univ, ← Finset.powersetCard_eq_filter,
      Finset.powersetCard_one, Finset.sum_map]
    exact h₁
  have cont : Continuous q :=
    continuous_finsetSum _ fun S _ => (continuous_pow (S.card - 1)).mul continuous_const
  have near := continuousAt_const.eventually_lt cont.continuousAt hq
  obtain ⟨ε, hε, H⟩ := Metric.eventually_nhds_iff.mp near
  let ρ := min ε 1 / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hε' : ρ < ε := by dsimp [ρ]; linarith [min_le_left ε 1]
  have hρ' : ρ < 1 := by dsimp [ρ]; linarith [min_le_right ε 1]
  refine ⟨ρ, hρ, hρ', sub_pos.mp ?_⟩
  have Hρ : 0 < q ρ := H (by simpa [Real.dist_eq, abs_of_pos hρ] using hε')
  convert mul_pos hρ Hρ using 1
  simp only [noiseStability, q, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← mul_sub, ← mul_assoc]
  rcases S.eq_empty_or_nonempty with rfl | h
  · simp [d, h₀]
  · rw [← pow_succ', Nat.sub_add_cancel h.card_pos]

/--
**Majority Is Least Stable fails in every odd dimension at least five.** For every odd natural
number $n \ge 5$, the Majority Is Least Stable conjecture in $n$ variables fails: there are a
linear threshold function $f : \{-1, 1\}^n \to \mathbb{R}$ and a real number $\rho$ with
$0 \le \rho \le 1$ such that $\mathrm{Stab}_\rho[f] < \mathrm{Stab}_\rho[\mathrm{Maj}_n]$, where
$\mathrm{Stab}_\rho$ is the noise stability and $\mathrm{Maj}_n$ is the majority function.

Biswas and Sarkar exhibit, for every odd $n \ge 5$, a linear threshold function $g_n$ with
$\mathrm{Stab}_\rho[g_n] < \mathrm{Stab}_\rho[\mathrm{Maj}_n]$ for all small $\rho > 0$. The
conjecture holds for $n = 1$ and $n = 3$; those cases are not formalized here.

Source: R. O'Donnell, Open problems in analysis of Boolean
functions, arXiv:1204.6447 (2012), 'Majority Is Least Stable Conjecture' (Benjamini, Kalai,
Schramm); resolution: A. Biswas, P. Sarkar, On the "majority is least stable" conjecture, Inform.
Process. Lett. 179 (2023), 106295, arXiv:2202.09024, Theorem 2 of arXiv:2202.09024v2: the conjecture
is true for n = 1 and n = 3 and false for every odd n ≥ 5; for odd n ≥ 5 the linear threshold
function g_n(x) = sgn(2(x₁ + ⋯ + x_{n-3}) + x_{n-2} + x_{n-1} + x_n) has W⁰[g_n] = 0 and W¹[g_n] <
W¹[Maj_n] (Lemmas 3 and 4), hence Stab_ρ[g_n] < Stab_ρ[Maj_n] for all small ρ > 0 (Lemma 1); the
case n = 5 is V. Jain, arXiv:1703.07657, https://doi.org/10.1016/j.ipl.2022.106295.
-/
theorem majorityIsLeastStableForSomeOddAtLeastFive_refuted :
    ¬ majorityIsLeastStableForSomeOddAtLeastFive := by
  rintro ⟨_, ⟨k, rfl⟩, hn, h⟩
  have hk : 2 ≤ k := by omega
  obtain ⟨s, _, hs⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin (2 * k + 1)))) (n := k + 1) (by simp; omega)
  let p := (supportEquiv _).symm s
  have hp : ∑ i, cubeVal (p i) = 1 := by simp [signSum, p, hs]; ring
  have h₀ : boolFourierCoeff _ (majority (2 * k + 1)) ∅ = boolFourierCoeff _ (perturbed p) ∅ := by
    simp [perturbed_coeff]
  obtain ⟨ρ, hρ, hρ', hlt⟩ := small_noise h₀ (singleton_gap hk p hp)
  exact hlt.not_ge (h _ (perturbed_threshold k p hp) ρ hρ.le hρ'.le)

end MathlibExt.Combinatorics.MajorityIsLeastStableAMR127Problem0009Wanted
