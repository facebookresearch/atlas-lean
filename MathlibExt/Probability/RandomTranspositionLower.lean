/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RandomWalkFiniteGroup
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A lower bound for mixing by random transpositions

The Diaconis–Shahshahani lower bound follows by testing on derangements. A position
untouched by either endpoint of any transposition is still a fixed point.
-/

open scoped BigOperators Topology
open Equiv Filter
open MathlibExt.RepresentationTheory.FourierTransformFiniteGroup (conv convPow sum_conv)
open MathlibExt.Probability.RandomWalkFiniteGroup
  (uniform randomTransposition sum_randomTransposition)
open MathlibExt.Probability.MarkovMixing (tvDist)

namespace MathlibExt.Probability.RandomWalkFiniteGroupWanted

variable {n : ℕ} [NeZero n]

private abbrev WalkPerm (n : ℕ) := Equiv.Perm (Fin n)

omit [NeZero n] in
private theorem swap_eq_swap_iff {a b i j : Fin n} (hab : a ≠ b) :
    swap i j = swap a b ↔ (i = a ∧ j = b) ∨ (i = b ∧ j = a) := by
  constructor
  · intro h
    have ha := DFunLike.congr_fun h a
    have hb := DFunLike.congr_fun h b
    simp only [swap_apply_def] at ha hb
    grind
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact swap_comm _ _

/-- Sampling two independent uniform endpoints and interchanging them gives the
random-transposition measure, including the identity step when the endpoints agree. -/
public theorem randomTransposition_eq_expect (σ : Equiv.Perm (Fin n)) :
    randomTransposition n σ =
      𝔼 i : Fin n, 𝔼 j : Fin n, if swap i j = σ then (1 : ℝ) else 0 := by
  classical
  by_cases h : σ = 1
  · subst σ
    simp [randomTransposition, swap_eq_one_iff]
  by_cases hs : σ.IsSwap
  · obtain ⟨a, b, hab, rfl⟩ := hs
    have hsplit (i j : Fin n) :
        (if swap i j = swap a b then (1 : ℝ) else 0) =
          (if i = a then (if j = b then 1 else 0) else 0) +
          (if i = b then (if j = a then 1 else 0) else 0) := by
      simp only [swap_eq_swap_iff hab]
      split_ifs <;> grind
    simp_rw [hsplit, Fintype.expect_eq_sum_div_card, Finset.sum_add_distrib,
      Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero]
    simp [randomTransposition, h, Perm.swap_isSwap_iff, hab, add_div, ite_div,
      Finset.sum_add_distrib]
    ring
  · have hne (i j : Fin n) : swap i j ≠ σ := by
      rintro rfl
      by_cases hij : i = j
      · exact h (swap_eq_one_iff.mpr hij)
      · exact hs (Perm.swap_isSwap_iff.mpr hij)
    simp [randomTransposition, h, hs, hne]

private noncomputable abbrev walk (n k : ℕ) [NeZero n] := convPow (randomTransposition n) k

private theorem walk_nonneg (k : ℕ) (σ : WalkPerm n) : 0 ≤ walk n k σ := by
  induction k generalizing σ with
  | zero => simp [walk, convPow]; split <;> norm_num
  | succ k ih =>
    apply Finset.sum_nonneg
    intro τ _
    apply mul_nonneg _ (ih τ)
    unfold randomTransposition
    split_ifs <;> positivity

private theorem sum_walk (k : ℕ) : ∑ σ, walk n k σ = 1 := by
  induction k with
  | zero => simp [walk, convPow]
  | succ k ih => rw [walk, convPow, sum_conv, sum_randomTransposition, one_mul]; exact ih

private theorem walk_succ_expect (k : ℕ) (f : WalkPerm n → ℝ) :
    ∑ σ, walk n (k + 1) σ * f σ =
      𝔼 i : Fin n, 𝔼 j : Fin n, ∑ τ, walk n k τ * f (swap i j * τ) := by
  classical
  simp only [walk, convPow, conv, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [randomTransposition_eq_expect, Finset.expect_mul, ← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro i _
  apply Finset.expect_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro τ _
  simp only [eq_mul_inv_iff_mul_eq, ite_mul, one_mul, zero_mul]
  simp

-- Drawing one endpoint removes it from the set of positions still required.
private theorem expect_erase_pow (s : Finset (Fin n)) {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1) :
    (𝔼 i, (1 - u) ^ (s.erase i).card) ≤ (1 - u * (1 - 1 / n)) ^ s.card := by
  classical
  by_cases hs : s = ∅
  · simp [hs]
  have hcard : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
  have hone : s.card - 1 + 1 = s.card := by omega
  have hterm (i : Fin n) : (1 - u) ^ (s.erase i).card =
      (1 - u) ^ s.card + (if i ∈ s then (1 - u) ^ (s.card - 1) * u else 0) := by
    by_cases hi : i ∈ s
    · rw [Finset.card_erase_of_mem hi, ite_eq_left hi]
      conv_rhs => lhs; rw [← hone, pow_succ]
      ring
    · simp [hi]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  simp only [hterm, Fintype.expect_eq_sum_div_card, Fintype.card_fin, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hbern := pow_add_mul_le_add_pow (a := 1 - u) (b := u / n) (sub_nonneg.mpr hu')
    (by positivity : 0 ≤ 2 * (1 - u) + u / n) s.card
  convert hbern using 1
  · field_simp
  · congr 1
    ring

private noncomputable def moved (s : Finset (Fin n)) (σ : WalkPerm n) : ℝ :=
  if s ⊆ σ.support then 1 else 0

private noncomputable def movedMass (k : ℕ) (s : Finset (Fin n)) : ℝ :=
  ∑ σ, walk n k σ * moved s σ

-- Only the two endpoints can become newly moved positions.
omit [NeZero n] in
private theorem moved_swap_le (s : Finset (Fin n)) (i j : Fin n) (σ : WalkPerm n) :
    moved s (swap i j * σ) ≤ moved ((s.erase i).erase j) σ := by
  have hsub : s ⊆ (swap i j * σ).support → (s.erase i).erase j ⊆ σ.support := by
    intro h x hx
    obtain ⟨hxj, hxi, hxs⟩ := (by simpa only [Finset.mem_erase] using hx :
      x ≠ j ∧ x ≠ i ∧ x ∈ s)
    rw [Perm.mem_support]
    intro he
    have := Perm.mem_support.mp (h hxs)
    exact this (by simp [Perm.mul_apply, he, swap_apply_of_ne_of_ne hxi hxj])
  unfold moved
  split_ifs <;> grind

private theorem movedMass_le (k : ℕ) (s : Finset (Fin n)) :
    movedMass k s ≤ (1 - (1 - 1 / (n : ℝ)) ^ (2 * k)) ^ s.card := by
  classical
  have hn : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have hq : 0 ≤ 1 - 1 / (n : ℝ) := by
    exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr hn)
  have hu (r : ℕ) : (1 - 1 / (n : ℝ)) ^ r ≤ 1 :=
    pow_le_one₀ hq (by simp)
  induction k generalizing s with
  | zero =>
    by_cases hs : s = ∅
    · simp [movedMass, moved, walk, convPow, hs]
    · simp only [movedMass, walk, convPow, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      simp [moved, hs]
  | succ k ih =>
    rw [movedMass, walk_succ_expect]
    calc
      _ ≤ 𝔼 i : Fin n, 𝔼 j : Fin n, movedMass k ((s.erase i).erase j) := by
        apply Finset.expect_le_expect fun i _ => ?_
        apply Finset.expect_le_expect fun j _ => ?_
        exact Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_left (moved_swap_le s i j σ) (walk_nonneg k σ)
      _ ≤ 𝔼 i : Fin n, (1 - (1 - 1 / (n : ℝ)) ^ (2 * k + 1)) ^ (s.erase i).card := by
        apply Finset.expect_le_expect fun i _ => ?_
        rw [pow_succ]
        exact (Finset.expect_le_expect fun j _ => ih ((s.erase i).erase j)).trans
          (expect_erase_pow (s.erase i) (pow_nonneg hq _) (hu _))
      _ ≤ _ := by
        simpa only [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, pow_succ] using
          expect_erase_pow s (pow_nonneg hq (2 * k + 1)) (hu _)

omit [NeZero n] in
private theorem uniform_movedMass :
    ∑ σ : WalkPerm n, uniform _ σ * moved Finset.univ σ =
      (numDerangements n : ℝ) / n.factorial := by
  classical
  have he (σ : WalkPerm n) : Finset.univ ⊆ σ.support ↔ σ ∈ derangements (Fin n) := by
    simp [derangements, Finset.subset_iff, Perm.mem_support]
  simp only [uniform, moved, he, mul_ite, mul_one, mul_zero, ← Finset.sum_filter,
    Finset.sum_const, nsmul_eq_mul]
  rw [← Fintype.card_subtype, card_derangements_fin_eq_numDerangements, Fintype.card_perm,
    Fintype.card_fin, div_eq_mul_inv]

private theorem derangement_test (k : ℕ) :
    (numDerangements n : ℝ) / n.factorial - movedMass (n := n) k Finset.univ ≤
      tvDist (walk n k) (uniform _) := by
  have h (σ : WalkPerm n) :
      2 * (uniform _ σ * moved Finset.univ σ - walk n k σ * moved Finset.univ σ) ≤
        |walk n k σ - uniform _ σ| + (uniform _ σ - walk n k σ) := by
    unfold moved
    split <;> simp only [mul_one, mul_zero, sub_self] <;>
      linarith [le_abs_self (walk n k σ - uniform _ σ), neg_le_abs (walk n k σ - uniform _ σ)]
  have hs := Finset.sum_le_sum (s := Finset.univ) fun σ _ => h σ
  have hU : ∑ σ : WalkPerm n, uniform _ σ = 1 := by simp [uniform]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_walk, hU,
    uniform_movedMass, sub_self, add_zero] at hs
  unfold tvDist movedMass
  linarith

private theorem profile_lipschitz (x y : ℝ) :
    |Real.exp (-Real.exp x) - Real.exp (-Real.exp y)| ≤ |x - y| := by
  let f (z : ℝ) := Real.exp (-Real.exp z)
  have hd (z : ℝ) : HasDerivAt f (Real.exp (-Real.exp z) * (-Real.exp z)) z :=
    (Real.hasDerivAt_exp z).neg.exp
  have hb (z : ℝ) : ‖Real.exp (-Real.exp z) * (-Real.exp z)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _),
      abs_of_pos (Real.exp_pos _), Real.exp_neg, inv_mul_le_one₀ (Real.exp_pos _)]
    exact (Real.add_one_le_exp _).trans' (by linarith)
  simpa [Real.norm_eq_abs, f] using
    (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z _ => (hd z).hasDerivWithinAt) (fun z _ => hb z) (Set.mem_univ y) (Set.mem_univ x)

-- In the pre-cutoff range the error in the logarithm of the expected number
-- of untouched positions is at most log(n)/(n-1), uniformly in the step count.
omit [NeZero n] in
private theorem cover_error (hn : 1 < n) (m : ℕ) (hm : (m : ℝ) ≤ n * Real.log n) :
    (1 - (1 - 1 / (n : ℝ)) ^ m) ^ n ≤
      Real.exp (-Real.exp (Real.log n - m / n)) + Real.log n / (n - 1) := by
  set N : ℝ := (n : ℝ)
  have hN : 1 < N := by
    change 1 < (n : ℝ)
    exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hq : 0 < 1 - 1 / N := sub_pos.mpr ((div_lt_one hN0).mpr hN)
  have hq' : 1 - 1 / N ≤ 1 := by linarith [one_div_pos.mpr hN0]
  have hl := Real.log_le_sub_one_of_pos hq
  have hl' : -(1 / (N - 1)) ≤ Real.log (1 - 1 / N) := by
    refine le_trans (le_of_eq ?_) (Real.one_sub_inv_le_log_of_pos hq)
    field_simp
    ring
  have hgap := profile_lipschitz (Real.log N + m * Real.log (1 - 1 / N))
    (Real.log N - m / N)
  have hsign : Real.log N + m * Real.log (1 - 1 / N) ≤ Real.log N - m / N := by
    have := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α := ℝ) m)
    simp only [div_eq_mul_inv, one_mul] at this ⊢
    linarith
  rw [abs_of_nonpos (sub_nonpos.mpr hsign)] at hgap
  have herr : -(m / N) - m * Real.log (1 - 1 / N) ≤ Real.log N / (N - 1) := by
    calc
      _ ≤ -(m / N) - m * (-(1 / (N - 1))) := by gcongr
      _ = (m / N) / (N - 1) := by field_simp; ring
      _ ≤ _ := by gcongr; exact (div_le_iff₀ hN0).mpr (by linarith)
  have hdiff := (le_abs_self _).trans hgap
  rw [Real.exp_add, Real.exp_log hN0, Real.exp_nat_mul, Real.exp_log hq] at hdiff
  have hpow := pow_le_pow_left₀ (sub_nonneg.mpr (pow_le_one₀ hq.le hq' (n := m)))
    (by linarith [Real.add_one_le_exp (-((1 - 1 / N) ^ m))] :
      1 - (1 - 1 / N) ^ m ≤ Real.exp (-((1 - 1 / N) ^ m))) n
  rw [← Real.exp_nat_mul, mul_neg] at hpow
  change _ ≤ Real.exp (-(N * (1 - 1 / N) ^ m)) at hpow
  linarith

/-- **Random transpositions: fewer than `(1/2) n log n` steps do not suffice
(Diaconis–Shahshahani).** For every choice of step numbers `k = k(n)`, with
`c = (k - (1/2) n log n) / n`, `‖T^{*k} - U‖ ≥ 2 (1/e - exp(-e^{-2c})) + o(1)` as `n → ∞`, in the
`ℓ¹` norm `‖·‖ = 2 ‖·‖_TV` (Diaconis and Shahshahani 1981, Theorem 2, proved there with the set
of permutations having a fixed point, an argument they credit to Charles Stein). -/
public theorem diaconis_shahshahani_lower (k : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ [NeZero n],
      2 * (Real.exp (-1) - Real.exp (-Real.exp (-2 * (((k n : ℝ) - n * Real.log n / 2) / n))))
        - ε ≤ 2 * tvDist (convPow (randomTransposition n) (k n))
          (uniform (Equiv.Perm (Fin n))) := by
  have hratio := numDerangements_tendsto_inv_e.eventually_const_lt
    (show Real.exp (-1) - ε / 4 < Real.exp (-1) by linarith)
  have hlog : Tendsto (fun n : ℕ => Real.log n / (n - 1)) atTop (𝓝 0) := by
    simpa [sub_eq_add_neg, Function.comp_def] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_gt_atTop 1, hratio,
    hlog.eventually_lt_const (show 0 < ε / 4 by linarith)] with n hn hr he
  intro inst
  have hn0 : (0 : ℝ) < n := by positivity
  have harg : -2 * (((k n : ℝ) - n * Real.log n / 2) / n) =
      Real.log n - (2 * k n : ℕ) / (n : ℝ) := by
    push_cast
    field_simp
    ring
  rw [harg]
  by_cases hm : ((2 * k n : ℕ) : ℝ) ≤ n * Real.log n
  · have hc := cover_error hn (2 * k n) hm
    have hw := movedMass_le (n := n) (k n) Finset.univ
    rw [Finset.card_univ, Fintype.card_fin] at hw
    have ht := derangement_test (n := n) (k n)
    change _ ≤ 2 * tvDist (walk n (k n)) (uniform _)
    linarith
  · have hx : Real.log n - (2 * k n : ℕ) / (n : ℝ) ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hn0, mul_comm]
      exact le_of_not_ge hm
    have hp := Real.exp_le_exp.mpr hx
    rw [Real.exp_zero] at hp
    have hl := Real.exp_le_exp.mpr (neg_le_neg hp)
    have htv : 0 ≤ tvDist (walk n (k n)) (uniform _) := by
      unfold tvDist
      positivity
    change _ ≤ 2 * tvDist (walk n (k n)) (uniform _)
    linarith

end MathlibExt.Probability.RandomWalkFiniteGroupWanted
