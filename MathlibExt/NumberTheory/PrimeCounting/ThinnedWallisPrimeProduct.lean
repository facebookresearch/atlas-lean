/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.SumPrimeReciprocals
import MathlibExt.NumberTheory.PrimeCounting.WeakPNTArithmeticProgression

/-!
# Convergence of thinned Wallis-type prime products modulo `2^m`

This file proves the convergence criterion `thinned_wallis_prime_product_tendsto_pos_iff` from
Mike Winkler, *Thinned Wallis-Type Prime Products in Residue Classes Modulo 2^m*, INTEGERS 26
(2026), Article A90, Corollary 1: the thinned Wallis-type prime product `P_S(x)` converges to a
positive real limit as `x → ∞` if and only if `μ(S) = 0`.

Following the source (arXiv:2602.13371v4, abstract and Sections 1–4): for an odd prime `p`,
`A(p) = (p - χ₄(p))/(p + χ₄(p))` with `χ₄ = ZMod.χ₄`; for `q = 2^m`, `m ≥ 2`, and a set
`S` of reduced residues modulo `q`, `P_S(x) = ∏_{p ≤ x, p mod q ∈ S} A(p)` over primes;
`μ(S) = ∑_{a ∈ S} χ₄(a)`, where `χ₄(a)` is `χ₄` of the reduction of `a` modulo `4`. Since
every element of `S` is a unit and `2` is not a unit modulo `2^m`, the product only
involves odd primes.

## Proof

The source deduces the criterion from its Theorem 1, which rests on Mertens' theorem in
arithmetic progressions with an explicit constant. Only a difference form of that theorem is
needed here: for units `a` and `b` modulo `q`, the partial sums of `1/p` over the primes
`p ≡ a (mod q)` minus those over the primes `p ≡ b (mod q)` converge. This follows from
Dirichlet's test, the bounded error term in Mertens' theorem in arithmetic progressions
(`Chebyshev.exists_abs_sum_residueClass_div_sub_log_le`) and the summability of the
contribution of prime powers. Since `log A(p) = -2 χ₄(p)/p + O(1/p²)`, the logarithm of the
partial product is `-2 μ(S)` times the reciprocal sum over one residue class plus a convergent
sequence, and that reciprocal sum diverges because the sum of the reciprocals of all primes does.
-/

open Filter Topology

namespace MetaMathlibExt

namespace ThinnedWallisPrimeProduct

open ArithmeticFunction

/-- The partial sums of `1 / p` over the primes `p < N` with `p ≡ a (mod q)`. -/
private noncomputable def recipSum {q : ℕ} (a : ZMod q) (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range N).filter (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a), (1 : ℝ) / p

/-- The prime reciprocal sums are nonnegative. -/
private lemma recipSum_nonneg {q : ℕ} (a : ZMod q) (N : ℕ) : 0 ≤ recipSum a N :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- A sum over `range (N + 1)` is a sum over `Ioc 0 N` when the term at `0` vanishes. -/
private lemma sum_range_succ_eq_sum_Ioc (f : ℕ → ℝ) (hf : f 0 = 0) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), f n = ∑ n ∈ Finset.Ioc 0 N, f n := by
  rw [Finset.sum_range_eq_add_Ico f (by omega : 0 < N + 1), hf, zero_add,
    ← Finset.Ico_add_one_add_one_eq_Ioc, zero_add]

/-- Bounded partial sums of `(Λ(p) 1_{p ≡ a} - Λ(p) 1_{p ≡ b}) / p` over primes, from Mertens'
theorem in arithmetic progressions. -/
private lemma exists_bound_sum_prime_residueClass_sub {q : ℕ} [NeZero q] {a b : ZMod q}
    (ha : IsUnit a) (hb : IsUnit b) :
    ∃ B : ℝ, ∀ N : ℕ, ‖∑ n ∈ Finset.range N,
      (if n.Prime then vonMangoldt.residueClass a n - vonMangoldt.residueClass b n else 0) /
        (n : ℝ)‖ ≤ B := by
  obtain ⟨Ca, hCa⟩ := Chebyshev.exists_abs_sum_residueClass_div_sub_log_le a ha
  obtain ⟨Cb, hCb⟩ := Chebyshev.exists_abs_sum_residueClass_div_sub_log_le b hb
  have hsa := vonMangoldt.summable_residueClass_non_primes_div a
  have hsb := vonMangoldt.summable_residueClass_non_primes_div b
  have hnn : ∀ (c : ZMod q) (n : ℕ),
      0 ≤ (if n.Prime then 0 else vonMangoldt.residueClass c n) / (n : ℝ) := by
    intro c n
    apply div_nonneg _ (Nat.cast_nonneg n)
    split_ifs
    · exact le_rfl
    · exact vonMangoldt.residueClass_nonneg c n
  have hCa0 : 0 ≤ Ca := le_trans (abs_nonneg _) (hCa 1 le_rfl)
  have hCb0 : 0 ≤ Cb := le_trans (abs_nonneg _) (hCb 1 le_rfl)
  refine ⟨Ca + Cb + (∑' n : ℕ, (if n.Prime then 0 else vonMangoldt.residueClass a n) / (n : ℝ)) +
    ∑' n : ℕ, (if n.Prime then 0 else vonMangoldt.residueClass b n) / (n : ℝ), fun N => ?_⟩
  have hfull : |∑ n ∈ Finset.range N,
      (vonMangoldt.residueClass a n - vonMangoldt.residueClass b n) / (n : ℝ)| ≤ Ca + Cb := by
    rcases N with _ | N
    · simp only [Finset.range_zero, Finset.sum_empty, abs_zero]
      linarith
    · rw [sum_range_succ_eq_sum_Ioc _ (by simp) N]
      rcases N with _ | N
      · simp only [Finset.Ioc_self, Finset.sum_empty, abs_zero]
        linarith
      · have h1 : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos N
        have ha' := hCa _ h1
        have hb' := hCb _ h1
        rw [Nat.floor_natCast] at ha' hb'
        simp only [sub_div, Finset.sum_sub_distrib]
        rw [abs_le] at ha' hb' ⊢
        constructor <;> linarith [ha'.1, ha'.2, hb'.1, hb'.2]
  have hTa := hsa.sum_le_tsum (Finset.range N) (fun n _ => hnn a n)
  have hTb := hsb.sum_le_tsum (Finset.range N) (fun n _ => hnn b n)
  have hTa0 : 0 ≤ ∑ n ∈ Finset.range N,
      (if n.Prime then 0 else vonMangoldt.residueClass a n) / (n : ℝ) :=
    Finset.sum_nonneg fun n _ => hnn a n
  have hTb0 : 0 ≤ ∑ n ∈ Finset.range N,
      (if n.Prime then 0 else vonMangoldt.residueClass b n) / (n : ℝ) :=
    Finset.sum_nonneg fun n _ => hnn b n
  have key : ∑ n ∈ Finset.range N,
      (if n.Prime then vonMangoldt.residueClass a n - vonMangoldt.residueClass b n else 0) /
        (n : ℝ) =
      ∑ n ∈ Finset.range N,
          (vonMangoldt.residueClass a n - vonMangoldt.residueClass b n) / (n : ℝ) -
        ∑ n ∈ Finset.range N,
          (if n.Prime then 0 else vonMangoldt.residueClass a n) / (n : ℝ) +
        ∑ n ∈ Finset.range N,
          (if n.Prime then 0 else vonMangoldt.residueClass b n) / (n : ℝ) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> ring
  rw [Real.norm_eq_abs, key]
  rw [abs_le] at hfull ⊢
  constructor <;> linarith [hfull.1, hfull.2]

/-- The difference of the prime reciprocal sums over two reduced residue classes converges. -/
private lemma exists_tendsto_recipSum_sub {q : ℕ} [NeZero q] {a b : ZMod q}
    (ha : IsUnit a) (hb : IsUnit b) :
    ∃ ℓ : ℝ, Tendsto (fun N : ℕ => recipSum a N - recipSum b N) atTop (𝓝 ℓ) := by
  obtain ⟨B, hB⟩ := exists_bound_sum_prime_residueClass_sub ha hb
  have hlogpos : ∀ n : ℕ, 0 < Real.log (max (n : ℝ) 2) := fun n =>
    Real.log_pos (lt_of_lt_of_le (by norm_num) (le_max_right _ _))
  have hfa : Antitone fun n : ℕ => (Real.log (max (n : ℝ) 2))⁻¹ := by
    intro i j hij
    apply inv_anti₀ (hlogpos i)
    apply Real.log_le_log (lt_of_lt_of_le (by norm_num) (le_max_right _ _))
    exact max_le_max (by exact_mod_cast hij) le_rfl
  have hf0 : Tendsto (fun n : ℕ => (Real.log (max (n : ℝ) 2))⁻¹) atTop (𝓝 0) := by
    apply Tendsto.inv_tendsto_atTop
    apply Real.tendsto_log_atTop.comp
    exact tendsto_atTop_mono (fun n => le_max_left _ _) tendsto_natCast_atTop_atTop
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete
    (hfa.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 hB)
  refine ⟨ℓ, hℓ.congr fun N => ?_⟩
  simp only [recipSum, Finset.sum_filter, ← Finset.sum_sub_distrib, smul_eq_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hn : n.Prime
  · have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn.two_le
    have hlog : Real.log n ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
    rw [max_eq_left h2]
    simp only [vonMangoldt.residueClass, Set.indicator_apply, Set.mem_ofPred_eq,
      vonMangoldt_apply_prime hn, hn, true_and]
    split_ifs <;> field_simp <;> ring
  · simp [hn]

/-- The prime reciprocal sum over a reduced residue class diverges. -/
private lemma tendsto_recipSum_atTop {q : ℕ} [NeZero q] {b : ZMod q} (hb : IsUnit b) :
    Tendsto (recipSum b) atTop atTop := by
  have hall : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      ({p | p.Prime}.indicator (fun n : ℕ => (1 : ℝ) / n)) n) atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (fun n => Set.indicator_nonneg (fun n _ => by positivity) n)).mp
      not_summable_one_div_on_primes
  have hdecomp : ∀ N, ∑ n ∈ Finset.range N,
      ({p | p.Prime}.indicator (fun n : ℕ => (1 : ℝ) / n)) n = ∑ c : ZMod q, recipSum c N := by
    intro N
    rw [← Finset.sum_fiberwise (Finset.range N) (fun n : ℕ => (n : ZMod q))]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [recipSum, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    by_cases hn : n.Prime <;> by_cases hc : (n : ZMod q) = c <;> simp [hn, hc]
  have hbound : ∀ c : ZMod q, ∃ K : ℝ, ∀ N, recipSum c N ≤ recipSum b N + K := by
    intro c
    by_cases hc : IsUnit c
    · obtain ⟨ℓ, hℓ⟩ := exists_tendsto_recipSum_sub hc hb
      obtain ⟨K, hK⟩ := hℓ.bddAbove_range
      refine ⟨K, fun N => ?_⟩
      have := hK ⟨N, rfl⟩
      linarith
    · refine ⟨∑ n ∈ Finset.range (q + 1), (1 : ℝ) / n, fun N => ?_⟩
      have hnn := recipSum_nonneg b N
      have : recipSum c N ≤ ∑ n ∈ Finset.range (q + 1), (1 : ℝ) / n := by
        unfold recipSum
        calc _ ≤ ∑ n ∈ (Finset.range (q + 1)).filter
                (fun p : ℕ => p.Prime ∧ (p : ZMod q) = c), (1 : ℝ) / n := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro n hn
                simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
                refine ⟨?_, hn.2⟩
                have hnu : ¬ IsUnit (n : ZMod q) := hn.2.2 ▸ hc
                rw [ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd hn.2.1,
                  not_not] at hnu
                have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hnu
                omega
              · intro n _ _
                positivity
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun n _ _ => by positivity)
      linarith
  choose K hK using hbound
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hle : ∀ N, (∑ n ∈ Finset.range N,
      ({p | p.Prime}.indicator (fun n : ℕ => (1 : ℝ) / n)) n + -∑ c : ZMod q, K c) / q ≤
        recipSum b N := by
    intro N
    rw [div_le_iff₀ hq, hdecomp N]
    have : ∑ c : ZMod q, recipSum c N ≤ ∑ c : ZMod q, (recipSum b N + K c) :=
      Finset.sum_le_sum fun c _ => hK c N
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul] at this
    linarith
  exact tendsto_atTop_mono hle
    ((tendsto_atTop_add_const_right _ _ hall).atTop_div_const hq)

/-- A second-order estimate for `log ((1 - u) / (1 + u))`. -/
private lemma abs_log_div_add_two_mul_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |Real.log ((1 - u) / (1 + u)) + 2 * u| ≤ 4 * u ^ 2 := by
  have hu1 : |u| < 1 := by linarith
  have h1 := Real.abs_log_sub_add_sum_range_le hu1 1
  have h2 := Real.abs_log_sub_add_sum_range_le (x := -u) (by rwa [abs_neg]) 1
  simp only [Finset.sum_range_one, pow_one, Nat.cast_zero, zero_add, div_one, abs_neg,
    sub_neg_eq_add] at h1 h2
  have hpos1 : 0 < 1 - u := by have := le_abs_self u; linarith
  have hpos2 : 0 < 1 + u := by have := neg_abs_le u; linarith
  rw [Real.log_div hpos1.ne' hpos2.ne']
  have hb : |u| ^ 2 / (1 - |u|) ≤ 2 * u ^ 2 := by
    rw [div_le_iff₀ (by linarith), sq_abs]
    nlinarith [sq_nonneg u, abs_nonneg u]
  calc |Real.log (1 - u) - Real.log (1 + u) + 2 * u|
      = |(u + Real.log (1 - u)) - (-u + Real.log (1 + u))| := by ring_nf
    _ ≤ |u + Real.log (1 - u)| + |-u + Real.log (1 + u)| := abs_sub _ _
    _ ≤ 2 * u ^ 2 + 2 * u ^ 2 := add_le_add (h1.trans hb) (h2.trans hb)
    _ = 4 * u ^ 2 := by ring

/-- A prime that is a unit modulo `2 ^ m`, `m ≥ 1`, is odd. -/
private lemma odd_of_isUnit_natCast {m p : ℕ} (hm : 1 ≤ m) (h : IsUnit (p : ZMod (2 ^ m))) :
    Odd p := by
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega)] at h
  exact h.odd_of_right

/-- At an odd number, `χ₄` takes the value `1` or `-1`. -/
private lemma chi4_natCast_eq_one_or_neg_one {p : ℕ} (hp : Odd p) :
    ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ) = 1 ∨ ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ) = -1 := by
  have h2 : p % 2 ≠ 0 := by obtain ⟨k, rfl⟩ := hp; omega
  rw [ZMod.χ₄_nat_eq_if_mod_four, ite_eq_right h2]
  split_ifs <;> simp

/-- The Wallis factor at an odd prime is positive, and its logarithm is `-2 χ₄(p) / p` up to an
error at most `4 / p ^ 2`. -/
private lemma factor_pos_and_abs_log_add_le {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    0 < ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4)) ∧
    |Real.log (((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4))) +
        2 * ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ) / p| ≤ 4 / (p : ℝ) ^ 2 := by
  have h3 : (3 : ℝ) ≤ p := by
    have h2 := hp.two_le
    have : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) even_two
    exact_mod_cast (by omega : 3 ≤ p)
  have hc' := chi4_natCast_eq_one_or_neg_one hodd
  set c : ℝ := ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ) with hc
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hcsq : c ^ 2 = 1 := by rcases hc' with h | h <;> rw [h] <;> norm_num
  constructor
  · rcases hc' with h | h <;> rw [h] <;> apply div_pos <;> linarith
  · have hu_abs : |c / p| = 1 / p := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < p)]
      rcases hc' with h | h <;> rw [h] <;> simp
    have hu_le : |c / p| ≤ 1 / 2 := by
      rw [hu_abs, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    have heq : ((p : ℝ) - c) / ((p : ℝ) + c) = (1 - c / p) / (1 + c / p) := by
      field_simp
    rw [heq]
    have := abs_log_div_add_two_mul_le hu_le
    have hu2 : (c / p) ^ 2 = 1 / (p : ℝ) ^ 2 := by rw [div_pow, hcsq]
    calc _ = |Real.log ((1 - c / p) / (1 + c / p)) + 2 * (c / p)| := by ring_nf
      _ ≤ 4 * (c / p) ^ 2 := this
      _ = 4 / (p : ℝ) ^ 2 := by rw [hu2]; ring

/-- If `p ≡ a (mod 2 ^ m)` with `m ≥ 2`, then `χ₄(p) = χ₄(a)`. -/
private lemma chi4_natCast_eq_of_natCast_eq {m p : ℕ} (hm : 2 ≤ m) {a : ZMod (2 ^ m)}
    (h : (p : ZMod (2 ^ m)) = a) :
    ZMod.χ₄ (p : ZMod 4) = ZMod.χ₄ ((a.val : ℕ) : ZMod 4) := by
  subst h
  have h4 : 4 ∣ 2 ^ m := by
    have := pow_dvd_pow 2 hm
    simpa using this
  rw [ZMod.val_natCast, (ZMod.natCast_eq_natCast_iff' _ _ 4).mpr (Nat.mod_mod_of_dvd p h4)]

end ThinnedWallisPrimeProduct

open ThinnedWallisPrimeProduct

/-- **Convergence of thinned Wallis-type prime products.** Let $m \ge 2$, let $q = 2^m$, and let
$S$ be a set of units of $\mathbb{Z}/q\mathbb{Z}$. Let $\chi_4$ be the nontrivial Dirichlet
character modulo $4$, put $\mu(S) = \sum_{a \in S} \chi_4(a)$, where $\chi_4(a)$ means $\chi_4$ of
the reduction of $a$ modulo $4$, and for real $x$ let
$$P_S(x) = \prod_{p \le x,\ p \bmod q \in S} \frac{p - \chi_4(p)}{p + \chi_4(p)},$$
the product running over primes $p$. Then $P_S(x)$ converges as $x \to \infty$ to a positive real
limit if and only if $\mu(S) = 0$.

Source: Mike Winkler, *Thinned Wallis-Type Prime Products in Residue Classes Modulo 2^m*,
INTEGERS 26 (2026), Article A90, Corollary 1 (`integers-2026-A90-cor-1`). -/
public theorem thinned_wallis_prime_product_tendsto_pos_iff
    (m : ℕ) (hm : 2 ≤ m) (S : Finset (ZMod (2 ^ m))) (hS : ∀ a ∈ S, IsUnit a) :
    (∃ L : ℝ, 0 < L ∧
        Tendsto (fun x : ℝ =>
            ∏ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter
                (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) ∈ S),
              ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4)))
          atTop (𝓝 L)) ↔
      ∑ a ∈ S, ZMod.χ₄ ((a.val : ℕ) : ZMod 4) = 0 := by
  -- The primes in the product are odd.
  have hodd : ∀ p : ℕ, p.Prime ∧ (p : ZMod (2 ^ m)) ∈ S → Odd p := fun p hp =>
    odd_of_isUnit_natCast (by omega) (hS _ hp.2)
  -- The partial products and their logarithms.
  set P : ℕ → ℝ := fun N => ∏ p ∈ (Finset.range N).filter
      (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) ∈ S),
    ((p : ℝ) - ZMod.χ₄ (p : ZMod 4)) / ((p : ℝ) + ZMod.χ₄ (p : ZMod 4)) with hP
  have hPpos : ∀ N, 0 < P N := fun N => Finset.prod_pos fun p hp =>
    (factor_pos_and_abs_log_add_le (Finset.mem_filter.mp hp).2.1
      (hodd p (Finset.mem_filter.mp hp).2)).1
  -- The error terms of the logarithms.
  set E : ℕ → ℝ := fun n => if n.Prime ∧ (n : ZMod (2 ^ m)) ∈ S then
      Real.log (((n : ℝ) - ZMod.χ₄ (n : ZMod 4)) / ((n : ℝ) + ZMod.χ₄ (n : ZMod 4))) +
        2 * ((ZMod.χ₄ (n : ZMod 4) : ℤ) : ℝ) / n
    else 0 with hE
  have hEsum : Summable E := by
    refine Summable.of_norm_bounded
      ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left 4) fun n => ?_
    simp only [hE, Real.norm_eq_abs]
    split_ifs with hn
    · simpa [div_eq_mul_inv] using (factor_pos_and_abs_log_add_le hn.1 (hodd n hn)).2
    · simp only [abs_zero]
      positivity
  -- The characters of the residue classes.
  set χ : ZMod (2 ^ m) → ℝ := fun a => ((ZMod.χ₄ ((a.val : ℕ) : ZMod 4) : ℤ) : ℝ) with hχ
  set μ : ℤ := ∑ a ∈ S, ZMod.χ₄ ((a.val : ℕ) : ZMod 4) with hμ
  have hμR : (μ : ℝ) = ∑ a ∈ S, χ a := by simp [hμ, hχ]
  -- The differences of the prime reciprocal sums.
  choose! ℓ hℓ using fun a (ha : a ∈ S) =>
    exists_tendsto_recipSum_sub (hS a ha) (isUnit_one : IsUnit (1 : ZMod (2 ^ m)))
  set G : ℕ → ℝ := fun N => ∑ a ∈ S, χ a * (recipSum a N - recipSum (1 : ZMod (2 ^ m)) N)
    with hG
  have hGlim : Tendsto G atTop (𝓝 (∑ a ∈ S, χ a * ℓ a)) :=
    tendsto_finsetSum S fun a ha => (hℓ a ha).const_mul (χ a)
  have hRlim : Tendsto (fun N => ∑ n ∈ Finset.range N, E n) atTop (𝓝 (∑' n, E n)) :=
    hEsum.hasSum.tendsto_sum_nat
  -- The logarithm of the partial products.
  have hlog : ∀ N, Real.log (P N) =
      -2 * (G N + μ * recipSum (1 : ZMod (2 ^ m)) N) + ∑ n ∈ Finset.range N, E n := by
    intro N
    have hdec : ∑ p ∈ (Finset.range N).filter (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) ∈ S),
        ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℝ) / p = ∑ a ∈ S, χ a * recipSum a N := by
      rw [← Finset.sum_fiberwise_of_maps_to (t := S) (g := fun p : ℕ => (p : ZMod (2 ^ m)))
        (fun p hp => (Finset.mem_filter.mp hp).2.2)]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [recipSum, Finset.mul_sum, Finset.filter_filter]
      have hfil : (Finset.range N).filter (fun p : ℕ =>
          (p.Prime ∧ (p : ZMod (2 ^ m)) ∈ S) ∧ (p : ZMod (2 ^ m)) = a) =
          (Finset.range N).filter (fun p : ℕ => p.Prime ∧ (p : ZMod (2 ^ m)) = a) := by
        apply Finset.filter_congr
        intro p _
        constructor
        · rintro ⟨⟨hp, _⟩, h⟩
          exact ⟨hp, h⟩
        · rintro ⟨hp, h⟩
          exact ⟨⟨hp, h ▸ ha⟩, h⟩
      rw [hfil]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [chi4_natCast_eq_of_natCast_eq hm (Finset.mem_filter.mp hp).2.2]
      simp [hχ, div_eq_mul_inv]
    have hsplit : ∑ a ∈ S, χ a * recipSum a N = G N + μ * recipSum (1 : ZMod (2 ^ m)) N := by
      rw [hμR, hG, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [hP, Real.log_prod (fun p hp => (factor_pos_and_abs_log_add_le
      (Finset.mem_filter.mp hp).2.1 (hodd p (Finset.mem_filter.mp hp).2)).1.ne'),
      ← hsplit, ← hdec, Finset.mul_sum, hE, ← Finset.sum_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  constructor
  · rintro ⟨L, hL, hT⟩
    by_contra hμ0
    have hμ0' : (μ : ℝ) ≠ 0 := by exact_mod_cast hμ0
    have hseq : Tendsto (fun N : ℕ => P (N + 1)) atTop (𝓝 L) := by
      refine (hT.comp tendsto_natCast_atTop_atTop).congr fun N => ?_
      simp only [Function.comp, Nat.floor_natCast, hP]
    have hconv : Tendsto (fun N : ℕ => recipSum (1 : ZMod (2 ^ m)) (N + 1)) atTop
        (𝓝 (((-(1 / 2)) * (Real.log L - ∑' n, E n) - ∑ a ∈ S, χ a * ℓ a) / μ)) := by
      have h1 := (((hseq.log hL.ne').sub (hRlim.comp (tendsto_add_atTop_nat 1))).const_mul
        (-(1 / 2))).sub (hGlim.comp (tendsto_add_atTop_nat 1))
      refine (h1.div_const (μ : ℝ)).congr fun N => ?_
      simp only [Function.comp]
      rw [hlog (N + 1)]
      field_simp
      ring
    exact not_tendsto_nhds_of_tendsto_atTop
      ((tendsto_recipSum_atTop isUnit_one).comp (tendsto_add_atTop_nat 1)) _ hconv
  · intro hμ0
    have hμ0' : (μ : ℝ) = 0 := by exact_mod_cast hμ0
    refine ⟨Real.exp (-2 * ∑ a ∈ S, χ a * ℓ a + ∑' n, E n), Real.exp_pos _, ?_⟩
    have hseq : Tendsto P atTop
        (𝓝 (Real.exp (-2 * ∑ a ∈ S, χ a * ℓ a + ∑' n, E n))) := by
      refine (((hGlim.const_mul (-2)).add hRlim).rexp).congr fun N => ?_
      rw [← Real.exp_log (hPpos N), hlog N, hμ0']
      ring_nf
    exact hseq.comp ((tendsto_add_atTop_nat 1).comp tendsto_nat_floor_atTop)

end MetaMathlibExt
