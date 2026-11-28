/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PracticalNumber
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Prime.Basic

/-!
# Products of a practical number with small factors

The product `m * n` of a practical number `m` with a factor `1 ≤ n ≤ σ(m) + 1` is practical.

Statements from Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and
Polygonal Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1
(arXiv:2403.13533). In the paper "natural number" means positive integer; practical numbers
are `MetaMathlibExt.IsPracticalNumber`. The paper proves the result by citing M. Margenstern,
*Les nombres pratiques: théorie, observations et conjectures*, J. Number Theory 37 (1991), 1-36,
Corollary 1.
-/

namespace MetaMathlibExt

open ArithmeticFunction
open scoped BigOperators

private theorem subset_sum_of_le_sum (D : Finset ℕ) : ∀ M : ℕ,
    (∀ d ∈ D, 0 < d) → (∀ d ∈ D, d ≤ M) →
    (∀ k, 1 ≤ k → k ≤ M → ∃ S : Finset ℕ, S ⊆ D ∧ ∑ x ∈ S, x = k) →
    ∀ k, k ≤ ∑ x ∈ D, x → ∃ S : Finset ℕ, S ⊆ D ∧ ∑ x ∈ S, x = k := by
  induction D using Finset.strongInduction with
  | _ D ih =>
    intro M hpos hle hrep k hk
    by_cases hk0 : k = 0
    · exact ⟨∅, Finset.empty_subset _, by simp [hk0]⟩
    · have hk1 : 1 ≤ k := by omega
      by_cases hDne : D.Nonempty
      · have haD : D.max' hDne ∈ D := Finset.max'_mem D hDne
        have hsum : ∑ x ∈ D, x = D.max' hDne + ∑ x ∈ D.erase (D.max' hDne), x :=
          (Finset.add_sum_erase D _ haD).symm
        rw [hsum] at hk
        have hIH : ∀ j, j ≤ ∑ x ∈ D.erase (D.max' hDne), x →
            ∃ S : Finset ℕ, S ⊆ D.erase (D.max' hDne) ∧ ∑ x ∈ S, x = j := by
          by_cases hEne : (D.erase (D.max' hDne)).Nonempty
          · have hbE : (D.erase (D.max' hDne)).max' hEne ∈ D.erase (D.max' hDne) :=
              Finset.max'_mem _ hEne
            have hlt : (D.erase (D.max' hDne)).max' hEne < D.max' hDne := by
              have hne := Finset.ne_of_mem_erase hbE
              have hle' : (D.erase (D.max' hDne)).max' hEne ≤ D.max' hDne :=
                Finset.le_max' D _ (Finset.erase_subset _ _ hbE)
              omega
            intro j hj
            exact ih _ (Finset.erase_ssubset haD) ((D.erase (D.max' hDne)).max' hEne)
              (fun d hd => hpos d (Finset.erase_subset _ _ hd))
              (fun d hd => Finset.le_max' _ d hd)
              (fun l hl1 hlM => by
                obtain ⟨S, hSsub, hSsum⟩ := hrep l hl1
                  (hlM.trans (hle _ (Finset.erase_subset _ _ hbE)))
                refine ⟨S, Finset.subset_erase.mpr ⟨hSsub, ?_⟩, hSsum⟩
                intro haS
                have hle'' : D.max' hDne ≤ ∑ x ∈ S, x :=
                  Finset.single_le_sum (fun i _ => Nat.zero_le i) haS
                omega)
              j hj
          · have hE0 := Finset.not_nonempty_iff_eq_empty.mp hEne
            intro j hj
            rw [hE0, Finset.sum_empty] at hj
            have hj0 : j = 0 := by omega
            exact ⟨∅, Finset.empty_subset _, by simp [hj0]⟩
        by_cases hSle : k ≤ ∑ x ∈ D.erase (D.max' hDne), x
        · obtain ⟨S, hSsub, hSsum⟩ := hIH k hSle
          exact ⟨S, hSsub.trans (Finset.erase_subset _ _), hSsum⟩
        · push Not at hSle
          by_cases hkM : k ≤ M
          · exact hrep k hk1 hkM
          · push Not at hkM
            have haM : D.max' hDne ≤ M := hle _ haD
            have ha0 : 0 < D.max' hDne := hpos _ haD
            have hka1 : 1 ≤ k - D.max' hDne := by omega
            have hkaS : k - D.max' hDne ≤ ∑ x ∈ D.erase (D.max' hDne), x := by omega
            obtain ⟨S0, hS0sub, hS0sum⟩ := hIH _ hkaS
            have haS0 : D.max' hDne ∉ S0 :=
              fun h => Finset.notMem_erase _ _ (hS0sub h)
            refine ⟨insert (D.max' hDne) S0, ?_, ?_⟩
            · intro y hy
              simp only [Finset.mem_insert] at hy
              rcases hy with rfl | hy
              · exact haD
              · exact Finset.erase_subset _ _ (hS0sub hy)
            · simp only [Finset.sum_insert haS0, hS0sum]
              omega
      · have hD0 := Finset.not_nonempty_iff_eq_empty.mp hDne
        subst hD0
        rw [Finset.sum_empty] at hk
        omega

/-- A positive natural number is at most the sum of its positive divisors. -/
public theorem le_sigma_one (m : ℕ) (hm : 0 < m) : m ≤ sigma 1 m := by
  rw [sigma_one_apply]
  exact Finset.single_le_sum (fun i _ => Nat.zero_le i)
    (Nat.mem_divisors_self m (by omega))

private theorem sigma_one_le_of_dvd (m n : ℕ) (hn : n ≠ 0) (h : m ∣ n) :
    sigma 1 m ≤ sigma 1 n := by
  rw [sigma_one_apply, sigma_one_apply]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Nat.divisors_subset_of_dvd hn h)
    (fun i _ _ => Nat.zero_le i)

private theorem isPracticalNumber_mul_prime_of_le_sigma_add_one (m p : ℕ)
    (hm : IsPracticalNumber m) (hp : p.Prime) (hpm : p ≤ sigma 1 m + 1) :
    IsPracticalNumber (m * p) := by
  obtain ⟨hmpos, hrep⟩ := hm
  have hppos : 0 < p := hp.pos
  have hmppos : 0 < m * p := mul_pos hmpos hppos
  have hσ : sigma 1 m = ∑ x ∈ m.divisors, x := sigma_one_apply m
  have hext := subset_sum_of_le_sum m.divisors m
    (fun d hd => Nat.pos_of_mem_divisors hd)
    (fun d hd => Nat.le_of_dvd hmpos (Nat.dvd_of_mem_divisors hd)) hrep
  refine ⟨hmppos, fun t ht1 htmp => ?_⟩
  have hdiv : p * (t / p) + t % p = t := Nat.div_add_mod t p
  have hrlt : t % p < p := Nat.mod_lt t hppos
  have hqle : t / p ≤ m := by
    have h := Nat.div_le_div_right (c := p) htmp
    rwa [Nat.mul_div_cancel m hppos] at h
  have hrS : t % p ≤ ∑ x ∈ m.divisors, x := by
    rw [← hσ]
    omega
  have hqS : t / p ≤ ∑ x ∈ m.divisors, x := by
    rw [← hσ]
    exact hqle.trans (le_sigma_one m hmpos)
  obtain ⟨S1, hS1sub, hS1sum⟩ := hext _ hrS
  obtain ⟨S2, hS2sub, hS2sum⟩ := hext _ hqS
  have hmpne : m * p ≠ 0 := mul_ne_zero (by omega) (by omega)
  have hsub1 : S1 ⊆ (m * p).divisors :=
    hS1sub.trans (Nat.divisors_subset_of_dvd hmpne ⟨p, rfl⟩)
  have himg : ∀ d ∈ S2, p * d ∈ (m * p).divisors := by
    intro d hd
    obtain ⟨k, hk⟩ := Nat.dvd_of_mem_divisors (hS2sub hd)
    refine Nat.mem_divisors.mpr ⟨⟨k, ?_⟩, hmpne⟩
    rw [hk]
    ring
  have hdisj : Disjoint S1 (S2.image (p * ·)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨d, hdS2, rfl⟩ := Finset.mem_image.mp hx2
    have hxle : p * d ≤ t % p := by
      have hle0 : p * d ≤ ∑ x ∈ S1, x :=
        Finset.single_le_sum (fun i _ => Nat.zero_le i) hx1
      rwa [hS1sum] at hle0
    have hdpos : 0 < d := Nat.pos_of_mem_divisors (hS2sub hdS2)
    have hle : p ≤ p * d := Nat.le_mul_of_pos_right p hdpos
    omega
  have hinj : Set.InjOn (p * ·) ↑S2 := by
    intro d1 _ d2 _ heq
    exact mul_left_cancel₀ (ne_of_gt hppos) heq
  have himg_sum : ∑ x ∈ S2.image (p * ·), x = p * (t / p) := by
    rw [Finset.sum_image hinj, ← Finset.mul_sum, hS2sum]
  refine ⟨S1 ∪ S2.image (p * ·), Finset.union_subset hsub1 ?_, ?_⟩
  · intro y hy
    obtain ⟨d, hdS2, rfl⟩ := Finset.mem_image.mp hy
    exact himg d hdS2
  · rw [Finset.sum_union hdisj, hS1sum, himg_sum]
    omega

private theorem isPracticalNumber_mul_of_le_sigma_add_one_aux :
    ∀ n m : ℕ, IsPracticalNumber m → 0 < n → n ≤ sigma 1 m + 1 →
    IsPracticalNumber (m * n) := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih m hm hn hnm
  by_cases hn1 : n = 1
  · subst hn1
    rw [mul_one]
    exact hm
  · by_cases hnp : n.Prime
    · exact isPracticalNumber_mul_prime_of_le_sigma_add_one m n hm hnp hnm
    · obtain ⟨d, hdvd, hd2, hdlt⟩ := Nat.exists_dvd_of_not_prime2 (by omega) hnp
      obtain ⟨k, rfl⟩ := hdvd
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with rfl | h
        · simp at hn
        · exact h
      have hklt : k < d * k := lt_mul_of_one_lt_left hkpos (by omega)
      have hdm : IsPracticalNumber (m * d) :=
        ih d hdlt m hm (by omega) (by omega)
      have hσle : sigma 1 m ≤ sigma 1 (m * d) :=
        sigma_one_le_of_dvd m (m * d)
          (mul_ne_zero (ne_of_gt hm.1) (ne_of_gt (by omega : 0 < d))) ⟨d, rfl⟩
      have hfinal : IsPracticalNumber (m * d * k) :=
        ih k hklt (m * d) hdm hkpos (by omega)
      rwa [mul_assoc] at hfinal

/-- **Products of a practical number with small factors.** Let $m$ be a practical number and let
$\sigma(m)$ denote the sum of the positive divisors of $m$. Then for every natural number $n$
with $1 \le n \le \sigma(m) + 1$, the product $mn$ is a practical number.

Source: Sai Teja Somu and Duc Van Khanh Tran, *On Sums of Practical Numbers and Polygonal
Numbers*, Journal of Integer Sequences 27 (2024), Article 24.5.1, Lemma 4
(arXiv Lemma 3.2; `jis-2024-24.5.1-lem-4`), quoting Margenstern. -/
public theorem isPracticalNumber_mul_of_le_sigma_add_one (m n : ℕ)
    (hm : IsPracticalNumber m) (hn : 0 < n) (hnm : n ≤ sigma 1 m + 1) :
    IsPracticalNumber (m * n) :=
  isPracticalNumber_mul_of_le_sigma_add_one_aux n m hm hn hnm

end MetaMathlibExt
