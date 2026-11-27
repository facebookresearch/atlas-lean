/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SuperMZumkeller
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Finset.Image
import Mathlib.NumberTheory.Divisors

/-! # Super-m-Zumkeller prime powers

This module characterizes the super-m-Zumkeller prime powers: for a prime `p` and `a ≥ 1`,
`p ^ a` is super-m-Zumkeller if and only if `a % 16 ∈ {0, 2, 5, 7, 8, 10, 13, 15}`
(`isSuperMZumkeller_prime_pow_iff`). All auxiliary lemmas are private.

Statements from Harish Patodia, "Super m-Zumkeller Numbers", *INTEGERS* 26 (2026),
Article A79 (<https://math.colgate.edu/~integers/aa79/aa79.pdf>),
DOI `10.5281/zenodo.20931172`.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.SuperMZumkellerWanted

private theorem divisorProd_prime_pow (p a : ℕ) (hp : p.Prime) :
    divisorProd (p ^ a) = p ^ (a * (a + 1) / 2) := by
  unfold divisorProd
  rw [Nat.prod_divisors_prime_pow hp, Finset.prod_pow_eq_pow_sum, Finset.sum_range_id,
    Nat.add_sub_cancel, mul_comm (a + 1) a]

private theorem exists_subset_half_sum_step (N : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range N) (hsum : 2 * ∑ i ∈ S, i = ∑ i ∈ Finset.range N, i) :
    ∃ S' : Finset ℕ, S' ⊆ Finset.range (N + 4) ∧
      2 * ∑ i ∈ S', i = ∑ i ∈ Finset.range (N + 4), i := by
  have h4 : ∑ i ∈ Finset.range (N + 4), i = ∑ i ∈ Finset.range N, i + (4 * N + 6) := by
    have e1 : N + 4 = (N + 3) + 1 := by omega
    have e2 : N + 3 = (N + 2) + 1 := by omega
    have e3 : N + 2 = (N + 1) + 1 := by omega
    rw [e1, Finset.sum_range_succ, e2, Finset.sum_range_succ, e3, Finset.sum_range_succ,
      Finset.sum_range_succ]
    omega
  have hdisj : Disjoint S {N, N + 3} := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    have hNx : x < N := Finset.mem_range.mp (hS hx)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
    omega
  have hNmem : N ∉ ({N + 3} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    omega
  refine ⟨S ∪ {N, N + 3}, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_range] at hx ⊢
    rcases hx with hx | rfl | rfl
    · have hNx : x < N := Finset.mem_range.mp (hS hx)
      omega
    · omega
    · omega
  · rw [Finset.sum_union hdisj, Finset.sum_insert hNmem, Finset.sum_singleton, h4]
    omega

private theorem exists_subset_half_sum_mod0 (m : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.range (4 * m + 1) ∧
      2 * ∑ i ∈ S, i = ∑ i ∈ Finset.range (4 * m + 1), i := by
  induction m with
  | zero =>
    refine ⟨∅, Finset.empty_subset _, ?_⟩
    decide
  | succ m ih =>
    obtain ⟨S, hS, hsum⟩ := ih
    have hN : 4 * (m + 1) + 1 = (4 * m + 1) + 4 := by omega
    rw [hN]
    exact exists_subset_half_sum_step (4 * m + 1) S hS hsum

private theorem exists_subset_half_sum_mod3 (m : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.range (4 * m + 4) ∧
      2 * ∑ i ∈ S, i = ∑ i ∈ Finset.range (4 * m + 4), i := by
  induction m with
  | zero =>
    refine ⟨{1, 2}, by decide, by decide⟩
  | succ m ih =>
    obtain ⟨S, hS, hsum⟩ := ih
    have hN : 4 * (m + 1) + 4 = (4 * m + 4) + 4 := by omega
    rw [hN]
    exact exists_subset_half_sum_step (4 * m + 4) S hS hsum

private theorem emod4_of_four_dvd (e : ℕ) (h : 4 ∣ e * (e + 1)) :
    e % 4 = 0 ∨ e % 4 = 3 := by
  have hlt : e % 4 < 4 := Nat.mod_lt _ (by decide)
  have hmod : (e * (e + 1)) % 4 = 0 := by
    obtain ⟨k, hk⟩ := h
    omega
  rw [Nat.mul_mod, Nat.add_mod, show (1 : ℕ) % 4 = 1 from rfl] at hmod
  have hcases : e % 4 = 0 ∨ e % 4 = 1 ∨ e % 4 = 2 ∨ e % 4 = 3 := by omega
  rcases hcases with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · rw [h1] at hmod
    exact absurd hmod (by decide)
  · rw [h1] at hmod
    exact absurd hmod (by decide)
  · exact Or.inr h1

private theorem emod4_iff_amod8 (a e : ℕ) (h2e : 2 * e = a * (a + 1)) :
    (e % 4 = 0 ∨ e % 4 = 3) ↔ a % 8 ∈ ({0, 2, 5, 7} : Finset ℕ) := by
  have h88 : (a * (a + 1)) % 8 = ((a % 8) * (((a % 8) + 1) % 8)) % 8 := by
    rw [Nat.mul_mod, Nat.add_mod, show (1 : ℕ) % 8 = 1 from rfl]
  have h2e8 : (2 * e) % 8 = (a * (a + 1)) % 8 := by rw [h2e]
  constructor
  · intro he
    have h68 : (2 * e) % 8 = 0 ∨ (2 * e) % 8 = 6 := by
      rcases he with he | he <;> omega
    rw [h2e8, h88] at h68
    have hlt : a % 8 < 8 := Nat.mod_lt _ (by decide)
    have hcases : a % 8 = 0 ∨ a % 8 = 1 ∨ a % 8 = 2 ∨ a % 8 = 3 ∨ a % 8 = 4 ∨
      a % 8 = 5 ∨ a % 8 = 6 ∨ a % 8 = 7 := by omega
    rcases hcases with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 <;> rw [h1] at h68 ⊢
    · decide
    · exact absurd h68 (by decide)
    · decide
    · exact absurd h68 (by decide)
    · exact absurd h68 (by decide)
    · decide
    · exact absurd h68 (by decide)
    · decide
  · intro ha
    have h68 : ((a % 8) * (((a % 8) + 1) % 8)) % 8 = 0 ∨
        ((a % 8) * (((a % 8) + 1) % 8)) % 8 = 6 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with h1 | h1 | h1 | h1 <;> rw [h1] <;> decide
    rw [← h88, ← h2e8] at h68
    omega

private theorem amod16_iff_amod8 (a : ℕ) :
    a % 16 ∈ ({0, 2, 5, 7, 8, 10, 13, 15} : Finset ℕ) ↔
      a % 8 ∈ ({0, 2, 5, 7} : Finset ℕ) := by
  have h168 : a % 16 % 8 = a % 8 := Nat.mod_mod_of_dvd a (by decide)
  rw [← h168]
  have hlt : a % 16 < 16 := Nat.mod_lt _ (by decide)
  have hcases : a % 16 = 0 ∨ a % 16 = 1 ∨ a % 16 = 2 ∨ a % 16 = 3 ∨ a % 16 = 4 ∨
      a % 16 = 5 ∨ a % 16 = 6 ∨ a % 16 = 7 ∨ a % 16 = 8 ∨ a % 16 = 9 ∨
      a % 16 = 10 ∨ a % 16 = 11 ∨ a % 16 = 12 ∨ a % 16 = 13 ∨ a % 16 = 14 ∨
      a % 16 = 15 := by omega
  rcases hcases with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 |
      h1 | h1 | h1 | h1 <;>
    rw [h1] <;> decide

private theorem exists_subset_prod_eq_of_half_sum (p e : ℕ) (hp : p.Prime)
    (S : Finset ℕ) (hSsub : S ⊆ Finset.range (e + 1))
    (hsum : 2 * ∑ i ∈ S, i = ∑ i ∈ Finset.range (e + 1), i) :
    ∃ A : Finset ℕ, A ⊆ (p ^ e).divisors ∧
      (∏ d ∈ A, d) = ∏ d ∈ (p ^ e).divisors \ A, d := by
  have hdiv : (p ^ e).divisors =
      (Finset.range (e + 1)).map ⟨(p ^ ·), Nat.pow_right_injective hp.two_le⟩ :=
    Nat.divisors_prime_pow hp e
  rw [hdiv]
  refine ⟨S.map ⟨(p ^ ·), Nat.pow_right_injective hp.two_le⟩,
    Finset.map_subset_map.mpr hSsub, ?_⟩
  rw [← Finset.map_sdiff, Finset.prod_map, Finset.prod_map]
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]
  congr 1
  have hsd : ∑ i ∈ Finset.range (e + 1) \ S, i + ∑ i ∈ S, i =
      ∑ i ∈ Finset.range (e + 1), i :=
    Finset.sum_sdiff hSsub
  omega

/-- **Super-m-Zumkeller prime powers.** Let $p$ be a prime and $\alpha \ge 1$ an integer. Then
$p^\alpha$ is super-m-Zumkeller if and only if
$\alpha \equiv 0, 2, 5, 7, 8, 10, 13$ or $15 \pmod{16}$.

Source: Harish Patodia, "Super m-Zumkeller Numbers", Theorem 3. -/
theorem isSuperMZumkeller_prime_pow_iff (p : ℕ)
    (hp : p.Prime) (a : ℕ) (ha : 1 ≤ a) :
    IsSuperMZumkeller (p ^ a) ↔
      a % 16 ∈ ({0, 2, 5, 7, 8, 10, 13, 15} : Finset ℕ) := by
  have hapos : 0 < a := ha
  have hT : divisorProd (p ^ a) = p ^ (a * (a + 1) / 2) := divisorProd_prime_pow p a hp
  have h2e : 2 * (a * (a + 1) / 2) = a * (a + 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self a)
  set e := a * (a + 1) / 2 with hedef
  constructor
  · intro h
    obtain ⟨A, hAsub, hprod⟩ := h
    rw [hT] at hAsub hprod
    have hdiv : (p ^ e).divisors =
        (Finset.range (e + 1)).map ⟨(p ^ ·), Nat.pow_right_injective hp.two_le⟩ :=
      Nat.divisors_prime_pow hp e
    rw [hdiv] at hAsub
    set S : Finset ℕ := (Finset.range (e + 1)).filter (fun i => p ^ i ∈ A) with hSdef
    have hSsub : S ⊆ Finset.range (e + 1) := Finset.filter_subset _ _
    have hAS : A = Finset.map ⟨(p ^ ·), Nat.pow_right_injective hp.two_le⟩ S := by
      ext x
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk, hSdef, Finset.mem_filter]
      constructor
      · intro hxA
        have hxmap := hAsub hxA
        rw [Finset.mem_map, Function.Embedding.coeFn_mk] at hxmap
        obtain ⟨i, hi, rfl⟩ := hxmap
        exact ⟨i, ⟨hi, hxA⟩, rfl⟩
      · rintro ⟨i, ⟨hi, hpiA⟩, rfl⟩
        exact hpiA
    have hprodA : ∏ d ∈ A, d = p ^ (∑ i ∈ S, i) := by
      rw [hAS, Finset.prod_map]
      simp only [Function.Embedding.coeFn_mk]
      exact Finset.prod_pow_eq_pow_sum S (fun i => i) p
    have hprodC : ∏ d ∈ (p ^ e).divisors \ A, d =
        p ^ (∑ i ∈ Finset.range (e + 1) \ S, i) := by
      rw [hdiv, hAS, ← Finset.map_sdiff, Finset.prod_map]
      simp only [Function.Embedding.coeFn_mk]
      exact Finset.prod_pow_eq_pow_sum _ _ _
    rw [hprodA, hprodC] at hprod
    have hexp : ∑ i ∈ S, i = ∑ i ∈ Finset.range (e + 1) \ S, i :=
      Nat.pow_right_injective hp.two_le hprod
    have hsum2 : 2 * ∑ i ∈ S, i = ∑ i ∈ Finset.range (e + 1), i := by
      have hsd : ∑ i ∈ Finset.range (e + 1) \ S, i + ∑ i ∈ S, i =
          ∑ i ∈ Finset.range (e + 1), i :=
        Finset.sum_sdiff hSsub
      omega
    rw [Finset.sum_range_id, Nat.add_sub_cancel] at hsum2
    have hdvd : 4 ∣ e * (e + 1) := by
      have heven : Even ((e + 1) * e) := by
        have h := Nat.even_mul_succ_self e
        rwa [mul_comm e (e + 1)] at h
      have h2 := Nat.two_mul_div_two_of_even heven
      have h4 : (e + 1) * e = 4 * ∑ i ∈ S, i := by omega
      rw [mul_comm (e + 1) e] at h4
      exact ⟨∑ i ∈ S, i, h4⟩
    have he4 := emod4_of_four_dvd e hdvd
    have ha8 := (emod4_iff_amod8 a e h2e).mp he4
    exact (amod16_iff_amod8 a).mpr ha8
  · intro ha16
    have ha8 := (amod16_iff_amod8 a).mp ha16
    have he4 := (emod4_iff_amod8 a e h2e).mpr ha8
    unfold IsSuperMZumkeller
    rw [hT]
    rcases he4 with he4 | he4
    · have heq : e = 4 * (e / 4) := by omega
      obtain ⟨S, hSsub, hsum⟩ := exists_subset_half_sum_mod0 (e / 4)
      rw [← heq] at hSsub hsum
      exact exists_subset_prod_eq_of_half_sum p e hp S hSsub hsum
    · have heq : e + 1 = 4 * (e / 4) + 4 := by omega
      obtain ⟨S, hSsub, hsum⟩ := exists_subset_half_sum_mod3 (e / 4)
      rw [← heq] at hSsub hsum
      exact exists_subset_prod_eq_of_half_sum p e hp S hSsub hsum

end MathlibExt.NumberTheory.SuperMZumkellerWanted
