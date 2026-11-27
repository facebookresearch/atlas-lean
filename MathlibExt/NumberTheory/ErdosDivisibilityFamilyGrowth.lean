/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Sym.Card
import Mathlib.NumberTheory.LSeries.WeakPNT

@[expose] public section

/-!
# Erdős Problem 793: growth of the largest 2-primitive family

Let `F(n)` be the maximum size of a set `A ⊆ {1, …, n}` such that
no element divides the product of two others: `¬ a ∣ b * c`
whenever `a, b, c ∈ A` with `a ≠ b` and `a ≠ c`.
Is there a constant `C` with
`F(n) = π(n) + (C + o(1)) * n^(2/3) / (log n)^2`?

This file proves that the answer is yes, with `C = 27 / 2` (`conjecture_holds`), following
Chojecki (2026, Theorem 1.1).

## Proof outline

Write `S = n ^ (2/3) / (log n) ^ 2`.

* Upper bound (Erdős's multiplicative basis). If every element `a = u * v` of a good set `A`
  is a product of two members of a set `B`, then `u` or `v` divides no other element of `A`,
  so `#A ≤ #B`. Every `m ≤ n` is such a product for the basis formed by the integers up to
  `n ^ (3/5)`, the primes up to `n`, the products of two primes up to `n ^ (1/3)`, and the
  products `q * r` of primes with `n ^ (1/3) < q ≤ n ^ (2/5)` and `r ≤ n / q ^ 2`. By the prime
  number theorem the last two families have at most `(9/2 + o(1)) S` and `(9 + o(1)) S`
  elements.
* Lower bound (linear prime triples). Split the primes near `n ^ (1/3)` into bins
  `(t ^ r n ^ (1/3), t ^ (r + 1) n ^ (1/3)]`. For bins `i < j` with `i + 2 j ≤ -4`, a
  Latin-square colouring of the pairs of primes from bins `i` and `j` by the primes of bin
  `k = -3 - i - j` gives triples `{p, q, r}` with `p q r ≤ n`, any two of which share at most one
  prime. The primes above all the bins, together with the triple products, form a good set.
  The number of triples is a geometric sum, which tends to `(27/2) S` as `t → 1`.

## Implementation notes

The thresholds `n ^ (1/5)`, `n ^ (2/5)` and `n ^ (3/5)` of the basis are encoded by fifth powers
in `ℕ`. The lower bound uses only the cells `(i, j)` with `i < j`: the diagonal cells of the
paper contribute a term that vanishes as `t → 1`, so the limit does not need them. A cell is
coloured by adding indices in `Fin m`, where `m` is the size of its third bin.

## References

* P. Chojecki, *The Second Term for Strongly 2-Primitive Sets*, arXiv:2607.15306 (2026).
-/

open Filter Asymptotics Finset
open scoped Topology

namespace MathlibExt.NumberTheory.ErdosDivisibilityFamilyGrowthWanted

/-! Source record `EP-793`. -/

/-- **Sets in which no element divides the product of two others.** A finite set $A$ of natural
numbers is good when every element of $A$ is positive and no $a \in A$ divides $bc$ for any
$b, c \in A$ with $a \ne b$ and $a \ne c$; here $b = c$ is allowed. -/
def Good (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → ¬ a ∣ b * c) ∧ (∀ a ∈ A, 1 ≤ a)

/-- **Maximum size of a good subset.** For a natural number $n$, $F(n)$ is the largest size of a
good subset of $\{1, \dots, n\}$, defined as the supremum of the sizes of the good sets
$A \subseteq \{1, \dots, n\}$. -/
noncomputable def F (n : ℕ) : ℕ :=
  sSup {k | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 n ∧ Good A ∧ A.card = k}

/-- **Statement of Erdős Problem 793.** For a natural number $n$, let $F(n)$ be the largest size
of a set $A \subseteq \{1, \dots, n\}$ with $a \nmid bc$ for all $a, b, c \in A$ such that
$a \ne b$ and $a \ne c$, and let $\pi(n)$ be the number of primes at most $n$. This is the
proposition that there is a real constant $C > 0$ such that
$(F(n) - \pi(n)) / (n^{2/3} / (\log n)^2) \to C$ as $n \to \infty$.
Equivalently, $F(n) = \pi(n) + (C + o(1))\, n^{2/3} / (\log n)^2$. -/
def conjecture : Prop :=
  ∃ C : ℝ, 0 < C ∧ Filter.Tendsto
    (fun n : ℕ => (((F n : ℤ) - (Nat.primeCounting n : ℤ)) : ℝ) /
      ((n : ℝ) ^ ((2 : ℝ) / 3) / (Real.log n) ^ 2))
    Filter.atTop (nhds C)

/-! ## Primes in intervals and the prime number theorem -/

/-- The primes in `(a, b]`. -/
private def primesIoc (a b : ℕ) : Finset ℕ := (Finset.Ioc a b).filter Nat.Prime

private theorem mem_primesIoc {a b p : ℕ} : p ∈ primesIoc a b ↔ a < p ∧ p ≤ b ∧ p.Prime := by
  simp [primesIoc, and_assoc]

/-- The number of primes in `(a, b]` is `π b - π a`. -/
private theorem card_primesIoc {a b : ℕ} (h : a ≤ b) :
    ((primesIoc a b).card : ℝ) = Nat.primeCounting b - Nat.primeCounting a := by
  have hdisj : Disjoint ((Finset.Ioc 0 a).filter Nat.Prime) (primesIoc a b) := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    rw [mem_primesIoc] at hp'
    omega
  have hunion : (Finset.Ioc 0 a).filter Nat.Prime ∪ primesIoc a b =
      (Finset.Ioc 0 b).filter Nat.Prime := by
    rw [primesIoc, ← Finset.filter_union, Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le a) h]
  have := Finset.card_union_of_disjoint hdisj
  rw [hunion, ← Nat.primesLE_eq_filter_Ioc_zero, ← Nat.primesLE_eq_filter_Ioc_zero,
    Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting] at this
  rw [this]
  push_cast
  ring

private theorem cbrt_pow_three (n : ℕ) : ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

private theorem cbrt_sq (n : ℕ) : ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 = (n : ℝ) ^ ((2 : ℝ) / 3) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

/-- **Prime number theorem at the scale `n ^ (1/3)`.** For `c > 0`,
`π (c n ^ (1/3)) / (n ^ (1/3) / log n) → 3 c`. -/
private theorem tendsto_primeCounting_floor_mul (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (Nat.primeCounting ⌊c * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) /
      ((n : ℝ) ^ ((1 : ℝ) / 3) / Real.log n)) atTop (𝓝 (3 * c)) := by
  have hpnt : Tendsto (fun x : ℝ => (Nat.primeCounting ⌊x⌋₊ : ℝ) / (x / Real.log x)) atTop
      (𝓝 1) := by
    have h := Nat.isEquivalent_primeCounting
    rw [isEquivalent_iff_tendsto_one] at h
    · exact h
    · filter_upwards [eventually_gt_atTop 1] with x hx
      exact div_ne_zero (by linarith) (Real.log_pos hx).ne'
  have hx : Tendsto (fun n : ℕ => c * (n : ℝ) ^ ((1 : ℝ) / 3)) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
  have h1 := hpnt.comp hx
  have hlog : Tendsto (fun n : ℕ => c * Real.log n / Real.log (c * (n : ℝ) ^ ((1 : ℝ) / 3)))
      atTop (𝓝 (3 * c)) := by
    have heq : ∀ᶠ n : ℕ in atTop, c * Real.log n / Real.log (c * (n : ℝ) ^ ((1 : ℝ) / 3)) =
        c / (Real.log c / Real.log n + 1 / 3) := by
      filter_upwards [eventually_gt_atTop 1] with n hn
      have hn' : (1 : ℝ) < n := by exact_mod_cast hn
      have hlogn : 0 < Real.log n := Real.log_pos hn'
      rw [Real.log_mul hc.ne' (by positivity), Real.log_rpow (by positivity)]
      field_simp
    rw [tendsto_congr' heq]
    have hl : Tendsto (fun n : ℕ => Real.log c / Real.log n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    convert tendsto_const_nhds.div (hl.add_const (1 / 3 : ℝ)) (by norm_num) using 2
    ring
  have h2 := h1.mul hlog
  rw [one_mul] at h2
  refine h2.congr' ?_
  filter_upwards [hx.eventually_gt_atTop 1, eventually_gt_atTop 1] with n hxn hn
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn
  have hlogn : 0 < Real.log n := Real.log_pos hn'
  have hy : 0 < (n : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have hlogx : 0 < Real.log (c * (n : ℝ) ^ ((1 : ℝ) / 3)) := Real.log_pos hxn
  simp only [Function.comp]
  field_simp

/-- The primes `q ≤ n` with `n < q ^ 3` and `q ^ 5 ≤ n ^ 2`. -/
private def bigPrimes (n : ℕ) : Finset ℕ :=
  (Finset.Iic n).filter fun q => q.Prime ∧ n < q ^ 3 ∧ q ^ 5 ≤ n ^ 2

/-- The prime bin `(t ^ r * n ^ (1/3), t ^ (r + 1) * n ^ (1/3)]`. -/
private noncomputable def bin (n : ℕ) (t : ℝ) (r : ℤ) : Finset ℕ :=
  primesIoc ⌊t ^ r * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ ⌊t ^ (r + 1) * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊

/-! ## The upper bound -/

/-! ### A good family is no larger than a multiplicative basis -/

/-- If every element of a good family `A` is a product of two elements of `B`, then
`#A ≤ #B`: each `a = u * v` has a factor `x ∈ {u, v}` dividing no other element of `A`,
and `a ↦ x` is injective. -/
private lemma upper_card_le_of_forall_eq_mul {A B : Finset ℕ} (hA : Good A)
    (hfac : ∀ a ∈ A, ∃ u ∈ B, ∃ v ∈ B, a = u * v) : A.card ≤ B.card := by
  have key : ∀ a, ∃ x, a ∈ A → x ∈ B ∧ x ∣ a ∧ ∀ b ∈ A, b ≠ a → ¬ x ∣ b := by
    intro a
    by_cases ha : a ∈ A
    · obtain ⟨u, hu, v, hv, rfl⟩ := hfac a ha
      by_cases h1 : ∃ b ∈ A, b ≠ u * v ∧ u ∣ b
      · obtain ⟨b, hb, hba, hub⟩ := h1
        refine ⟨v, fun _ => ⟨hv, dvd_mul_left v u, ?_⟩⟩
        intro c hc hca hvc
        exact hA.1 (u * v) ha b hb c hc (Ne.symm hba) (Ne.symm hca) (mul_dvd_mul hub hvc)
      · refine ⟨u, fun _ => ⟨hu, dvd_mul_right u v, ?_⟩⟩
        intro b hb hba hub
        exact h1 ⟨b, hb, hba, hub⟩
    · exact ⟨0, fun h => absurd h ha⟩
  choose g hg using key
  refine card_le_card_of_injOn g (fun a ha => (hg a ha).1) ?_
  intro a ha a' ha' h
  by_contra hne
  refine (hg a ha).2.2 a' ha' (Ne.symm hne) ?_
  rw [h]
  exact (hg a' ha').2.1

/-! ### The basis -/

/-- The integers `1 ≤ u ≤ n` with `u ^ 5 ≤ n ^ 3`, i.e. `u ≤ n ^ (3 / 5)`. -/
private def upper_smallSet (n : ℕ) : Finset ℕ := (Icc 1 n).filter fun u => u ^ 5 ≤ n ^ 3

/-- The products `p * q` of two primes `p, q ≤ n ^ (1 / 3)`. -/
private noncomputable def upper_cbrtPairs (n : ℕ) : Finset ℕ :=
  (Nat.primesLE ⌊(n : ℝ) ^ ((1 : ℝ) / 3)⌋₊).sym2.image
    (Sym2.lift ⟨fun p q => p * q, fun _ _ => mul_comm _ _⟩)

/-- The products `q * r` with `q ∈ bigPrimes n` and `r ≤ n / q ^ 2` prime. -/
private def upper_bigPairs (n : ℕ) : Finset ℕ :=
  (bigPrimes n).biUnion fun q => (Nat.primesLE (n / q ^ 2)).image (q * ·)

/-- The multiplicative basis: every `1 ≤ m ≤ n` is a product of two of its elements. -/
private noncomputable def upper_basis (n : ℕ) : Finset ℕ :=
  upper_smallSet n ∪ Nat.primesLE n ∪ upper_cbrtPairs n ∪ upper_bigPairs n

private lemma upper_mem_basis_of_pow_le {n u : ℕ} (hu1 : 1 ≤ u) (hun : u ≤ n)
    (hu : u ^ 5 ≤ n ^ 3) : u ∈ upper_basis n := by
  refine mem_union_left _ (mem_union_left _ (mem_union_left _ ?_))
  simp only [upper_smallSet, mem_filter, mem_Icc]
  exact ⟨⟨hu1, hun⟩, hu⟩

private lemma upper_mem_basis_of_prime {n p : ℕ} (hp : p.Prime) (hpn : p ≤ n) :
    p ∈ upper_basis n :=
  mem_union_left _ (mem_union_left _ (mem_union_right _ (Nat.mem_primesLE.mpr ⟨hpn, hp⟩)))

private lemma upper_le_floor_cbrt {n p : ℕ} (hp : p ^ 3 ≤ n) :
    p ≤ ⌊(n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := by
  apply Nat.le_floor
  by_contra h
  rw [not_le] at h
  have h3 : ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 < (p : ℝ) ^ 3 :=
    pow_lt_pow_left₀ h (by positivity) (by norm_num)
  rw [cbrt_pow_three] at h3
  have : (n : ℝ) < ((p ^ 3 : ℕ) : ℝ) := by push_cast; exact h3
  exact absurd hp (not_le.mpr (by exact_mod_cast this))

private lemma upper_mul_mem_basis_of_cube_le {n p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp3 : p ^ 3 ≤ n) (hq3 : q ^ 3 ≤ n) : p * q ∈ upper_basis n := by
  refine mem_union_left _ (mem_union_right _ ?_)
  simp only [upper_cbrtPairs, mem_image]
  refine ⟨s(p, q), mk_mem_sym2_iff.mpr ⟨?_, ?_⟩, rfl⟩
  · exact Nat.mem_primesLE.mpr ⟨upper_le_floor_cbrt hp3, hp⟩
  · exact Nat.mem_primesLE.mpr ⟨upper_le_floor_cbrt hq3, hq⟩

private lemma upper_mul_mem_basis_of_lt_cube {n q r : ℕ} (hq : q.Prime) (hq3 : n < q ^ 3)
    (hq5 : q ^ 5 ≤ n ^ 2) (hqn : q ≤ n) (hr : r.Prime) (hrq : r * q ^ 2 ≤ n) :
    q * r ∈ upper_basis n := by
  refine mem_union_right _ ?_
  simp only [upper_bigPairs, mem_biUnion, mem_image]
  refine ⟨q, ?_, r, ?_, rfl⟩
  · simp only [bigPrimes, mem_filter, mem_Iic]
    exact ⟨hqn, hq, hq3, hq5⟩
  · refine Nat.mem_primesLE.mpr ⟨?_, hr⟩
    exact (Nat.le_div_iff_mul_le (pow_pos hq.pos 2)).mpr hrq

/-! ### Every `1 ≤ m ≤ n` is a product of two basis elements -/

private lemma upper_pow_le_cube_of_mul_le {n x y : ℕ} (hxy : x * y ≤ n)
    (hx : n ^ 2 < x ^ 5) : y ^ 5 ≤ n ^ 3 := by
  by_contra h
  rw [not_le] at h
  have h1 : n ^ 2 * n ^ 3 < x ^ 5 * y ^ 5 := Nat.mul_lt_mul'' hx h
  have h2 : (x * y) ^ 5 ≤ n ^ 5 := Nat.pow_le_pow_left hxy 5
  rw [mul_pow] at h2
  have h3 : n ^ 2 * n ^ 3 = n ^ 5 := by ring
  omega

private lemma upper_pow_le_sq_of_mul_le {n x y : ℕ} (hxy : x * y ≤ n)
    (hy : n ^ 3 < y ^ 5) : x ^ 5 ≤ n ^ 2 := by
  by_contra h
  exact absurd (upper_pow_le_cube_of_mul_le hxy (not_le.mp h)) (not_le.mpr hy)

/-- Greedy lemma: multiplying `a` by the small prime factors of `s` one at a time, some
`a * d` with `d ∣ s` lands in the gap `(n ^ (2 / 5), n ^ (3 / 5)]`. -/
private lemma upper_exists_dvd_gap (n a : ℕ) (ha : a ^ 5 ≤ n ^ 2) :
    ∀ s : ℕ, (∀ ℓ, ℓ.Prime → ℓ ∣ s → ℓ ^ 5 ≤ n) → n ^ 2 < (a * s) ^ 5 →
      ∃ d, d ∣ s ∧ n ^ 2 < (a * d) ^ 5 ∧ (a * d) ^ 5 ≤ n ^ 3 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro hsmall hs
    have hs0 : s ≠ 0 := by
      rintro rfl
      simp at hs
    have hs1 : s ≠ 1 := by
      rintro rfl
      rw [mul_one] at hs
      omega
    obtain ⟨ℓ, hp, s', hs'⟩ := Nat.exists_prime_and_dvd hs1
    have hs'0 : s' ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hs'
      exact hs0 hs'
    by_cases h : n ^ 2 < (a * s') ^ 5
    · have hlt : s' < s := by
        have h2 := hp.two_le
        rw [hs']
        nlinarith [Nat.pos_of_ne_zero hs'0]
      have hss : s' ∣ s := ⟨ℓ, by rw [hs']; ring⟩
      obtain ⟨d, hd, h1, h2⟩ :=
        ih s' hlt (fun q hq hqs => hsmall q hq (hqs.trans hss)) h
      exact ⟨d, hd.trans hss, h1, h2⟩
    · refine ⟨s, dvd_rfl, hs, ?_⟩
      rw [not_lt] at h
      have hℓ := hsmall ℓ hp ⟨s', hs'⟩
      calc (a * s) ^ 5 = (a * s') ^ 5 * ℓ ^ 5 := by rw [hs']; ring
        _ ≤ n ^ 2 * n := Nat.mul_le_mul h hℓ
        _ = n ^ 3 := by ring

/-- If no divisor of `m` lies in the gap, then `s` has a prime factor `ℓ` with
`n < ℓ ^ 5`. -/
private lemma upper_exists_large_prime_dvd {n m a s : ℕ}
    (hgap : ∀ u w, m = u * w → n ^ 2 < u ^ 5 → n ^ 3 < u ^ 5)
    (ha : a ^ 5 ≤ n ^ 2) (hdvd : a * s ∣ m) (hs : n ^ 2 < (a * s) ^ 5) :
    ∃ ℓ, ℓ.Prime ∧ ℓ ∣ s ∧ n < ℓ ^ 5 := by
  by_contra h
  push Not at h
  obtain ⟨d, hd, h1, h2⟩ := upper_exists_dvd_gap n a ha s h hs
  obtain ⟨w, hw⟩ : a * d ∣ m := (mul_dvd_mul_left a hd).trans hdvd
  have := hgap (a * d) w hw h1
  omega

/-- In the remaining case, `m` is divisible by three primes `ℓ` with `n < ℓ ^ 5`. -/
private lemma upper_exists_three_large_primes {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (h1 : n ^ 3 < m ^ 5) (h2 : ∀ p k, p.Prime → m = p * k → n ^ 3 < k ^ 5)
    (hgap : ∀ u w, m = u * w → n ^ 2 < u ^ 5 → n ^ 3 < u ^ 5) :
    ∃ ℓ₁ ℓ₂ ℓ₃ k, ℓ₁.Prime ∧ ℓ₂.Prime ∧ ℓ₃.Prime ∧ n < ℓ₁ ^ 5 ∧ n < ℓ₂ ^ 5 ∧
      n < ℓ₃ ^ 5 ∧ m = ℓ₁ * ℓ₂ * ℓ₃ * k := by
  have hn : 1 ≤ n := hm1.trans hmn
  have hn23 : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right hn (by norm_num)
  obtain ⟨ℓ₁, hp1, ⟨m1, hm1'⟩, hl1⟩ :=
    upper_exists_large_prime_dvd hgap (a := 1) (s := m)
      (by rw [one_pow]; exact Nat.one_le_pow _ _ hn) (by rw [one_mul]) (by rw [one_mul]; omega)
  have ha1 : ℓ₁ ^ 5 ≤ n ^ 2 := upper_pow_le_sq_of_mul_le (hm1' ▸ hmn) (h2 ℓ₁ m1 hp1 hm1')
  obtain ⟨ℓ₂, hp2, ⟨m2, hm2⟩, hl2⟩ :=
    upper_exists_large_prime_dvd hgap ha1 (s := m1) (by rw [hm1']) (by rw [← hm1']; omega)
  have hC : n ^ 3 < (ℓ₁ * m2) ^ 5 := h2 ℓ₂ (ℓ₁ * m2) hp2 (by rw [hm1', hm2]; ring)
  obtain ⟨ℓ₃, hp3, ⟨k, hk⟩, hl3⟩ :=
    upper_exists_large_prime_dvd hgap ha1 (s := m2) ⟨ℓ₂, by rw [hm1', hm2]; ring⟩ (by omega)
  exact ⟨ℓ₁, ℓ₂, ℓ₃, k, hp1, hp2, hp3, hl1, hl2, hl3, by rw [hm1', hm2, hk]; ring⟩

/-- The case of three primes `r ≤ q ≤ p` with `n < r ^ 5` dividing `m`: take
`u = q * r` and `v = m / (q * r)`. -/
private lemma upper_cover_three {n m p q r k : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (hmk : m = p * q * r * k) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hqp : q ≤ p) (hrq : r ≤ q) (hql : n < q ^ 5) (hrl : n < r ^ 5)
    (h2 : ∀ p k, p.Prime → m = p * k → n ^ 3 < k ^ 5) :
    ∃ u ∈ upper_basis n, ∃ v ∈ upper_basis n, m = u * v := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hmk
    omega
  have huv : m = q * r * (p * k) := by rw [hmk]; ring
  have hqr : n ^ 2 < (q * r) ^ 5 := by
    calc n ^ 2 = n * n := by ring
      _ < q ^ 5 * r ^ 5 := Nat.mul_lt_mul'' hql hrl
      _ = (q * r) ^ 5 := by ring
  have hv5 : (p * k) ^ 5 ≤ n ^ 3 := upper_pow_le_cube_of_mul_le (huv ▸ hmn) hqr
  have hv1 : 1 ≤ p * k := Nat.pos_of_ne_zero (mul_ne_zero hp.ne_zero hk0)
  have hvn : p * k ≤ n := by
    have : 1 ≤ q * r := Nat.pos_of_ne_zero (mul_ne_zero hq.ne_zero hr.ne_zero)
    nlinarith
  refine ⟨q * r, ?_, p * k, upper_mem_basis_of_pow_le hv1 hvn hv5, huv⟩
  by_cases hq3 : q ^ 3 ≤ n
  · exact upper_mul_mem_basis_of_cube_le hq hr hq3 ((Nat.pow_le_pow_left hrq 3).trans hq3)
  · rw [not_le] at hq3
    have hm' : m = q * (p * r * k) := by rw [hmk]; ring
    have hq5 : q ^ 5 ≤ n ^ 2 :=
      upper_pow_le_sq_of_mul_le (hm' ▸ hmn) (h2 q (p * r * k) hq hm')
    have hrq2 : r * q ^ 2 ≤ n :=
      calc r * q ^ 2 = r * q * q := by ring
        _ ≤ r * q * p := Nat.mul_le_mul_left _ hqp
        _ ≤ r * q * p * k := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hk0)
        _ = m := by rw [hmk]; ring
        _ ≤ n := hmn
    have hqn : q ≤ n := by
      have : 1 ≤ r := hr.one_lt.le
      nlinarith [hq.one_lt]
    exact upper_mul_mem_basis_of_lt_cube hq hq3 hq5 hqn hr hrq2

/-- Every `1 ≤ m ≤ n` is a product of two elements of the basis. -/
private lemma upper_cover {n m : ℕ} (hn : 1 ≤ n) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    ∃ u ∈ upper_basis n, ∃ v ∈ upper_basis n, m = u * v := by
  by_cases h1 : m ^ 5 ≤ n ^ 3
  · refine ⟨m, upper_mem_basis_of_pow_le hm1 hmn h1, 1,
      upper_mem_basis_of_pow_le le_rfl hn ?_, (mul_one m).symm⟩
    rw [one_pow]
    exact Nat.one_le_pow _ _ hn
  rw [not_le] at h1
  by_cases h2 : ∃ p k, p.Prime ∧ m = p * k ∧ k ^ 5 ≤ n ^ 3
  · obtain ⟨p, k, hp, hpk, hk⟩ := h2
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hpk
      omega
    have hkn : k ≤ n := le_trans (Nat.le_of_dvd hm1 ⟨p, by rw [hpk]; ring⟩) hmn
    have hpn : p ≤ n := le_trans (Nat.le_of_dvd hm1 ⟨k, hpk⟩) hmn
    exact ⟨p, upper_mem_basis_of_prime hp hpn, k,
      upper_mem_basis_of_pow_le (Nat.pos_of_ne_zero hk0) hkn hk, hpk⟩
  have h2' : ∀ p k, p.Prime → m = p * k → n ^ 3 < k ^ 5 := by
    intro p k hp hpk
    by_contra h
    exact h2 ⟨p, k, hp, hpk, not_lt.mp h⟩
  by_cases h3 : ∃ u w, m = u * w ∧ n ^ 2 < u ^ 5 ∧ u ^ 5 ≤ n ^ 3
  · obtain ⟨u, w, huw, hu1, hu2⟩ := h3
    have hu0 : u ≠ 0 := by
      rintro rfl
      rw [zero_mul] at huw
      omega
    have hw0 : w ≠ 0 := by
      rintro rfl
      rw [mul_zero] at huw
      omega
    have hun : u ≤ n := le_trans (Nat.le_of_dvd hm1 ⟨w, huw⟩) hmn
    have hwn : w ≤ n := le_trans (Nat.le_of_dvd hm1 ⟨u, by rw [huw]; ring⟩) hmn
    have hw := upper_pow_le_cube_of_mul_le (huw ▸ hmn) hu1
    exact ⟨u, upper_mem_basis_of_pow_le (Nat.pos_of_ne_zero hu0) hun hu2, w,
      upper_mem_basis_of_pow_le (Nat.pos_of_ne_zero hw0) hwn hw, huw⟩
  have hgap : ∀ u w, m = u * w → n ^ 2 < u ^ 5 → n ^ 3 < u ^ 5 := by
    intro u w huw hu
    by_contra h
    exact h3 ⟨u, w, huw, hu, not_lt.mp h⟩
  obtain ⟨ℓ₁, ℓ₂, ℓ₃, k, hp1, hp2, hp3, hl1, hl2, hl3, hmk⟩ :=
    upper_exists_three_large_primes hm1 hmn h1 h2' hgap
  rcases le_total ℓ₁ ℓ₂ with h12 | h12 <;> rcases le_total ℓ₂ ℓ₃ with h23 | h23 <;>
    rcases le_total ℓ₁ ℓ₃ with h13 | h13
  · exact upper_cover_three hm1 hmn (k := k) (hmk.trans (by ring)) hp3 hp2 hp1 h23 h12 hl2 hl1 h2'
  · exact upper_cover_three hm1 hmn (k := k) (hmk.trans (by ring)) hp3 hp2 hp1 h23 h12 hl2 hl1 h2'
  · exact upper_cover_three hm1 hmn (k := k) (hmk.trans (by ring)) hp2 hp3 hp1 h23 h13 hl3 hl1 h2'
  · exact upper_cover_three hm1 hmn (k := k) (hmk.trans (by ring)) hp2 hp1 hp3 h12 h13 hl1 hl3 h2'
  · exact upper_cover_three hm1 hmn (k := k) (hmk.trans (by ring)) hp3 hp1 hp2 h13 h12 hl1 hl2 h2'
  · exact upper_cover_three hm1 hmn (k := k) (hmk.trans (by ring)) hp1 hp3 hp2 h13 h23 hl3 hl2 h2'
  · exact upper_cover_three hm1 hmn (k := k) (hmk.trans (by ring)) hp1 hp2 hp3 h12 h23 hl2 hl3 h2'
  · exact upper_cover_three hm1 hmn (k := k) (hmk.trans (by ring)) hp1 hp2 hp3 h12 h23 hl2 hl3 h2'

/-! ### Counting -/

private lemma upper_F_le_card_basis {n : ℕ} (hn : 1 ≤ n) : F n ≤ (upper_basis n).card := by
  unfold F
  refine csSup_le ⟨0, ∅, empty_subset _, by simp [Good], rfl⟩ ?_
  rintro k ⟨A, hA, hgood, rfl⟩
  refine upper_card_le_of_forall_eq_mul hgood fun a ha => ?_
  have := mem_Icc.mp (hA ha)
  exact upper_cover hn this.1 this.2

private lemma upper_card_smallSet_le (n : ℕ) :
    ((upper_smallSet n).card : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 5) := by
  have hsub : upper_smallSet n ⊆ Icc 1 ⌊(n : ℝ) ^ ((3 : ℝ) / 5)⌋₊ := by
    intro u hu
    simp only [upper_smallSet, mem_filter, mem_Icc] at hu
    refine mem_Icc.mpr ⟨hu.1.1, Nat.le_floor ?_⟩
    by_contra h
    rw [not_le] at h
    have h5 : ((n : ℝ) ^ ((3 : ℝ) / 5)) ^ 5 < (u : ℝ) ^ 5 :=
      pow_lt_pow_left₀ h (by positivity) (by norm_num)
    have hc : ((n : ℝ) ^ ((3 : ℝ) / 5)) ^ 5 = (n : ℝ) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
      norm_num
    rw [hc] at h5
    have : ((n ^ 3 : ℕ) : ℝ) < ((u ^ 5 : ℕ) : ℝ) := by push_cast; exact h5
    exact absurd hu.2 (not_le.mpr (by exact_mod_cast this))
  have h1 := card_le_card hsub
  rw [Nat.card_Icc, Nat.add_sub_cancel] at h1
  calc ((upper_smallSet n).card : ℝ) ≤ (⌊(n : ℝ) ^ ((3 : ℝ) / 5)⌋₊ : ℝ) := by exact_mod_cast h1
    _ ≤ (n : ℝ) ^ ((3 : ℝ) / 5) := Nat.floor_le (by positivity)

private lemma upper_card_cbrtPairs_le (n : ℕ) :
    ((upper_cbrtPairs n).card : ℝ) ≤ ((Nat.primeCounting ⌊(n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) ^ 2
      + Nat.primeCounting ⌊(n : ℝ) ^ ((1 : ℝ) / 3)⌋₊) / 2 := by
  set t := Nat.primeCounting ⌊(n : ℝ) ^ ((1 : ℝ) / 3)⌋₊
  have h1 : (upper_cbrtPairs n).card ≤ (t + 1).choose 2 := by
    refine card_image_le.trans ?_
    rw [card_sym2, Nat.primesLE_card_eq_primeCounting]
  rw [Nat.choose_two_right, Nat.add_sub_cancel] at h1
  calc ((upper_cbrtPairs n).card : ℝ) ≤ (((t + 1) * t / 2 : ℕ) : ℝ) := by exact_mod_cast h1
    _ ≤ (((t + 1) * t : ℕ) : ℝ) / 2 := Nat.cast_div_le
    _ = ((t : ℝ) ^ 2 + t) / 2 := by push_cast; ring

private lemma upper_card_bigPairs_le (n : ℕ) :
    ((upper_bigPairs n).card : ℝ) ≤ ∑ q ∈ bigPrimes n, (Nat.primeCounting (n / q ^ 2) : ℝ) := by
  have h1 : (upper_bigPairs n).card ≤ ∑ q ∈ bigPrimes n, Nat.primeCounting (n / q ^ 2) := by
    refine card_biUnion_le.trans (sum_le_sum fun q _ => ?_)
    refine card_image_le.trans ?_
    rw [Nat.primesLE_card_eq_primeCounting]
  exact_mod_cast h1

/-- **Upper bound.** `F n` is at most the size of the multiplicative basis. -/
private theorem upper_F_le (n : ℕ) (hn : 1 ≤ n) :
    (F n : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 5) + (Nat.primeCounting n : ℝ)
      + ((Nat.primeCounting ⌊(n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) ^ 2
          + Nat.primeCounting ⌊(n : ℝ) ^ ((1 : ℝ) / 3)⌋₊) / 2
      + ∑ q ∈ bigPrimes n, (Nat.primeCounting (n / q ^ 2) : ℝ) := by
  have hB : (upper_basis n).card ≤ (upper_smallSet n).card + (Nat.primesLE n).card
      + (upper_cbrtPairs n).card + (upper_bigPairs n).card := by
    unfold upper_basis
    refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    refine (card_union_le _ _).trans (Nat.add_le_add_right ?_ _)
    exact card_union_le _ _
  have hF : (F n : ℝ) ≤ ((upper_smallSet n).card : ℝ) + ((Nat.primesLE n).card : ℝ)
      + ((upper_cbrtPairs n).card : ℝ) + ((upper_bigPairs n).card : ℝ) := by
    exact_mod_cast (upper_F_le_card_basis hn).trans hB
  rw [Nat.primesLE_card_eq_primeCounting] at hF
  linarith [upper_card_smallSet_le n, upper_card_cbrtPairs_le n, upper_card_bigPairs_le n]

/-! ## The prime sum of the upper bound -/

private theorem tail_mem_bigPrimes {n q : ℕ} :
    q ∈ bigPrimes n ↔ q ≤ n ∧ q.Prime ∧ n < q ^ 3 ∧ q ^ 5 ≤ n ^ 2 := by
  simp [bigPrimes]

/-- Splitting a sum over the primes of `(a, c]` at `b`. -/
private theorem tail_sum_primesIoc_add (f : ℕ → ℝ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    ∑ q ∈ primesIoc a b, f q + ∑ q ∈ primesIoc b c, f q = ∑ q ∈ primesIoc a c, f q := by
  simp only [primesIoc, Finset.sum_filter]
  exact Finset.sum_Ioc_consecutive _ hab hbc

/-- Decomposition of a sum over the primes of `(X 0, X J]` into the bins `(X k, X (k + 1)]`. -/
private theorem tail_sum_primesIoc_bins (f : ℕ → ℝ) {X : ℕ → ℕ} (hX : Monotone X) (J : ℕ) :
    ∑ q ∈ primesIoc (X 0) (X J), f q =
      ∑ k ∈ Finset.range J, ∑ q ∈ primesIoc (X k) (X (k + 1)), f q := by
  induction J with
  | zero => simp [primesIoc]
  | succ J ih =>
    rw [Finset.sum_range_succ, ← ih,
      tail_sum_primesIoc_add f (hX (Nat.zero_le J)) (hX J.le_succ)]

/-- If `t ^ k * n ^ (1/3) < q`, then `π (n / q ^ 2) ≤ π ⌊n ^ (1/3) / t ^ (2 k)⌋`. -/
private theorem tail_primeCounting_div_sq_le_of_lt {n q k : ℕ} {t : ℝ} (ht : 0 < t) (hn : 0 < n)
    (hq : t ^ k * (n : ℝ) ^ ((1 : ℝ) / 3) < q) :
    Nat.primeCounting (n / q ^ 2) ≤
      Nat.primeCounting ⌊1 / t ^ (2 * k) * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := by
  apply Nat.monotone_primeCounting
  apply Nat.le_floor
  have hy : 0 < (n : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  calc ((n / q ^ 2 : ℕ) : ℝ) ≤ (n : ℝ) / ((q ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
    _ = ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 / (q : ℝ) ^ 2 := by rw [cbrt_pow_three]; push_cast; ring
    _ ≤ ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 / (t ^ k * (n : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 := by
      gcongr
    _ = 1 / t ^ (2 * k) * (n : ℝ) ^ ((1 : ℝ) / 3) := by
      rw [pow_mul']
      field_simp

/-- The contribution of the `k`-th bin. -/
private theorem tail_bin_sum_le {n : ℕ} {t : ℝ} (ht : 1 ≤ t) (hn : 0 < n) (k : ℕ) :
    ∑ q ∈ primesIoc ⌊t ^ k * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊
        ⌊t ^ (k + 1) * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊, (Nat.primeCounting (n / q ^ 2) : ℝ) ≤
      ((Nat.primeCounting ⌊t ^ (k + 1) * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) -
        Nat.primeCounting ⌊t ^ k * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊) *
        Nat.primeCounting ⌊1 / t ^ (2 * k) * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := by
  have ht0 : 0 < t := by linarith
  have hy : 0 < (n : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have hle : ⌊t ^ k * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ ≤ ⌊t ^ (k + 1) * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ :=
    Nat.floor_le_floor (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ht k.le_succ) hy.le)
  rw [← card_primesIoc hle, ← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun q hq => ?_
  rw [mem_primesIoc] at hq
  have hq' := (Nat.floor_lt (by positivity)).1 hq.1
  exact_mod_cast tail_primeCounting_div_sq_le_of_lt ht0 hn hq'

/-- The normalized contribution of the `k`-th bin converges. -/
private theorem tail_tendsto_bin {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Tendsto (fun n : ℕ =>
      ((Nat.primeCounting ⌊t ^ (k + 1) * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) -
        Nat.primeCounting ⌊t ^ k * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊) *
        Nat.primeCounting ⌊1 / t ^ (2 * k) * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ /
          ((n : ℝ) ^ ((2 : ℝ) / 3) / Real.log n ^ 2)) atTop
      (𝓝 ((3 * t ^ (k + 1) - 3 * t ^ k) * (3 * (1 / t ^ (2 * k))))) := by
  have h1 := tendsto_primeCounting_floor_mul (t ^ (k + 1)) (by positivity)
  have h2 := tendsto_primeCounting_floor_mul (t ^ k) (by positivity)
  have h3 := tendsto_primeCounting_floor_mul (1 / t ^ (2 * k)) (by positivity)
  refine ((h1.sub h2).mul h3).congr fun n => ?_
  have hS : (n : ℝ) ^ ((2 : ℝ) / 3) / Real.log n ^ 2 =
      (n : ℝ) ^ ((1 : ℝ) / 3) / Real.log n * ((n : ℝ) ^ ((1 : ℝ) / 3) / Real.log n) := by
    rw [← cbrt_sq]; ring
  rw [hS, ← sub_div, div_mul_div_comm]

/-- The limit of the normalized main part is smaller than `9 t`. -/
private theorem tail_sum_bin_limit_lt {t : ℝ} (ht : 1 < t) (J : ℕ) :
    ∑ k ∈ Finset.range J, (3 * t ^ (k + 1) - 3 * t ^ k) * (3 * (1 / t ^ (2 * k))) < 9 * t := by
  have ht0 : 0 < t := by linarith
  have ht0' : t ≠ 0 := ht0.ne'
  have h : ∀ k : ℕ, (3 * t ^ (k + 1) - 3 * t ^ k) * (3 * (1 / t ^ (2 * k))) =
      9 * t * ((1 - 1 / t) * (1 / t) ^ k) := by
    intro k
    rw [one_div_pow, pow_mul']
    field_simp
    ring
  simp_rw [h, ← Finset.mul_sum, mul_neg_geom_sum]
  have : 0 < (1 / t) ^ J := by positivity
  nlinarith

/-- Eventually, the sum of the bin bounds is at most `9 t n ^ (2/3) / (log n) ^ 2`. -/
private theorem tail_eventually_bins_le {t : ℝ} (ht : 1 < t) (J : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∑ k ∈ Finset.range J,
      ((Nat.primeCounting ⌊t ^ (k + 1) * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) -
        Nat.primeCounting ⌊t ^ k * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊) *
        Nat.primeCounting ⌊1 / t ^ (2 * k) * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ ≤
      9 * t * ((n : ℝ) ^ ((2 : ℝ) / 3) / Real.log n ^ 2) := by
  have hlim := tendsto_finsetSum (Finset.range J) fun k _ =>
    tail_tendsto_bin (t := t) (by linarith) k
  filter_upwards [hlim.eventually_lt_const (tail_sum_bin_limit_lt ht J), eventually_gt_atTop 1]
    with n hn hn1
  have hn' : (1 : ℝ) < n := by exact_mod_cast hn1
  have hlog := Real.log_pos hn'
  have hS : 0 < (n : ℝ) ^ ((2 : ℝ) / 3) / Real.log n ^ 2 := by positivity
  rw [← Finset.sum_div, div_lt_iff₀ hS] at hn
  exact hn.le

/-- The main part: the primes of `bigPrimes n` up to `⌊t ^ J * n ^ (1/3)⌋`. -/
private theorem tail_main_part_le {n : ℕ} {t : ℝ} (ht : 1 ≤ t) (hn : 0 < n) (J : ℕ) :
    ∑ q ∈ (bigPrimes n).filter (fun q => q ≤ ⌊t ^ J * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊),
        (Nat.primeCounting (n / q ^ 2) : ℝ) ≤
      ∑ k ∈ Finset.range J,
        ((Nat.primeCounting ⌊t ^ (k + 1) * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) -
          Nat.primeCounting ⌊t ^ k * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊) *
          Nat.primeCounting ⌊1 / t ^ (2 * k) * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := by
  have ht0 : 0 < t := by linarith
  have hy0 : 0 < (n : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have hX : Monotone fun k : ℕ => ⌊t ^ k * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := fun a b hab =>
    Nat.floor_le_floor (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ ht hab) hy0.le)
  calc ∑ q ∈ (bigPrimes n).filter (fun q => q ≤ ⌊t ^ J * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊),
        (Nat.primeCounting (n / q ^ 2) : ℝ)
      ≤ ∑ q ∈ primesIoc ⌊t ^ 0 * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊
          ⌊t ^ J * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊, (Nat.primeCounting (n / q ^ 2) : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun q hq => ?_) fun _ _ _ => by positivity
        rw [Finset.mem_filter, tail_mem_bigPrimes] at hq
        rw [mem_primesIoc, Nat.floor_lt (by positivity), pow_zero, one_mul]
        refine ⟨?_, hq.2, hq.1.2.1⟩
        have h3 : ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 < (q : ℝ) ^ 3 := by
          rw [cbrt_pow_three]; exact_mod_cast hq.1.2.2.1
        exact lt_of_pow_lt_pow_left₀ 3 (by positivity) h3
    _ = ∑ k ∈ Finset.range J, ∑ q ∈ primesIoc ⌊t ^ k * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊
          ⌊t ^ (k + 1) * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊, (Nat.primeCounting (n / q ^ 2) : ℝ) :=
        tail_sum_primesIoc_bins _ hX J
    _ ≤ _ := Finset.sum_le_sum fun k _ => tail_bin_sum_le ht hn k

/-- **Lemma T.** A Chebyshev bound gives `∑_{X < q ≤ 2 ^ L X} 1 / q ^ 2 ≤ 4 K / (X log X)`. -/
private theorem tail_sum_one_div_sq_le {K x₁ : ℝ}
    (hcheb : ∀ x : ℝ, x₁ ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ K * x / Real.log x)
    (hK : 0 ≤ K) {X : ℕ} (hX₁ : x₁ ≤ X) (hX₂ : 2 ≤ X) (L : ℕ) :
    ∑ q ∈ primesIoc X (2 ^ L * X), 1 / (q : ℝ) ^ 2 ≤
      4 * (K / (X * Real.log X)) * (1 - (1 / 2) ^ L) := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlogX : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  induction L with
  | zero => simp [primesIoc]
  | succ L ih =>
    have hle1 : X ≤ 2 ^ L * X := Nat.le_mul_of_pos_left X (by positivity)
    have hle2 : 2 ^ L * X ≤ 2 ^ (L + 1) * X :=
      Nat.mul_le_mul_right X (Nat.pow_le_pow_right (by norm_num) L.le_succ)
    have hcard : ((primesIoc (2 ^ L * X) (2 ^ (L + 1) * X)).card : ℝ) ≤
        K * ((2 : ℝ) ^ (L + 1) * X) / Real.log X := by
      rw [card_primesIoc hle2]
      have h := hcheb ((2 ^ (L + 1) * X : ℕ) : ℝ) (hX₁.trans (by exact_mod_cast hle1.trans hle2))
      rw [Nat.floor_natCast] at h
      push_cast at h
      have h0 : (0 : ℝ) ≤ Nat.primeCounting (2 ^ L * X) := Nat.cast_nonneg _
      calc (Nat.primeCounting (2 ^ (L + 1) * X) : ℝ) - Nat.primeCounting (2 ^ L * X)
          ≤ Nat.primeCounting (2 ^ (L + 1) * X) := by linarith
        _ ≤ K * ((2 : ℝ) ^ (L + 1) * X) / Real.log ((2 : ℝ) ^ (L + 1) * X) := h
        _ ≤ K * ((2 : ℝ) ^ (L + 1) * X) / Real.log X := by
          apply div_le_div_of_nonneg_left (by positivity) hlogX
          apply Real.log_le_log hX0
          have : (1 : ℝ) ≤ 2 ^ (L + 1) := one_le_pow₀ (by norm_num)
          nlinarith
    have hblock : ∑ q ∈ primesIoc (2 ^ L * X) (2 ^ (L + 1) * X), 1 / (q : ℝ) ^ 2 ≤
        2 * (K / (X * Real.log X)) * (1 / 2) ^ L := by
      calc ∑ q ∈ primesIoc (2 ^ L * X) (2 ^ (L + 1) * X), 1 / (q : ℝ) ^ 2
          ≤ (primesIoc (2 ^ L * X) (2 ^ (L + 1) * X)).card • (1 / ((2 : ℝ) ^ L * X) ^ 2) := by
            refine Finset.sum_le_card_nsmul _ _ _ fun q hq => ?_
            rw [mem_primesIoc] at hq
            have : ((2 : ℝ) ^ L * X) < q := by exact_mod_cast hq.1
            exact one_div_le_one_div_of_le (by positivity)
              (pow_le_pow_left₀ (by positivity) this.le 2)
        _ = (primesIoc (2 ^ L * X) (2 ^ (L + 1) * X)).card * (1 / ((2 : ℝ) ^ L * X) ^ 2) :=
            nsmul_eq_mul _ _
        _ ≤ K * ((2 : ℝ) ^ (L + 1) * X) / Real.log X * (1 / ((2 : ℝ) ^ L * X) ^ 2) := by
            gcongr
        _ = 2 * (K / (X * Real.log X)) * (1 / 2) ^ L := by
            rw [one_div_pow]
            field_simp
            ring
    calc ∑ q ∈ primesIoc X (2 ^ (L + 1) * X), 1 / (q : ℝ) ^ 2
        = ∑ q ∈ primesIoc X (2 ^ L * X), 1 / (q : ℝ) ^ 2 +
          ∑ q ∈ primesIoc (2 ^ L * X) (2 ^ (L + 1) * X), 1 / (q : ℝ) ^ 2 :=
          (tail_sum_primesIoc_add _ hle1 hle2).symm
      _ ≤ 4 * (K / (X * Real.log X)) * (1 - (1 / 2) ^ L) +
          2 * (K / (X * Real.log X)) * (1 / 2) ^ L := add_le_add ih hblock
      _ = 4 * (K / (X * Real.log X)) * (1 - (1 / 2) ^ (L + 1)) := by ring

/-- For `q ^ 5 ≤ n ^ 2`, Chebyshev gives `π (n / q ^ 2) ≤ 5 K n / (q ^ 2 log n)`. -/
private theorem tail_primeCounting_div_sq_le_of_pow_five_le {K x₁ : ℝ}
    (hcheb : ∀ x : ℝ, x₁ ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ K * x / Real.log x)
    (hK : 0 ≤ K) {n q : ℕ} (hn : 1 < n) (hnx : max x₁ 1 ^ 5 ≤ n) (hq : 0 < q)
    (hq5 : q ^ 5 ≤ n ^ 2) :
    (Nat.primeCounting (n / q ^ 2) : ℝ) ≤ 5 * K * n / Real.log n * (1 / (q : ℝ) ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hx0 : 0 < (n : ℝ) / (q : ℝ) ^ 2 := by positivity
  have hx5 : (n : ℝ) ≤ ((n : ℝ) / (q : ℝ) ^ 2) ^ 5 := by
    have h : (q : ℝ) ^ 5 ≤ (n : ℝ) ^ 2 := by exact_mod_cast hq5
    rw [div_pow, le_div_iff₀ (by positivity)]
    calc (n : ℝ) * ((q : ℝ) ^ 2) ^ 5 = n * ((q : ℝ) ^ 5) ^ 2 := by ring
      _ ≤ n * ((n : ℝ) ^ 2) ^ 2 := by gcongr
      _ = (n : ℝ) ^ 5 := by ring
  have hx₁ : x₁ ≤ (n : ℝ) / (q : ℝ) ^ 2 :=
    (le_max_left x₁ 1).trans (le_of_pow_le_pow_left₀ (n := 5) (by norm_num) hx0.le
      (hnx.trans hx5))
  have hlogx : Real.log n ≤ 5 * Real.log ((n : ℝ) / (q : ℝ) ^ 2) := by
    have := Real.log_le_log hn0 hx5
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hfloor : ⌊(n : ℝ) / (q : ℝ) ^ 2⌋₊ = n / q ^ 2 := by
    rw [← Nat.cast_pow]
    exact Nat.floor_div_eq_div n (q ^ 2)
  rw [← hfloor]
  calc (Nat.primeCounting ⌊(n : ℝ) / (q : ℝ) ^ 2⌋₊ : ℝ)
      ≤ K * ((n : ℝ) / (q : ℝ) ^ 2) / Real.log ((n : ℝ) / (q : ℝ) ^ 2) :=
        hcheb _ hx₁
    _ ≤ K * ((n : ℝ) / (q : ℝ) ^ 2) / (Real.log n / 5) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      linarith
    _ = 5 * K * n / Real.log n * (1 / (q : ℝ) ^ 2) := by
      field_simp

/-- The primes of `bigPrimes n` above `X`. -/
private theorem tail_sum_filter_le {K x₁ : ℝ}
    (hcheb : ∀ x : ℝ, x₁ ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ K * x / Real.log x)
    (hK : 0 ≤ K) {n X : ℕ} (hn : 1 < n) (hnx : max x₁ 1 ^ 5 ≤ n) (hX₁ : x₁ ≤ X)
    (hX₂ : 2 ≤ X) :
    ∑ q ∈ (bigPrimes n).filter (fun q => ¬ q ≤ X), (Nat.primeCounting (n / q ^ 2) : ℝ) ≤
      5 * K * n / Real.log n * (4 * (K / (X * Real.log X))) := by
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hlogX : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hsub : (bigPrimes n).filter (fun q => ¬ q ≤ X) ⊆ primesIoc X (2 ^ n * X) := by
    intro q hq
    rw [Finset.mem_filter, tail_mem_bigPrimes] at hq
    rw [mem_primesIoc]
    refine ⟨not_le.1 hq.2, ?_, hq.1.2.1⟩
    calc q ≤ n := hq.1.1
      _ ≤ 2 ^ n := Nat.lt_two_pow_self.le
      _ ≤ 2 ^ n * X := Nat.le_mul_of_pos_right _ (by omega)
  calc ∑ q ∈ (bigPrimes n).filter (fun q => ¬ q ≤ X), (Nat.primeCounting (n / q ^ 2) : ℝ)
      ≤ ∑ q ∈ (bigPrimes n).filter (fun q => ¬ q ≤ X),
          5 * K * n / Real.log n * (1 / (q : ℝ) ^ 2) := by
        refine Finset.sum_le_sum fun q hq => ?_
        rw [Finset.mem_filter, tail_mem_bigPrimes] at hq
        exact tail_primeCounting_div_sq_le_of_pow_five_le hcheb hK hn hnx hq.1.2.1.pos hq.1.2.2.2
    _ = 5 * K * n / Real.log n * ∑ q ∈ (bigPrimes n).filter (fun q => ¬ q ≤ X),
          1 / (q : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 5 * K * n / Real.log n * ∑ q ∈ primesIoc X (2 ^ n * X), 1 / (q : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity)
          (by positivity)
    _ ≤ 5 * K * n / Real.log n * (4 * (K / (X * Real.log X)) * (1 - (1 / 2) ^ n)) :=
        mul_le_mul_of_nonneg_left (tail_sum_one_div_sq_le hcheb hK hX₁ hX₂ n) (by positivity)
    _ ≤ 5 * K * n / Real.log n * (4 * (K / (X * Real.log X))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_of_le_one_right (by positivity) (sub_le_self _ (by positivity))

/-- The tail part: the primes of `bigPrimes n` above `⌊t ^ J * n ^ (1/3)⌋`. -/
private theorem tail_tail_part_le {K x₁ t : ℝ}
    (hcheb : ∀ x : ℝ, x₁ ≤ x → (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ K * x / Real.log x)
    (hK : 0 ≤ K) {J n : ℕ} (htJ : 2 ≤ t ^ J) (hn : 1 < n) (hnx : max x₁ 1 ^ 5 ≤ n)
    (hy : max x₁ 2 ≤ (n : ℝ) ^ ((1 : ℝ) / 3)) :
    ∑ q ∈ (bigPrimes n).filter (fun q => ¬ q ≤ ⌊t ^ J * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊),
        (Nat.primeCounting (n / q ^ 2) : ℝ) ≤
      120 * K ^ 2 / t ^ J * ((n : ℝ) ^ ((2 : ℝ) / 3) / Real.log n ^ 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hy2 : 2 ≤ (n : ℝ) ^ ((1 : ℝ) / 3) := (le_max_right _ _).trans hy
  have hy0 : 0 < (n : ℝ) ^ ((1 : ℝ) / 3) := by linarith
  have htJ0 : 0 < t ^ J := by linarith
  have hlogy : Real.log ((n : ℝ) ^ ((1 : ℝ) / 3)) = Real.log n / 3 := by
    rw [Real.log_rpow hn0]; ring
  have hXJ : t ^ J * (n : ℝ) ^ ((1 : ℝ) / 3) / 2 ≤ ⌊t ^ J * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := by
    have h1 := Nat.sub_one_lt_floor (t ^ J * (n : ℝ) ^ ((1 : ℝ) / 3))
    have h2 : 4 ≤ t ^ J * (n : ℝ) ^ ((1 : ℝ) / 3) := by nlinarith
    linarith
  have hXJy : (n : ℝ) ^ ((1 : ℝ) / 3) ≤ ⌊t ^ J * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := by nlinarith
  have hXJ2 : 2 ≤ ⌊t ^ J * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := by
    have : (2 : ℝ) ≤ ⌊t ^ J * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := by linarith
    exact_mod_cast this
  have hXJx : x₁ ≤ ⌊t ^ J * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ :=
    ((le_max_left _ _).trans hy).trans hXJy
  have hlogXJ : Real.log n / 3 ≤ Real.log ⌊t ^ J * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := by
    rw [← hlogy]
    exact Real.log_le_log hy0 hXJy
  calc ∑ q ∈ (bigPrimes n).filter (fun q => ¬ q ≤ ⌊t ^ J * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊),
        (Nat.primeCounting (n / q ^ 2) : ℝ)
      ≤ 5 * K * n / Real.log n * (4 * (K / (⌊t ^ J * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ *
          Real.log ⌊t ^ J * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊))) :=
        tail_sum_filter_le hcheb hK hn hnx hXJx hXJ2
    _ ≤ 5 * K * n / Real.log n * (4 * (K / ((t ^ J * (n : ℝ) ^ ((1 : ℝ) / 3) / 2) *
          (Real.log n / 3)))) := by
        gcongr
    _ = 120 * K ^ 2 / t ^ J * ((n : ℝ) ^ ((2 : ℝ) / 3) / Real.log n ^ 2) := by
        rw [← cbrt_sq]
        nth_rewrite 1 [← cbrt_pow_three n]
        field_simp
        ring

/-- **Chojecki, Lemma 2.3.** Eventually `∑_{q ∈ bigPrimes n} π (n / q ^ 2) ≤ (9 + δ) S`. -/
private theorem tail_sum_bigPrimes_le (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∑ q ∈ bigPrimes n, (Nat.primeCounting (n / q ^ 2) : ℝ) ≤
      (9 + δ) * ((n : ℝ) ^ ((2 : ℝ) / 3) / Real.log n ^ 2) := by
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1
    (Chebyshev.eventually_primeCounting_le (ε := 1) one_pos)
  have hK0 : 0 < Real.log 4 + 1 := by positivity
  have ht1 : 1 < 1 + δ / 27 := by linarith
  obtain ⟨J, hJ⟩ := pow_unbounded_of_one_lt (max 2 (360 * (Real.log 4 + 1) ^ 2 / δ)) ht1
  have hJ2 : 2 ≤ (1 + δ / 27) ^ J := (le_max_left _ _).trans hJ.le
  have hJK : 120 * (Real.log 4 + 1) ^ 2 / (1 + δ / 27) ^ J ≤ δ / 3 := by
    have h := (le_max_right _ _).trans hJ.le
    rw [div_le_iff₀ hδ] at h
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hy : Tendsto (fun n : ℕ => (n : ℝ) ^ ((1 : ℝ) / 3)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [tail_eventually_bins_le ht1 J, eventually_gt_atTop 1,
    hy.eventually_ge_atTop (max x₁ 2), eventually_ge_atTop ⌈max x₁ 1 ^ 5⌉₊]
    with n hmain hn1 hyx hn5
  have hn5' : max x₁ 1 ^ 5 ≤ n := Nat.ceil_le.1 hn5
  have hS : 0 ≤ (n : ℝ) ^ ((2 : ℝ) / 3) / Real.log n ^ 2 := by positivity
  rw [← Finset.sum_filter_add_sum_filter_not (bigPrimes n)
    (fun q => q ≤ ⌊(1 + δ / 27) ^ J * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊)]
  have h1 := (tail_main_part_le ht1.le (by omega) J).trans hmain
  have h2 := tail_tail_part_le hx₁ hK0.le hJ2 hn1 hn5' hyx
  calc _ ≤ 9 * (1 + δ / 27) * ((n : ℝ) ^ ((2 : ℝ) / 3) / Real.log n ^ 2) +
        120 * (Real.log 4 + 1) ^ 2 / (1 + δ / 27) ^ J *
          ((n : ℝ) ^ ((2 : ℝ) / 3) / Real.log n ^ 2) := add_le_add h1 h2
    _ ≤ 9 * (1 + δ / 27) * ((n : ℝ) ^ ((2 : ℝ) / 3) / Real.log n ^ 2) +
        δ / 3 * ((n : ℝ) ^ ((2 : ℝ) / 3) / Real.log n ^ 2) := by gcongr
    _ ≤ (9 + δ) * ((n : ℝ) ^ ((2 : ℝ) / 3) / Real.log n ^ 2) := by nlinarith

/-! ## The lower bound -/

/-! ### Bin facts -/

private lemma lower_mem_bin {n : ℕ} {t : ℝ} {r : ℤ} {p : ℕ} (hp : p ∈ bin n t r) :
    p.Prime ∧ t ^ r * (n : ℝ) ^ ((1 : ℝ) / 3) < p ∧
      (p : ℝ) ≤ t ^ (r + 1) * (n : ℝ) ^ ((1 : ℝ) / 3) := by
  rw [bin, mem_primesIoc] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  exact ⟨h3, Nat.lt_of_floor_lt h1, (Nat.le_floor_iff' h3.ne_zero).mp h2⟩

private lemma lower_cbrt_pos {n : ℕ} {t : ℝ} (ht : 1 < t) {r : ℤ} {p : ℕ}
    (hp : p ∈ bin n t r) : 0 < (n : ℝ) ^ ((1 : ℝ) / 3) := by
  obtain ⟨hpr, -, h2⟩ := lower_mem_bin hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
  have htr : 0 < t ^ (r + 1) := zpow_pos (by linarith) _
  have hy : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  rcases hy.lt_or_eq with hy | hy
  · exact hy
  · rw [← hy, mul_zero] at h2
    linarith

private lemma lower_eq_of_mem_bin {n : ℕ} {t : ℝ} (ht : 1 < t) {r s : ℤ} {p : ℕ}
    (hr : p ∈ bin n t r) (hs : p ∈ bin n t s) : r = s := by
  have hy := lower_cbrt_pos ht hr
  obtain ⟨-, hr1, hr2⟩ := lower_mem_bin hr
  obtain ⟨-, hs1, hs2⟩ := lower_mem_bin hs
  have h1 : t ^ r < t ^ (s + 1) := lt_of_mul_lt_mul_right (hr1.trans_le hs2) hy.le
  have h2 : t ^ s < t ^ (r + 1) := lt_of_mul_lt_mul_right (hs1.trans_le hr2) hy.le
  rw [zpow_lt_zpow_iff_right₀ ht] at h1 h2
  omega

private lemma lower_le_floor {n : ℕ} {t : ℝ} (ht : 1 < t) {r R : ℤ} {p : ℕ}
    (hp : p ∈ bin n t r) (hrR : r + 1 ≤ R) : p ≤ ⌊t ^ R * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := by
  rw [bin, mem_primesIoc] at hp
  refine hp.2.1.trans (Nat.floor_le_floor ?_)
  have hy : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  exact mul_le_mul_of_nonneg_right (zpow_le_zpow_right₀ ht.le hrR) hy

private lemma lower_mul_mul_le {n : ℕ} {t : ℝ} (ht : 1 < t) {i j k : ℤ} {p q r : ℕ}
    (hp : p ∈ bin n t i) (hq : q ∈ bin n t j) (hr : r ∈ bin n t k) (hijk : i + j + k = -3) :
    p * q * r ≤ n := by
  obtain ⟨-, -, hp2⟩ := lower_mem_bin hp
  obtain ⟨-, -, hq2⟩ := lower_mem_bin hq
  obtain ⟨-, -, hr2⟩ := lower_mem_bin hr
  have ht0 : t ≠ 0 := by positivity
  have hy : 0 ≤ (n : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have key : ((p * q * r : ℕ) : ℝ) ≤ n := by
    push_cast
    calc (p : ℝ) * q * r
        ≤ (t ^ (i + 1) * (n : ℝ) ^ ((1 : ℝ) / 3)) * (t ^ (j + 1) * (n : ℝ) ^ ((1 : ℝ) / 3)) *
          (t ^ (k + 1) * (n : ℝ) ^ ((1 : ℝ) / 3)) := by gcongr
      _ = t ^ ((i + 1) + (j + 1) + (k + 1)) * ((n : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 := by
          rw [zpow_add₀ ht0 _ (k + 1), zpow_add₀ ht0 (i + 1) (j + 1)]; ring
      _ = n := by
          rw [cbrt_pow_three, show (i + 1) + (j + 1) + (k + 1) = 0 by omega, zpow_zero, one_mul]
  exact_mod_cast key

/-! ### Latin colourings -/

/-- `g` is a Latin colouring of `X × Y` by `Z`. -/
private def lower_IsLatin (X Y Z : Finset ℕ) (g : ℕ → ℕ → ℕ) : Prop :=
  (∀ x ∈ X, ∀ y ∈ Y, g x y ∈ Z) ∧ (∀ x ∈ X, Set.InjOn (g x) Y) ∧
    ∀ y ∈ Y, Set.InjOn (fun x => g x y) X

private lemma lower_exists_isLatin (X Y Z : Finset ℕ) (hX : X.card ≤ Z.card)
    (hY : Y.card ≤ Z.card) : ∃ g, lower_IsLatin X Y Z g := by
  classical
  rcases Nat.eq_zero_or_pos Z.card with h0 | hpos
  · have hX0 : X = ∅ := Finset.card_eq_zero.mp (by omega)
    have hY0 : Y = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hX0 hY0
    exact ⟨fun _ _ => 0, by simp, by simp, by simp⟩
  · have : NeZero Z.card := ⟨by omega⟩
    let eX : X → Fin Z.card := fun x => Fin.castLE hX (X.equivFin x)
    let eY : Y → Fin Z.card := fun y => Fin.castLE hY (Y.equivFin y)
    have heX : Function.Injective eX := fun a b h =>
      X.equivFin.injective (Fin.castLE_injective hX h)
    have heY : Function.Injective eY := fun a b h =>
      Y.equivFin.injective (Fin.castLE_injective hY h)
    refine ⟨fun x y => if hx : x ∈ X then if hy : y ∈ Y then
      (Z.equivFin.symm (eX ⟨x, hx⟩ + eY ⟨y, hy⟩) : ℕ) else 0 else 0, ?_, ?_, ?_⟩
    · intro x hx y hy
      simp only [dite_eq_left hx, dite_eq_left hy]
      exact (Z.equivFin.symm _).2
    · intro x hx y₁ hy₁ y₂ hy₂ h
      rw [Finset.mem_coe] at hy₁ hy₂
      simp only [dite_eq_left hx, dite_eq_left hy₁, dite_eq_left hy₂] at h
      have h' := add_left_cancel (Z.equivFin.symm.injective (Subtype.ext h))
      exact congrArg Subtype.val (heY h')
    · intro y hy x₁ hx₁ x₂ hx₂ h
      rw [Finset.mem_coe] at hx₁ hx₂
      simp only [dite_eq_left hy, dite_eq_left hx₁, dite_eq_left hx₂] at h
      have h' := add_right_cancel (Z.equivFin.symm.injective (Subtype.ext h))
      exact congrArg Subtype.val (heX h')

/-! ### The triples of primes -/

/-- The index set of the triples: a cell together with a prime from each of its first two
bins. -/
private noncomputable def lower_triples (n : ℕ) (t : ℝ) (C : Finset (ℤ × ℤ)) :
    Finset (Σ _ : ℤ × ℤ, ℕ × ℕ) :=
  C.sigma fun c => bin n t c.1 ×ˢ bin n t c.2

/-- The product of the triple of primes attached to `τ`. -/
private def lower_prod (f : ℤ × ℤ → ℕ → ℕ → ℕ) (τ : Σ _ : ℤ × ℤ, ℕ × ℕ) : ℕ :=
  τ.2.1 * τ.2.2 * f τ.1 τ.2.1 τ.2.2

private lemma lower_mem_triples {n : ℕ} {t : ℝ} {C : Finset (ℤ × ℤ)} {i j : ℤ} {p q : ℕ} :
    (⟨(i, j), (p, q)⟩ : Σ _ : ℤ × ℤ, ℕ × ℕ) ∈ lower_triples n t C ↔
      (i, j) ∈ C ∧ p ∈ bin n t i ∧ q ∈ bin n t j := by
  simp [lower_triples]

private lemma lower_eq_of_dvd_mul_mul {ℓ p q r : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (h : ℓ ∣ p * q * r) : ℓ = p ∨ ℓ = q ∨ ℓ = r := by
  rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hℓ).mp h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h)
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hℓ hq).mp h))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hℓ hr).mp h))

private lemma lower_position {n : ℕ} {t : ℝ} (ht : 1 < t) {ℓ p q r : ℕ} {s i j k : ℤ}
    (hℓ : ℓ ∈ bin n t s) (hp : p ∈ bin n t i) (hq : q ∈ bin n t j) (hr : r ∈ bin n t k)
    (h : ℓ ∣ p * q * r) : (ℓ = p ∧ s = i) ∨ (ℓ = q ∧ s = j) ∨ (ℓ = r ∧ s = k) := by
  rcases lower_eq_of_dvd_mul_mul (lower_mem_bin hℓ).1 (lower_mem_bin hp).1 (lower_mem_bin hq).1
      (lower_mem_bin hr).1 h with rfl | rfl | rfl
  · exact Or.inl ⟨rfl, lower_eq_of_mem_bin ht hℓ hp⟩
  · exact Or.inr (Or.inl ⟨rfl, lower_eq_of_mem_bin ht hℓ hq⟩)
  · exact Or.inr (Or.inr ⟨rfl, lower_eq_of_mem_bin ht hℓ hr⟩)

/-- Within a cell, a prime of a known bin sits at the same position in two triples. -/
private lemma lower_same_pos {ℓ p q r p' q' r' : ℕ} {s i j : ℤ} (hij : i < j)
    (hjk : i + 2 * j ≤ -4) (e : (ℓ = p ∧ s = i) ∨ (ℓ = q ∧ s = j) ∨ (ℓ = r ∧ s = -3 - i - j))
    (e' : (ℓ = p' ∧ s = i) ∨ (ℓ = q' ∧ s = j) ∨ (ℓ = r' ∧ s = -3 - i - j)) :
    (s = i → p = p') ∧ (s = j → q = q') ∧ (s = -3 - i - j → r = r') := by
  omega

/-- **Linearity**: two distinct primes determine the triple containing them. -/
private lemma lower_linear {n : ℕ} {t : ℝ} (ht : 1 < t) {C : Finset (ℤ × ℤ)}
    (hC : ∀ c ∈ C, c.1 < c.2 ∧ c.1 + 2 * c.2 ≤ -4) {f : ℤ × ℤ → ℕ → ℕ → ℕ}
    (hf : ∀ c ∈ C, lower_IsLatin (bin n t c.1) (bin n t c.2) (bin n t (-3 - c.1 - c.2)) (f c))
    {τ τ' : Σ _ : ℤ × ℤ, ℕ × ℕ} (hτ : τ ∈ lower_triples n t C) (hτ' : τ' ∈ lower_triples n t C)
    {ℓ₁ ℓ₂ : ℕ} {s₁ s₂ : ℤ} (h₁ : ℓ₁ ∈ bin n t s₁) (h₂ : ℓ₂ ∈ bin n t s₂) (hne : ℓ₁ ≠ ℓ₂)
    (h₁τ : ℓ₁ ∣ lower_prod f τ) (h₂τ : ℓ₂ ∣ lower_prod f τ)
    (h₁τ' : ℓ₁ ∣ lower_prod f τ') (h₂τ' : ℓ₂ ∣ lower_prod f τ') : τ = τ' := by
  obtain ⟨⟨i, j⟩, ⟨p, q⟩⟩ := τ
  obtain ⟨⟨i', j'⟩, ⟨p', q'⟩⟩ := τ'
  rw [lower_mem_triples] at hτ hτ'
  obtain ⟨hc, hp, hq⟩ := hτ
  obtain ⟨hc', hp', hq'⟩ := hτ'
  obtain ⟨hr, hinj₁, hinj₂⟩ := hf _ hc
  obtain ⟨hr', -, -⟩ := hf _ hc'
  have hr₀ := hr p hp q hq
  have hr₀' := hr' p' hp' q' hq'
  have ho := hC _ hc
  have ho' := hC _ hc'
  simp only [lower_prod] at h₁τ h₂τ h₁τ' h₂τ'
  simp only at hr₀ hr₀' ho ho'
  have e₁ := lower_position ht h₁ hp hq hr₀ h₁τ
  have e₂ := lower_position ht h₂ hp hq hr₀ h₂τ
  have e₁' := lower_position ht h₁ hp' hq' hr₀' h₁τ'
  have e₂' := lower_position ht h₂ hp' hq' hr₀' h₂τ'
  have hs : s₁ ≠ s₂ := by clear e₁' e₂'; omega
  have a₁ : s₁ = i ∨ s₁ = j ∨ s₁ = -3 - i - j := by clear e₂ e₁' e₂'; omega
  have a₂ : s₂ = i ∨ s₂ = j ∨ s₂ = -3 - i - j := by clear e₁ e₁' e₂'; omega
  have a₁' : s₁ = i' ∨ s₁ = j' ∨ s₁ = -3 - i' - j' := by clear e₁ e₂ e₂'; omega
  have a₂' : s₂ = i' ∨ s₂ = j' ∨ s₂ = -3 - i' - j' := by clear e₁ e₂ e₁'; omega
  obtain ⟨rfl, rfl⟩ : i = i' ∧ j = j' := by clear e₁ e₂ e₁' e₂'; omega
  obtain ⟨P₁, Q₁, R₁⟩ := lower_same_pos ho.1 ho.2 e₁ e₁'
  obtain ⟨P₂, Q₂, R₂⟩ := lower_same_pos ho.1 ho.2 e₂ e₂'
  have h : (p = p' ∧ q = q') ∨ (p = p' ∧ f (i, j) p q = f (i, j) p' q') ∨
      (q = q' ∧ f (i, j) p q = f (i, j) p' q') := by
    rcases a₁ with h1 | h1 | h1 <;> rcases a₂ with h2 | h2 | h2 <;>
      first
      | exact absurd (h1.trans h2.symm) hs
      | exact Or.inl ⟨P₁ h1, Q₂ h2⟩
      | exact Or.inl ⟨P₂ h2, Q₁ h1⟩
      | exact Or.inr (Or.inl ⟨P₁ h1, R₂ h2⟩)
      | exact Or.inr (Or.inl ⟨P₂ h2, R₁ h1⟩)
      | exact Or.inr (Or.inr ⟨Q₁ h1, R₂ h2⟩)
      | exact Or.inr (Or.inr ⟨Q₂ h2, R₁ h1⟩)
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · rfl
  · rw [hinj₁ _ hp hq hq' h]
  · rw [hinj₂ _ hq hp hp' h]

private lemma lower_prod_injOn {n : ℕ} {t : ℝ} (ht : 1 < t) {C : Finset (ℤ × ℤ)}
    (hC : ∀ c ∈ C, c.1 < c.2 ∧ c.1 + 2 * c.2 ≤ -4) {f : ℤ × ℤ → ℕ → ℕ → ℕ}
    (hf : ∀ c ∈ C, lower_IsLatin (bin n t c.1) (bin n t c.2) (bin n t (-3 - c.1 - c.2)) (f c)) :
    Set.InjOn (lower_prod f) (lower_triples n t C) := by
  intro τ hτ τ' hτ' h
  rw [Finset.mem_coe] at hτ hτ'
  obtain ⟨⟨i, j⟩, ⟨p, q⟩⟩ := τ
  have hτ₀ := hτ
  rw [lower_mem_triples] at hτ₀
  obtain ⟨hc, hp, hq⟩ := hτ₀
  have hpq : p ≠ q := by
    rintro rfl
    have h1 := lower_eq_of_mem_bin ht hp hq
    have h2 := (hC _ hc).1
    simp only at h2
    omega
  have h₁ : p ∣ lower_prod f ⟨(i, j), (p, q)⟩ := dvd_mul_of_dvd_left (dvd_mul_right p q) _
  have h₂ : q ∣ lower_prod f ⟨(i, j), (p, q)⟩ := dvd_mul_of_dvd_left (dvd_mul_left q p) _
  exact lower_linear ht hC hf hτ hτ' hp hq hpq h₁ h₂ (h ▸ h₁) (h ▸ h₂)

/-- The three primes of a triple, with their bins. -/
private lemma lower_exists_of_mem_triples {n : ℕ} {t : ℝ} {C : Finset (ℤ × ℤ)}
    (hC : ∀ c ∈ C, c.1 < c.2 ∧ c.1 + 2 * c.2 ≤ -4) {R : ℤ}
    (hR : ∀ c ∈ C, -2 - c.1 - c.2 ≤ R) {f : ℤ × ℤ → ℕ → ℕ → ℕ}
    (hf : ∀ c ∈ C, lower_IsLatin (bin n t c.1) (bin n t c.2) (bin n t (-3 - c.1 - c.2)) (f c))
    {τ : Σ _ : ℤ × ℤ, ℕ × ℕ} (hτ : τ ∈ lower_triples n t C) :
    ∃ i j : ℤ, ∃ p q r : ℕ, lower_prod f τ = p * q * r ∧ p ∈ bin n t i ∧ q ∈ bin n t j ∧
      r ∈ bin n t (-3 - i - j) ∧ i < j ∧ i + 2 * j ≤ -4 ∧ -2 - i - j ≤ R := by
  obtain ⟨⟨i, j⟩, ⟨p, q⟩⟩ := τ
  rw [lower_mem_triples] at hτ
  obtain ⟨hc, hp, hq⟩ := hτ
  exact ⟨i, j, p, q, f (i, j) p q, rfl, hp, hq, (hf _ hc).1 p hp q hq, (hC _ hc).1, (hC _ hc).2,
    hR _ hc⟩

private lemma lower_le_floor_of_dvd_prod {n : ℕ} {t : ℝ} (ht : 1 < t) {C : Finset (ℤ × ℤ)}
    (hC : ∀ c ∈ C, c.1 < c.2 ∧ c.1 + 2 * c.2 ≤ -4) {R : ℤ}
    (hR : ∀ c ∈ C, -2 - c.1 - c.2 ≤ R) {f : ℤ × ℤ → ℕ → ℕ → ℕ}
    (hf : ∀ c ∈ C, lower_IsLatin (bin n t c.1) (bin n t c.2) (bin n t (-3 - c.1 - c.2)) (f c))
    {τ : Σ _ : ℤ × ℤ, ℕ × ℕ} (hτ : τ ∈ lower_triples n t C) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (h : ℓ ∣ lower_prod f τ) : ℓ ≤ ⌊t ^ R * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := by
  obtain ⟨i, j, p, q, r, he, hp, hq, hr, h1, h2, h3⟩ := lower_exists_of_mem_triples hC hR hf hτ
  rw [he] at h
  rcases lower_eq_of_dvd_mul_mul hℓ (lower_mem_bin hp).1 (lower_mem_bin hq).1 (lower_mem_bin hr).1 h
    with rfl | rfl | rfl
  · exact lower_le_floor ht hp (by omega)
  · exact lower_le_floor ht hq (by omega)
  · exact lower_le_floor ht hr (by omega)

private lemma lower_prod_mem_Icc {n : ℕ} {t : ℝ} (ht : 1 < t) {C : Finset (ℤ × ℤ)}
    (hC : ∀ c ∈ C, c.1 < c.2 ∧ c.1 + 2 * c.2 ≤ -4) {R : ℤ}
    (hR : ∀ c ∈ C, -2 - c.1 - c.2 ≤ R) {f : ℤ × ℤ → ℕ → ℕ → ℕ}
    (hf : ∀ c ∈ C, lower_IsLatin (bin n t c.1) (bin n t c.2) (bin n t (-3 - c.1 - c.2)) (f c))
    {τ : Σ _ : ℤ × ℤ, ℕ × ℕ} (hτ : τ ∈ lower_triples n t C) :
    1 ≤ lower_prod f τ ∧ lower_prod f τ ≤ n := by
  obtain ⟨i, j, p, q, r, he, hp, hq, hr, -, -, -⟩ := lower_exists_of_mem_triples hC hR hf hτ
  rw [he]
  refine ⟨?_, lower_mul_mul_le ht hp hq hr (by ring)⟩
  exact Nat.mul_pos (Nat.mul_pos (lower_mem_bin hp).1.pos (lower_mem_bin hq).1.pos)
    (lower_mem_bin hr).1.pos

/-! ### The family -/

/-- The family: the primes in `(Y, n]` together with the triple products. -/
private noncomputable def lower_family (n : ℕ) (t : ℝ) (C : Finset (ℤ × ℤ)) (R : ℤ)
    (f : ℤ × ℤ → ℕ → ℕ → ℕ) : Finset ℕ :=
  (Nat.primesLE n \ Nat.primesLE ⌊t ^ R * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊) ∪
    (lower_triples n t C).image (lower_prod f)

private lemma lower_mem_family {n : ℕ} {t : ℝ} {C : Finset (ℤ × ℤ)} {R : ℤ}
    {f : ℤ × ℤ → ℕ → ℕ → ℕ} {x : ℕ} :
    x ∈ lower_family n t C R f ↔ (x.Prime ∧ x ≤ n ∧ ⌊t ^ R * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ < x) ∨
      ∃ τ ∈ lower_triples n t C, lower_prod f τ = x := by
  simp only [lower_family, Finset.mem_union, Finset.mem_sdiff, Nat.mem_primesLE, Finset.mem_image]
  constructor
  · rintro (⟨⟨h1, h2⟩, h3⟩ | h)
    · exact Or.inl ⟨h2, h1, not_le.mp fun h => h3 ⟨h, h2⟩⟩
    · exact Or.inr h
  · rintro (⟨h1, h2, h3⟩ | h)
    · exact Or.inl ⟨⟨h2, h1⟩, fun h => absurd h.1 (not_le.mpr h3)⟩
    · exact Or.inr h

/-- A member of the family divisible by two distinct primes of a triple is that triple's
product. -/
private lemma lower_eq_of_two_dvd {n : ℕ} {t : ℝ} (ht : 1 < t) {C : Finset (ℤ × ℤ)}
    (hC : ∀ c ∈ C, c.1 < c.2 ∧ c.1 + 2 * c.2 ≤ -4) {R : ℤ} {f : ℤ × ℤ → ℕ → ℕ → ℕ}
    (hf : ∀ c ∈ C, lower_IsLatin (bin n t c.1) (bin n t c.2) (bin n t (-3 - c.1 - c.2)) (f c))
    {τ : Σ _ : ℤ × ℤ, ℕ × ℕ} (hτ : τ ∈ lower_triples n t C) {x : ℕ}
    (hx : x ∈ lower_family n t C R f)
    {ℓ₁ ℓ₂ : ℕ} {s₁ s₂ : ℤ} (h₁ : ℓ₁ ∈ bin n t s₁) (h₂ : ℓ₂ ∈ bin n t s₂) (hne : ℓ₁ ≠ ℓ₂)
    (h₁τ : ℓ₁ ∣ lower_prod f τ) (h₂τ : ℓ₂ ∣ lower_prod f τ) (h₁x : ℓ₁ ∣ x) (h₂x : ℓ₂ ∣ x) :
    x = lower_prod f τ := by
  rcases lower_mem_family.mp hx with ⟨hxp, -, -⟩ | ⟨τ', hτ', rfl⟩
  · exact absurd (((Nat.prime_dvd_prime_iff_eq (lower_mem_bin h₁).1 hxp).mp h₁x).trans
      ((Nat.prime_dvd_prime_iff_eq (lower_mem_bin h₂).1 hxp).mp h₂x).symm) hne
  · rw [lower_linear ht hC hf hτ hτ' h₁ h₂ hne h₁τ h₂τ h₁x h₂x]

/-- A prime of the family divides no other member of the family. -/
private lemma lower_not_dvd_of_large_prime {n : ℕ} {t : ℝ} (ht : 1 < t) {C : Finset (ℤ × ℤ)}
    (hC : ∀ c ∈ C, c.1 < c.2 ∧ c.1 + 2 * c.2 ≤ -4) {R : ℤ}
    (hR : ∀ c ∈ C, -2 - c.1 - c.2 ≤ R) {f : ℤ × ℤ → ℕ → ℕ → ℕ}
    (hf : ∀ c ∈ C, lower_IsLatin (bin n t c.1) (bin n t c.2) (bin n t (-3 - c.1 - c.2)) (f c))
    {a x : ℕ} (ha : a.Prime) (haY : ⌊t ^ R * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ < a)
    (hx : x ∈ lower_family n t C R f) (hax : a ≠ x) : ¬ a ∣ x := by
  intro h
  rcases lower_mem_family.mp hx with ⟨hxp, -, -⟩ | ⟨τ', hτ', rfl⟩
  · exact hax ((Nat.prime_dvd_prime_iff_eq ha hxp).mp h)
  · exact absurd (lower_le_floor_of_dvd_prod ht hC hR hf hτ' ha h) (not_le.mpr haY)

private lemma lower_good_family {n : ℕ} {t : ℝ} (ht : 1 < t) {C : Finset (ℤ × ℤ)}
    (hC : ∀ c ∈ C, c.1 < c.2 ∧ c.1 + 2 * c.2 ≤ -4) {R : ℤ}
    (hR : ∀ c ∈ C, -2 - c.1 - c.2 ≤ R) {f : ℤ × ℤ → ℕ → ℕ → ℕ}
    (hf : ∀ c ∈ C, lower_IsLatin (bin n t c.1) (bin n t c.2) (bin n t (-3 - c.1 - c.2)) (f c)) :
    Good (lower_family n t C R f) := by
  refine ⟨?_, fun a ha => ?_⟩
  · intro a ha b hb c hc hab hac hdvd
    rcases lower_mem_family.mp ha with ⟨hap, -, haY⟩ | ⟨τ, hτ, rfl⟩
    · rcases (Nat.Prime.dvd_mul hap).mp hdvd with h | h
      · exact lower_not_dvd_of_large_prime ht hC hR hf hap haY hb hab h
      · exact lower_not_dvd_of_large_prime ht hC hR hf hap haY hc hac h
    · obtain ⟨i, j, p, q, r, he, hp, hq, hr, h1, h2, -⟩ := lower_exists_of_mem_triples hC hR hf hτ
      have hpq : p ≠ q := fun h => by subst h; have := lower_eq_of_mem_bin ht hp hq; omega
      have hpr : p ≠ r := fun h => by subst h; have := lower_eq_of_mem_bin ht hp hr; omega
      have hqr : q ≠ r := fun h => by subst h; have := lower_eq_of_mem_bin ht hq hr; omega
      have dp : p ∣ lower_prod f τ := he ▸ dvd_mul_of_dvd_left (dvd_mul_right p q) r
      have dq : q ∣ lower_prod f τ := he ▸ dvd_mul_of_dvd_left (dvd_mul_left q p) r
      have dr : r ∣ lower_prod f τ := he ▸ dvd_mul_left r (p * q)
      have key : ∀ x ∈ lower_family n t C R f, lower_prod f τ ≠ x → ∀ ℓ₁ ℓ₂ : ℕ, ∀ s₁ s₂ : ℤ,
          ℓ₁ ∈ bin n t s₁ → ℓ₂ ∈ bin n t s₂ → ℓ₁ ≠ ℓ₂ → ℓ₁ ∣ lower_prod f τ →
          ℓ₂ ∣ lower_prod f τ → ℓ₁ ∣ x → ℓ₂ ∣ x → False :=
        fun x hx hax ℓ₁ ℓ₂ s₁ s₂ h₁ h₂ hne h₁τ h₂τ h₁x h₂x =>
          hax (lower_eq_of_two_dvd ht hC hf hτ hx h₁ h₂ hne h₁τ h₂τ h₁x h₂x).symm
      have hp' := (Nat.Prime.dvd_mul (lower_mem_bin hp).1).mp (dp.trans hdvd)
      have hq' := (Nat.Prime.dvd_mul (lower_mem_bin hq).1).mp (dq.trans hdvd)
      have hr' := (Nat.Prime.dvd_mul (lower_mem_bin hr).1).mp (dr.trans hdvd)
      rcases hp' with hpb | hpc <;> rcases hq' with hqb | hqc <;> rcases hr' with hrb | hrc <;>
        first
        | exact key b hb hab p q i j hp hq hpq dp dq hpb hqb
        | exact key b hb hab p r i _ hp hr hpr dp dr hpb hrb
        | exact key b hb hab q r j _ hq hr hqr dq dr hqb hrb
        | exact key c hc hac p q i j hp hq hpq dp dq hpc hqc
        | exact key c hc hac p r i _ hp hr hpr dp dr hpc hrc
        | exact key c hc hac q r j _ hq hr hqr dq dr hqc hrc
  · rcases lower_mem_family.mp ha with ⟨hap, -, -⟩ | ⟨τ, hτ, rfl⟩
    · exact hap.one_lt.le
    · exact (lower_prod_mem_Icc ht hC hR hf hτ).1

private lemma lower_family_subset {n : ℕ} {t : ℝ} (ht : 1 < t) {C : Finset (ℤ × ℤ)}
    (hC : ∀ c ∈ C, c.1 < c.2 ∧ c.1 + 2 * c.2 ≤ -4) {R : ℤ}
    (hR : ∀ c ∈ C, -2 - c.1 - c.2 ≤ R) {f : ℤ × ℤ → ℕ → ℕ → ℕ}
    (hf : ∀ c ∈ C, lower_IsLatin (bin n t c.1) (bin n t c.2) (bin n t (-3 - c.1 - c.2)) (f c)) :
    lower_family n t C R f ⊆ Finset.Icc 1 n := by
  intro x hx
  rw [Finset.mem_Icc]
  rcases lower_mem_family.mp hx with ⟨hxp, hxn, -⟩ | ⟨τ, hτ, rfl⟩
  · exact ⟨hxp.one_lt.le, hxn⟩
  · exact lower_prod_mem_Icc ht hC hR hf hτ

private lemma lower_card_family {n : ℕ} {t : ℝ} (ht : 1 < t) {C : Finset (ℤ × ℤ)}
    (hC : ∀ c ∈ C, c.1 < c.2 ∧ c.1 + 2 * c.2 ≤ -4) {R : ℤ}
    (hR : ∀ c ∈ C, -2 - c.1 - c.2 ≤ R) {f : ℤ × ℤ → ℕ → ℕ → ℕ}
    (hf : ∀ c ∈ C, lower_IsLatin (bin n t c.1) (bin n t c.2) (bin n t (-3 - c.1 - c.2)) (f c)) :
    (Nat.primeCounting n : ℝ) - Nat.primeCounting ⌊t ^ R * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊
      + ∑ c ∈ C, ((bin n t c.1).card : ℝ) * (bin n t c.2).card ≤
        (lower_family n t C R f).card := by
  have hdisj : Disjoint (Nat.primesLE n \ Nat.primesLE ⌊t ^ R * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊)
      ((lower_triples n t C).image (lower_prod f)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_sdiff, Nat.mem_primesLE, Nat.mem_primesLE] at hx
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hx'
    exact hx.2 ⟨lower_le_floor_of_dvd_prod ht hC hR hf hτ hx.1.2 dvd_rfl, hx.1.2⟩
  have hT : (lower_triples n t C).card = ∑ c ∈ C, (bin n t c.1).card * (bin n t c.2).card := by
    rw [lower_triples, Finset.card_sigma]
    simp only [Finset.card_product]
  have hsd := Finset.le_card_sdiff (Nat.primesLE ⌊t ^ R * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊)
    (Nat.primesLE n)
  rw [Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting] at hsd
  have hsd' : (Nat.primeCounting n : ℝ) ≤
      (Nat.primesLE n \ Nat.primesLE ⌊t ^ R * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊).card +
        Nat.primeCounting ⌊t ^ R * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ := by
    exact_mod_cast (by omega : Nat.primeCounting n ≤
      (Nat.primesLE n \ Nat.primesLE ⌊t ^ R * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊).card +
        Nat.primeCounting ⌊t ^ R * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊)
  rw [lower_family, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injOn (lower_prod_injOn ht hC hf), hT]
  push_cast
  linarith

private lemma lower_card_le_F {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 n) (hG : Good A) :
    A.card ≤ F n := by
  refine le_csSup ⟨n, ?_⟩ ⟨A, hA, hG, rfl⟩
  rintro k ⟨B, hB, -, rfl⟩
  simpa using Finset.card_le_card hB

/-! ### Assembling the lower bound -/

/-- **Lower bound.** Under the capacity condition, the primes above `t ^ R n ^ (1/3)` and the
products of the linear triples form a good set. -/
private theorem lower_F_ge (n : ℕ) (t : ℝ) (ht : 1 < t) (C : Finset (ℤ × ℤ))
    (hC : ∀ c ∈ C, c.1 < c.2 ∧ c.1 + 2 * c.2 ≤ -4) (R : ℤ)
    (hR : ∀ c ∈ C, -2 - c.1 - c.2 ≤ R)
    (hcap : ∀ c ∈ C, (bin n t c.1).card ≤ (bin n t (-3 - c.1 - c.2)).card ∧
      (bin n t c.2).card ≤ (bin n t (-3 - c.1 - c.2)).card) :
    (Nat.primeCounting n : ℝ) - Nat.primeCounting ⌊t ^ R * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊
      + ∑ c ∈ C, ((bin n t c.1).card : ℝ) * (bin n t c.2).card ≤ F n := by
  have hlat : ∀ c ∈ C, ∃ g,
      lower_IsLatin (bin n t c.1) (bin n t c.2) (bin n t (-3 - c.1 - c.2)) g :=
    fun c hc => lower_exists_isLatin _ _ _ (hcap c hc).1 (hcap c hc).2
  choose! f hf using hlat
  calc _ ≤ ((lower_family n t C R f).card : ℝ) := lower_card_family ht hC hR hf
    _ ≤ F n := by
      exact_mod_cast lower_card_le_F (lower_family_subset ht hC hR hf)
        (lower_good_family ht hC hR hf)

/-! ## The cells of the lower-bound construction -/

/-- The finite family of index cells `(i, j)` used for the lower bound. -/
private def cells (N : ℕ) : Finset (ℤ × ℤ) :=
  ((range N ×ˢ range N).image fun ab : ℕ × ℕ => ((-2 - ab.1 - ab.2 : ℤ), (-1 - ab.1 : ℤ))) ∪
    ((range N ×ˢ range N).image fun ab : ℕ × ℕ => ((-4 - 2 * ab.1 - ab.2 : ℤ), (ab.1 : ℤ)))

/-- Every cell `(i, j)` satisfies `i < j` and `i + 2 j ≤ -4`. -/
private theorem cells_valid {N : ℕ} : ∀ c ∈ cells N, c.1 < c.2 ∧ c.1 + 2 * c.2 ≤ -4 := by
  intro c hc
  simp only [cells, Finset.mem_union, Finset.mem_image, Finset.mem_product,
    Finset.mem_range] at hc
  rcases hc with ⟨⟨a, b⟩, _, rfl⟩ | ⟨⟨a, b⟩, _, rfl⟩ <;> dsimp only <;> omega

/-- The bins used by `cells N` have indices below `3 N`. -/
private theorem cells_bound {N : ℕ} : ∀ c ∈ cells N, -2 - c.1 - c.2 ≤ 3 * N := by
  intro c hc
  simp only [cells, Finset.mem_union, Finset.mem_image, Finset.mem_product,
    Finset.mem_range] at hc
  rcases hc with ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ | ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ <;> dsimp only <;> omega

/-- **Cell weight.** With `t = s⁻¹`, the total weight `∑ Δᵢ Δⱼ` of `cells N` is at least
`(1 - s ^ N) ^ 2 (s / (1 + s) + s ^ 2)`, which tends to `3 / 2` (Chojecki, Lemma 3.2). -/
private theorem cells_weight (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ) :
    (1 - s ^ N) ^ 2 * (s / (1 + s) + s ^ 2) ≤
      ∑ c ∈ cells N, (s⁻¹ ^ (c.1 + 1) - s⁻¹ ^ c.1) * (s⁻¹ ^ (c.2 + 1) - s⁻¹ ^ c.2) := by
  have hneg (m : ℕ) : s⁻¹ ^ (-(m : ℤ)) = s ^ m := by
    rw [zpow_neg, zpow_natCast, inv_pow, inv_inv]
  have hdisj : Disjoint
      ((range N ×ˢ range N).image fun ab : ℕ × ℕ => ((-2 - ab.1 - ab.2 : ℤ), (-1 - ab.1 : ℤ)))
      ((range N ×ˢ range N).image fun ab : ℕ × ℕ => ((-4 - 2 * ab.1 - ab.2 : ℤ), (ab.1 : ℤ))) := by
    rw [Finset.disjoint_left]
    intro c hc hc'
    simp only [Finset.mem_image] at hc hc'
    obtain ⟨⟨a, b⟩, _, rfl⟩ := hc
    obtain ⟨⟨a', b'⟩, _, h⟩ := hc'
    simp only [Prod.mk.injEq] at h
    omega
  rw [cells, Finset.sum_union hdisj, Finset.sum_image, Finset.sum_image]
  rotate_left
  · rintro ⟨a, b⟩ _ ⟨a', b'⟩ _ h
    simp only [Prod.mk.injEq] at h ⊢
    omega
  · rintro ⟨a, b⟩ _ ⟨a', b'⟩ _ h
    simp only [Prod.mk.injEq] at h ⊢
    omega
  have h1 : ∀ ab ∈ range N ×ˢ range N,
      (s⁻¹ ^ ((-2 - (ab.1 : ℤ) - ab.2) + 1) - s⁻¹ ^ (-2 - (ab.1 : ℤ) - ab.2)) *
        (s⁻¹ ^ ((-1 - (ab.1 : ℤ)) + 1) - s⁻¹ ^ (-1 - (ab.1 : ℤ))) =
        (1 - s) ^ 2 * s * ((s ^ 2) ^ ab.1 * s ^ ab.2) := by
    rintro ⟨a, b⟩ _
    dsimp only
    rw [show (-2 - (a : ℤ) - b) + 1 = -((1 + a + b : ℕ) : ℤ) by push_cast; ring,
      show (-2 - (a : ℤ) - b) = -((2 + a + b : ℕ) : ℤ) by push_cast; ring,
      show (-1 - (a : ℤ)) + 1 = -((a : ℕ) : ℤ) by ring,
      show (-1 - (a : ℤ)) = -((1 + a : ℕ) : ℤ) by push_cast; ring]
    simp only [hneg]
    ring
  have h2 : ∀ ab ∈ range N ×ˢ range N,
      (s⁻¹ ^ ((-4 - 2 * (ab.1 : ℤ) - ab.2) + 1) - s⁻¹ ^ (-4 - 2 * (ab.1 : ℤ) - ab.2)) *
        (s⁻¹ ^ ((ab.1 : ℤ) + 1) - s⁻¹ ^ (ab.1 : ℤ)) =
        (1 - s) ^ 2 * s ^ 2 * (s ^ ab.1 * s ^ ab.2) := by
    rintro ⟨a, b⟩ _
    dsimp only
    rw [show (-4 - 2 * (a : ℤ) - b) + 1 = -((3 + 2 * a + b : ℕ) : ℤ) by push_cast; ring,
      show (-4 - 2 * (a : ℤ) - b) = -((4 + 2 * a + b : ℕ) : ℤ) by push_cast; ring,
      show (a : ℤ) + 1 = ((a + 1 : ℕ) : ℤ) by push_cast; ring]
    simp only [hneg, zpow_natCast, inv_pow]
    field_simp
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_product, Finset.sum_product]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  set G := ∑ b ∈ range N, s ^ b with hGdef
  set G₁ := ∑ a ∈ range N, (s ^ 2) ^ a with hG₁def
  have hG : (1 - s) * G = 1 - s ^ N := mul_neg_geom_sum s N
  have hG₁ : (1 - s ^ 2) * G₁ = 1 - (s ^ 2) ^ N := mul_neg_geom_sum (s ^ 2) N
  have hsN : s ^ N ≤ 1 := pow_le_one₀ hs0.le hs1.le
  have hsN0 : 0 ≤ s ^ N := by positivity
  have h2N : (s ^ 2) ^ N ≤ s ^ N :=
    pow_le_pow_left₀ (sq_nonneg s) (by nlinarith) N
  have key1 : (1 - s) ^ 2 * s * (G₁ * G) = s * ((1 - s) * G₁) * (1 - s ^ N) := by
    rw [← hG]; ring
  have key2 : (1 - s) ^ 2 * s ^ 2 * (G * G) = s ^ 2 * (1 - s ^ N) ^ 2 := by
    rw [← hG]; ring
  have key3 : (1 - s ^ N) / (1 + s) ≤ (1 - s) * G₁ := by
    rw [div_le_iff₀ (by linarith)]
    have : (1 - s) * G₁ * (1 + s) = 1 - (s ^ 2) ^ N := by rw [← hG₁]; ring
    linarith
  rw [key1, key2]
  calc (1 - s ^ N) ^ 2 * (s / (1 + s) + s ^ 2)
      = s * ((1 - s ^ N) / (1 + s)) * (1 - s ^ N) + s ^ 2 * (1 - s ^ N) ^ 2 := by
        field_simp
    _ ≤ s * ((1 - s) * G₁) * (1 - s ^ N) + s ^ 2 * (1 - s ^ N) ^ 2 := by
        gcongr

/-! ## Limits and the main estimate -/

/-- The bin `r` holds `(3 + o(1)) (t ^ (r + 1) - t ^ r) n ^ (1/3) / log n` primes. -/
private theorem tendsto_bin_card (t : ℝ) (ht : 1 < t) (r : ℤ) :
    Tendsto (fun n : ℕ => ((bin n t r).card : ℝ) / ((n : ℝ) ^ ((1 : ℝ) / 3) / Real.log n))
      atTop (𝓝 (3 * (t ^ (r + 1) - t ^ r))) := by
  have h0 : 0 < t := by linarith
  have h1 := tendsto_primeCounting_floor_mul (t ^ (r + 1)) (zpow_pos h0 _)
  have h2 := tendsto_primeCounting_floor_mul (t ^ r) (zpow_pos h0 _)
  rw [mul_sub]
  refine (h1.sub h2).congr fun n => ?_
  rw [bin, card_primesIoc, sub_div]
  apply Nat.floor_le_floor
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact zpow_le_zpow_right₀ ht.le (by omega)

private theorem tendsto_log_div_cbrt :
    Tendsto (fun n : ℕ => Real.log n / (n : ℝ) ^ ((1 : ℝ) / 3)) atTop (𝓝 0) :=
  ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).tendsto_div_nhds_zero).comp
    tendsto_natCast_atTop_atTop

private theorem tendsto_rpow_div_S :
    Tendsto (fun n : ℕ => (n : ℝ) ^ ((3 : ℝ) / 5) / ((n : ℝ) ^ ((2 : ℝ) / 3) / Real.log n ^ 2))
      atTop (𝓝 0) := by
  have h := ((isLittleO_log_rpow_rpow_atTop 2
    (by norm_num : (0 : ℝ) < 1 / 15)).tendsto_div_nhds_zero).comp tendsto_natCast_atTop_atTop
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hn' : (0 : ℝ) < n := by positivity
  have hsplit : (n : ℝ) ^ ((2 : ℝ) / 3) = (n : ℝ) ^ ((3 : ℝ) / 5) * (n : ℝ) ^ ((1 : ℝ) / 15) := by
    rw [← Real.rpow_add hn']
    norm_num
  simp only [Function.comp, Real.rpow_two]
  rw [hsplit]
  have h35 : 0 < (n : ℝ) ^ ((3 : ℝ) / 5) := by positivity
  have h15 : 0 < (n : ℝ) ^ ((1 : ℝ) / 15) := by positivity
  field_simp

/-- The normalised size of the triple family minus the primes it removes. -/
private theorem tendsto_lower (t : ℝ) (ht : 1 < t) (C : Finset (ℤ × ℤ)) (R : ℤ) :
    Tendsto (fun n : ℕ => (∑ c ∈ C, ((bin n t c.1).card : ℝ) * (bin n t c.2).card
        - Nat.primeCounting ⌊t ^ R * (n : ℝ) ^ ((1 : ℝ) / 3)⌋₊) /
        ((n : ℝ) ^ ((2 : ℝ) / 3) / Real.log n ^ 2)) atTop
      (𝓝 (9 * ∑ c ∈ C, (t ^ (c.1 + 1) - t ^ c.1) * (t ^ (c.2 + 1) - t ^ c.2))) := by
  have hsum := tendsto_finsetSum C fun c _ =>
    (tendsto_bin_card t ht c.1).mul (tendsto_bin_card t ht c.2)
  have hY := (tendsto_primeCounting_floor_mul (t ^ R) (zpow_pos (by linarith) _)).mul
    tendsto_log_div_cbrt
  have h := hsum.sub hY
  rw [mul_zero, sub_zero] at h
  convert h.congr' ?_ using 2
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  · filter_upwards [eventually_gt_atTop 1] with n hn
    have hy : 0 < (n : ℝ) ^ ((1 : ℝ) / 3) := by positivity
    have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
    rw [← cbrt_sq n, sub_div, Finset.sum_div]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => ?_
      field_simp
    · field_simp

/-- A higher bin eventually holds more primes than a lower one. -/
private theorem eventually_card_bin_le (t : ℝ) (ht : 1 < t) (i k : ℤ) (hik : i < k) :
    ∀ᶠ n : ℕ in atTop, (bin n t i).card ≤ (bin n t k).card := by
  have h0 : 0 < t := by linarith
  have hlt : 3 * (t ^ (i + 1) - t ^ i) < 3 * (t ^ (k + 1) - t ^ k) := by
    rw [zpow_add_one₀ h0.ne', zpow_add_one₀ h0.ne']
    have := zpow_lt_zpow_right₀ ht hik
    nlinarith
  filter_upwards [(tendsto_bin_card t ht i).eventually_lt (tendsto_bin_card t ht k) hlt,
    eventually_gt_atTop 1] with n hn hn1
  have hy : 0 < (n : ℝ) ^ ((1 : ℝ) / 3) := by positivity
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn1)
  have hM : 0 < (n : ℝ) ^ ((1 : ℝ) / 3) / Real.log n := by positivity
  have := (div_lt_div_iff_of_pos_right hM).mp hn
  exact_mod_cast this.le

/-- **Main estimate.** `(F n - π n) / (n ^ (2/3) / (log n) ^ 2) → 27 / 2`. -/
private theorem tendsto_main :
    Tendsto (fun n : ℕ => (((F n : ℤ) - (Nat.primeCounting n : ℤ)) : ℝ) /
      ((n : ℝ) ^ ((2 : ℝ) / 3) / (Real.log n) ^ 2)) atTop (𝓝 (27 / 2)) := by
  have hS : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) ^ ((2 : ℝ) / 3) / Real.log n ^ 2 := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    have := Real.log_pos (by exact_mod_cast hn : (1 : ℝ) < n)
    positivity
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨s, hs0, hs1, hsa⟩ : ∃ s : ℝ, 0 < s ∧ s < 1 ∧ a < 9 * (s / (1 + s) + s ^ 2) := by
      have hcont : Tendsto (fun s : ℝ => 9 * (s / (1 + s) + s ^ 2)) (𝓝[<] 1)
          (𝓝 (27 / 2)) := by
        have hc : ContinuousAt (fun s : ℝ => 9 * (s / (1 + s) + s ^ 2)) 1 := by
          fun_prop (disch := norm_num)
        convert hc.tendsto.mono_left nhdsWithin_le_nhds using 2
        norm_num
      have h1 := hcont.eventually (lt_mem_nhds ha)
      have h2 : ∀ᶠ s in 𝓝[<] (1 : ℝ), s ∈ Set.Ioo 0 1 := Ioo_mem_nhdsLT (by norm_num)
      obtain ⟨s, h1, h2⟩ := (h1.and h2).exists
      exact ⟨s, h2.1, h2.2, h1⟩
    obtain ⟨N, hN⟩ : ∃ N : ℕ, a < 9 * ((1 - s ^ N) ^ 2 * (s / (1 + s) + s ^ 2)) := by
      have hlim : Tendsto (fun N : ℕ => 9 * ((1 - s ^ N) ^ 2 * (s / (1 + s) + s ^ 2))) atTop
          (𝓝 (9 * ((1 - 0) ^ 2 * (s / (1 + s) + s ^ 2)))) :=
        (((tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one hs0.le hs1)).pow
          2).mul tendsto_const_nhds).const_mul 9
      rw [sub_zero, one_pow, one_mul] at hlim
      exact (hlim.eventually (lt_mem_nhds hsa)).exists
    have ht : 1 < s⁻¹ := (one_lt_inv₀ hs0).mpr hs1
    have hW := cells_weight s hs0 hs1 N
    have hev := (tendsto_lower s⁻¹ ht (cells N) (3 * N)).eventually
      (lt_mem_nhds (lt_of_lt_of_le hN (by linarith)))
    have hcap : ∀ᶠ n : ℕ in atTop, ∀ c ∈ cells N,
        (bin n s⁻¹ c.1).card ≤ (bin n s⁻¹ (-3 - c.1 - c.2)).card ∧
          (bin n s⁻¹ c.2).card ≤ (bin n s⁻¹ (-3 - c.1 - c.2)).card := by
      rw [Finset.eventually_all]
      intro c hc
      obtain ⟨h1, h2⟩ := cells_valid c hc
      exact (eventually_card_bin_le _ ht _ _ (by omega)).and
        (eventually_card_bin_le _ ht _ _ (by omega))
    filter_upwards [hev, hcap, hS] with n hn hcapn hSn
    have hF := lower_F_ge n s⁻¹ ht (cells N) cells_valid (3 * N) cells_bound hcapn
    refine lt_of_lt_of_le hn ?_
    apply div_le_div_of_nonneg_right _ hSn.le
    push_cast
    linarith
  · have hδ : 0 < (b - 27 / 2) / 4 := by linarith
    set δ := (b - 27 / 2) / 4 with hδdef
    have h1 := tendsto_rpow_div_S.eventually (gt_mem_nhds hδ)
    have h2 : Tendsto (fun n : ℕ => (((Nat.primeCounting ⌊(n : ℝ) ^ ((1 : ℝ) / 3)⌋₊ : ℝ) ^ 2
        + Nat.primeCounting ⌊(n : ℝ) ^ ((1 : ℝ) / 3)⌋₊) / 2) /
        ((n : ℝ) ^ ((2 : ℝ) / 3) / Real.log n ^ 2)) atTop (𝓝 (9 / 2)) := by
      have hA := tendsto_primeCounting_floor_mul 1 one_pos
      simp only [one_mul] at hA
      have h := ((hA.pow 2).add (hA.mul tendsto_log_div_cbrt)).div_const 2
      norm_num at h
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop 1] with n hn
      have hy : 0 < (n : ℝ) ^ ((1 : ℝ) / 3) := by positivity
      have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
      rw [← cbrt_sq n]
      field_simp
    have h2' := h2.eventually (gt_mem_nhds (show 9 / 2 < 9 / 2 + δ by linarith))
    have h3 := tail_sum_bigPrimes_le δ hδ
    filter_upwards [h1, h2', h3, hS, eventually_ge_atTop 1] with n h1n h2n h3n hSn hn1
    have hF := upper_F_le n hn1
    rw [div_lt_iff₀ hSn] at h1n h2n ⊢
    push_cast
    nlinarith

/--
**Erdős Problem 793 has a positive answer.** Let $F(n)$ be the largest size of a set
$A \subseteq \{1, \dots, n\}$ such that $a \nmid bc$ whenever $a, b, c \in A$ with $a \ne b$ and
$a \ne c$ ($b = c$ is allowed), and let $\pi(n)$ be the number of primes at most $n$. Then there
is a real constant $C > 0$ such that $(F(n) - \pi(n)) / (n^{2/3} / (\log n)^2) \to C$ as
$n \to \infty$.

Chojecki (2026, Theorem 1.1) proves this with $C = 27/2$.

Source: P. Chojecki, The Second
Term for Strongly 2-Primitive Sets, arXiv preprint (2026), arXiv:2607.15306,
https://arxiv.org/abs/2607.15306. Moved from
`OpenConjectures/NumberTheory/ErdosDivisibilityFamilyGrowth`.
-/
theorem conjecture_holds : conjecture :=
  ⟨27 / 2, by norm_num, tendsto_main⟩

end MathlibExt.NumberTheory.ErdosDivisibilityFamilyGrowthWanted
