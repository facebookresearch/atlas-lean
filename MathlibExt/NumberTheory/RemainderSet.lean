/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Sets of remainders and unbounded drops in their size

For a natural number `n`, the remainder set is `S(n) = {n mod k : 1 ≤ k ≤ ⌊n/2⌋}` and the
remainder count is `s(n) = |S(n)|` (OEIS A283190). The main result,
`remainderCount_drops_unbounded`, shows that the differences `s(n+1) - s(n)` are unbounded
below: for every natural number `M` there are infinitely many `n` with `s(n+1) + M ≤ s(n)`.
This is Proposition 4 of Omkar Baraskar and Ingrid Vukusic, *Bounds for sets of remainders*,
arXiv:2508.20853v1 (2025), Section 4, the preprint of the journal article that the docstrings
below cite.

For the eventual lower bound, the odd primes associated with lost remainders
grow at least by squaring, so their number is bounded by a double logarithm.

The proof of unbounded drops follows the preprint. Every nonzero element of `S(n+1)` is
`r + 1` for some `r ∈ S(n)` (Lemma 6 of the preprint), so `s(n+1) + |T| ≤ s(n) + 1` for every
set `T ⊆ S(n)` of elements `r` with `r + 1 ∉ S(n+1)`. If `n + 1 = d (p + 1)` with `p` prime and
`d` free of primes below `p`, then `d - 1` is such an element (Lemma 9 of the preprint characterizes
all of them). Given a prime `p`, Dirichlet's theorem on primes in arithmetic progressions gives a
larger prime `p'` with `p' ≡ p (mod (p + 1) (p - 1)!)`. Then `(p' + 1)/(p + 1)` has no prime
factor below `p`, so every such factorization of `p + 1` gives one of `p' + 1`, and
`p' + 1 = 1 · (p' + 1)` is one more. Iterating from any prime gives `n` with arbitrarily many
such factorizations of `n + 1`. The preprint chooses the arithmetic progression with the
Chinese remainder theorem instead.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Remainder set.** For a natural number $n$, the remainder set is
$S(n) = \{\, n \bmod k : 1 \le k \le \lfloor n/2 \rfloor \,\}$, the set of remainders of $n$
modulo the integers from $1$ to $\lfloor n/2 \rfloor$.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Section 1 (definition of `S(n)`). -/
public def remainderSet (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (n / 2)).image (n % ·)

/-- **Remainder count.** For a natural number $n$, $s(n)$ is the number of elements of the
remainder set $S(n)$, that is, the number of distinct values of $n \bmod k$ for
$1 \le k \le \lfloor n/2 \rfloor$ (OEIS A283190).

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Section 1 (definition of `s(n)`). -/
public def remainderCount (n : ℕ) : ℕ :=
  (remainderSet n).card

/-- Membership in the remainder set, unfolded. -/
private theorem mem_remainderSet_iff {n r : ℕ} :
    r ∈ remainderSet n ↔ ∃ k, 1 ≤ k ∧ k ≤ n / 2 ∧ n % k = r := by
  simp only [remainderSet, Finset.mem_image, Finset.mem_Icc, and_assoc]

/-- If `n + 1 = (p + 1) d` with `p` prime, then `d - 1 = n mod d` lies in `S(n)`. -/
private theorem div_sub_one_mem_remainderSet {n p : ℕ} (hp : p.Prime) (hdvd : p + 1 ∣ n + 1) :
    (n + 1) / (p + 1) - 1 ∈ remainderSet n := by
  obtain ⟨d, hd⟩ := hdvd
  have hp2 := hp.two_le
  rw [hd, Nat.mul_div_cancel_left d (by omega), mem_remainderSet_iff]
  have hd0 : 0 < d := Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at hd; omega
  have h1 : n + 1 = d * p + d := by rw [hd]; ring
  have h2 : d * 2 ≤ d * p := Nat.mul_le_mul_left d hp2
  have hn : n = d - 1 + d * p := by omega
  refine ⟨d, hd0, by omega, ?_⟩
  rw [hn, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- If `n + 1 = (p + 1) d` with `p` prime and `d` free of primes below `p`, then `d ∉ S(n + 1)`:
a modulus `k` with `(n + 1) mod k = d` would divide `n + 1 - d = d p` and exceed `d`, so it
would be `d p`, which is larger than `(n + 1)/2`. -/
private theorem div_notMem_remainderSet_succ {n p : ℕ} (hp : p.Prime) (hdvd : p + 1 ∣ n + 1)
    (hfac : ∀ q, q.Prime → q ∣ (n + 1) / (p + 1) → p ≤ q) :
    (n + 1) / (p + 1) ∉ remainderSet (n + 1) := by
  obtain ⟨d, hd⟩ := hdvd
  have hp2 := hp.two_le
  have hdiv : (n + 1) / (p + 1) = d := by rw [hd, Nat.mul_div_cancel_left d (by omega)]
  rw [hdiv] at hfac ⊢
  rw [mem_remainderSet_iff]
  rintro ⟨k, hk1, hk2, hmod⟩
  have hd0 : 0 < d := Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at hd; omega
  have h1 : n + 1 = d * p + d := by rw [hd]; ring
  have hdk : d < k := hmod ▸ Nat.mod_lt _ (by omega)
  have hkdvd : k ∣ d * p := by
    have h2 : k ∣ n + 1 - (n + 1) % k := Nat.dvd_sub_mod (n + 1)
    rwa [hmod, show n + 1 - d = d * p by omega] at h2
  obtain ⟨c, hc⟩ := hkdvd
  have hdp : 0 < d * p := Nat.mul_pos hd0 (by omega)
  have hcp : c < p := by
    by_contra h
    have h3 : d * p < k * p := Nat.mul_lt_mul_of_pos_right hdk (by omega)
    have h4 : k * p ≤ k * c := Nat.mul_le_mul_left k (not_lt.1 h)
    omega
  have hc1 : c = 1 := by
    by_contra hne
    obtain ⟨q, hq, hqc⟩ := Nat.exists_prime_and_dvd hne
    have hc0 : 0 < c := Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at hc; omega
    have hqle : q ≤ c := Nat.le_of_dvd hc0 hqc
    have hqdp : q ∣ d * p := by rw [hc]; exact hqc.mul_left k
    rcases hq.dvd_mul.1 hqdp with hqd | hqp
    · have := hfac q hq hqd
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hq hp).1 hqp
      omega
  rw [hc1, Nat.mul_one] at hc
  omega

/-- Every nonzero element of `S(n + 1)` is `r + 1` for some `r ∈ S(n)`. So if `r + 1 ∉ S(n + 1)`
for every `r ∈ T`, then `S(n + 1) ⊆ {0} ∪ {r + 1 : r ∈ S(n) \ T}`. -/
private theorem remainderSet_succ_subset (n : ℕ) (T : Finset ℕ)
    (hT : ∀ r ∈ T, r + 1 ∉ remainderSet (n + 1)) :
    remainderSet (n + 1) ⊆ insert 0 ((remainderSet n \ T).image (· + 1)) := by
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact Finset.mem_insert_self _ _
  apply Finset.mem_insert_of_mem
  rw [Finset.mem_image]
  refine ⟨j - 1, Finset.mem_sdiff.2 ⟨?_, fun hmem => hT _ hmem ?_⟩, by omega⟩
  · obtain ⟨k, hk1, hk2, hmod⟩ := mem_remainderSet_iff.1 hj
    have hjk : j < k := hmod ▸ Nat.mod_lt _ (by omega)
    rw [mem_remainderSet_iff]
    refine ⟨k, hk1, ?_, ?_⟩
    · by_contra hk
      have h2 : n + 1 = k * 2 := by omega
      have h3 : (n + 1) % k = 0 := by rw [h2]; simp
      omega
    · have key := Nat.div_add_mod (n + 1) k
      rw [hmod] at key
      have hn : n = j - 1 + k * ((n + 1) / k) := by omega
      rw [hn, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · rwa [Nat.sub_add_cancel hj0]

/-- **The drop criterion.** If `P` is a finite set of primes `p` with `p + 1 ∣ n + 1` such that
`(n + 1)/(p + 1)` has no prime factor below `p`, then `s(n + 1) + |P| ≤ s(n) + 1`. -/
private theorem remainderCount_succ_add_card_le {n : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p + 1 ∣ n + 1 ∧ ∀ q, q.Prime → q ∣ (n + 1) / (p + 1) → p ≤ q) :
    remainderCount (n + 1) + P.card ≤ remainderCount n + 1 := by
  have hpos : ∀ p ∈ P, 0 < (n + 1) / (p + 1) := fun p hp =>
    Nat.div_pos (Nat.le_of_dvd (by omega) (hP p hp).2.1) (by omega)
  obtain ⟨T, hT⟩ : ∃ T, T = P.image (fun p => (n + 1) / (p + 1) - 1) := ⟨_, rfl⟩
  have hTcard : T.card = P.card := by
    rw [hT]
    refine Finset.card_image_of_injOn fun p hp p' hp' h => ?_
    have h' : (n + 1) / (p + 1) = (n + 1) / (p' + 1) := by
      have := hpos p hp
      have := hpos p' hp'
      omega
    have e1 := Nat.div_div_self (hP p hp).2.1 (by omega)
    have e2 := Nat.div_div_self (hP p' hp').2.1 (by omega)
    rw [h', e2] at e1
    omega
  have hTsub : T ⊆ remainderSet n := by
    intro r hr
    rw [hT] at hr
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hr
    exact div_sub_one_mem_remainderSet (hP p hp).1 (hP p hp).2.1
  have hTnot : ∀ r ∈ T, r + 1 ∉ remainderSet (n + 1) := by
    intro r hr
    rw [hT] at hr
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hr
    rw [Nat.sub_add_cancel (hpos p hp)]
    exact div_notMem_remainderSet_succ (hP p hp).1 (hP p hp).2.1 (hP p hp).2.2
  have h1 := Finset.card_le_card (remainderSet_succ_subset n T hTnot)
  have h2 := Finset.card_insert_le 0 ((remainderSet n \ T).image (· + 1))
  have h3 := Finset.card_image_le (s := remainderSet n \ T) (f := (· + 1))
  have h4 := Finset.card_sdiff_add_card_eq_card hTsub
  unfold remainderCount
  omega

/-- The remainder count increases by at most one at each step. -/
private theorem remainderCount_succ_le (n : ℕ) : remainderCount (n + 1) ≤ remainderCount n + 1 := by
  simpa using remainderCount_succ_add_card_le (n := n) ∅ (by simp)

/-- The successor set consists of zero and the shifted remainders that are retained. -/
private theorem remainderSet_succ_eq_shift {n : ℕ} (hn : 1 ≤ n) :
    remainderSet (n + 1) =
      insert 0 (((remainderSet n).filter fun r => r + 1 ∈ remainderSet (n + 1)).image (· + 1)) := by
  apply Finset.Subset.antisymm
  · intro r hr
    have h := remainderSet_succ_subset n ∅ (by simp) hr
    simp only [Finset.sdiff_empty] at h
    rcases Finset.mem_insert.1 h with rfl | h
    · exact Finset.mem_insert_self _ _
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h
      exact Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨j, Finset.mem_filter.2 ⟨hj, hr⟩, rfl⟩)
  · intro r hr
    rcases Finset.mem_insert.1 hr with rfl | hr
    · exact mem_remainderSet_iff.2 ⟨1, le_rfl, by omega, Nat.mod_one _⟩
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hr
      exact (Finset.mem_filter.1 hj).2

/-- A remainder is lost at the next step exactly when its successor is the complementary
factor of `p + 1`, for a prime `p` no larger than any prime factor of that complementary factor. -/
private theorem lost_remainder_iff {n r : ℕ} :
    (r ∈ remainderSet n ∧ r + 1 ∉ remainderSet (n + 1)) ↔
      ∃ p, p.Prime ∧ n + 1 = (p + 1) * (r + 1) ∧
        ∀ q, q.Prime → q ∣ r + 1 → p ≤ q := by
  constructor
  · rintro ⟨hr, hnot⟩
    obtain ⟨k, hk1, hk2, hmod⟩ := mem_remainderSet_iff.1 hr
    let d := r + 1
    have hd : 0 < d := by simp [d]
    have hdk : d ≤ k := by
      have h := Nat.mod_lt n (show 0 < k by omega)
      rw [hmod] at h
      dsimp [d]
      omega
    have heq : n + 1 = k * (n / k) + d := by
      have h := Nat.div_add_mod n k
      rw [hmod] at h
      dsimp [d]
      omega
    have hk : k = d := by
      by_contra hne
      apply hnot
      refine mem_remainderSet_iff.2 ⟨k, hk1, by omega, ?_⟩
      change (n + 1) % k = d
      rw [heq, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    let p := n / d
    have hp2 : 2 ≤ p := by
      change 2 ≤ n / d
      exact (Nat.le_div_iff_mul_le hd).2 (by omega)
    rw [hk] at heq
    change n + 1 = d * p + d at heq
    have hfac : ∀ q, q.Prime → q ∣ d * p → p ≤ q := by
      intro q hq hqdp
      by_contra! hqp
      obtain ⟨c, hc⟩ := hqdp
      have hdc : d < c := by
        by_contra! hcd
        have h1 := Nat.mul_le_mul_left q hcd
        have h2 := Nat.mul_lt_mul_of_pos_right hqp hd
        rw [Nat.mul_comm p d] at h2
        omega
      have hhalf : c ≤ (n + 1) / 2 := by
        have h := Nat.mul_le_mul_right c hq.two_le
        omega
      apply hnot
      refine mem_remainderSet_iff.2 ⟨c, by omega, hhalf, ?_⟩
      change (n + 1) % c = d
      rw [heq, hc, Nat.add_comm, Nat.mul_comm q c, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hdc]
    have hminPrime := Nat.minFac_prime (n := p) (by omega)
    have hminDvd := Nat.minFac_dvd p
    have hminEq : p.minFac = p := le_antisymm (Nat.le_of_dvd (by omega) hminDvd)
      (hfac _ hminPrime (hminDvd.mul_left d))
    have hp : p.Prime := hminEq ▸ hminPrime
    refine ⟨p, hp, ?_, fun q hq hqd => hfac q hq (hqd.mul_right p)⟩
    change n + 1 = (p + 1) * d
    rw [heq]
    ring
  · rintro ⟨p, hp, heq, hfac⟩
    have hdvd : p + 1 ∣ n + 1 := ⟨r + 1, heq⟩
    have hdiv : (n + 1) / (p + 1) = r + 1 := by
      rw [heq, Nat.mul_div_cancel_left _ (by omega)]
    have hfac' : ∀ q, q.Prime → q ∣ (n + 1) / (p + 1) → p ≤ q := by
      simpa only [hdiv] using hfac
    constructor
    · simpa [hdiv] using div_sub_one_mem_remainderSet hp hdvd
    · simpa only [hdiv] using div_notMem_remainderSet_succ hp hdvd hfac'

/-- The odd primes that can account for a remainder lost between `n` and `n + 1`. -/
private def oddDropPrimes (n : ℕ) : Finset ℕ :=
  (Finset.Icc 3 (n + 1)).filter fun p =>
    p.Prime ∧ p + 1 ∣ n + 1 ∧ ∀ q ∈ Finset.range p, q.Prime → ¬ q ∣ (n + 1) / (p + 1)

private theorem mem_oddDropPrimes {n p : ℕ} :
    p ∈ oddDropPrimes n ↔
      3 ≤ p ∧ p.Prime ∧ p + 1 ∣ n + 1 ∧ ∀ q, q.Prime → q ∣ (n + 1) / (p + 1) → p ≤ q := by
  simp only [oddDropPrimes, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨hp3, -⟩, hp, hdvd, hfac⟩
    exact ⟨hp3, hp, hdvd, fun q hq hqd => le_of_not_gt fun hqp => hfac q hqp hq hqd⟩
  · rintro ⟨hp3, hp, hdvd, hfac⟩
    have hle := Nat.le_of_dvd (by omega) hdvd
    exact ⟨⟨hp3, by omega⟩, hp, hdvd, fun q hqp hq hqd => (Nat.not_lt_of_ge (hfac q hq hqd)) hqp⟩

/-- The number of lost remainders accounts exactly for the count change after adding zero. -/
private theorem remainderCount_succ_add_card_lost {n : ℕ} (hn : 1 ≤ n) :
    remainderCount (n + 1) + ((remainderSet n).filter fun r => r + 1 ∉ remainderSet (n + 1)).card =
      remainderCount n + 1 := by
  let lost := (remainderSet n).filter fun r => r + 1 ∉ remainderSet (n + 1)
  have hshift : (remainderSet n).filter (fun r => r + 1 ∈ remainderSet (n + 1)) =
      remainderSet n \ lost := by
    ext r
    simp only [lost, Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hzero : 0 ∉ ((remainderSet n \ lost).image (· + 1)) := by
    rw [Finset.mem_image]
    rintro ⟨r, -, hr⟩
    omega
  have hcard := Finset.card_sdiff_add_card_eq_card
    (Finset.filter_subset (fun r => r + 1 ∉ remainderSet (n + 1)) (remainderSet n))
  change (remainderSet (n + 1)).card + lost.card = (remainderSet n).card + 1
  rw [remainderSet_succ_eq_shift hn, hshift, Finset.card_insert_of_notMem hzero,
    Finset.card_image_of_injOn (fun _ _ _ _ h => Nat.add_right_cancel h)]
  change (remainderSet n \ lost).card + lost.card = _ at hcard
  omega

/-- A lost remainder determines an odd candidate prime or the single exception `2`.
The zero in the successor remainder set absorbs that exception in the count bound. -/
private theorem remainderCount_le_succ_add_card_oddDropPrimes {n : ℕ} (hn : 1 ≤ n) :
    remainderCount n ≤ remainderCount (n + 1) + (oddDropPrimes n).card := by
  let lost := (remainderSet n).filter fun r => r + 1 ∉ remainderSet (n + 1)
  let f : ℕ → ℕ := fun r => (n + 1) / (r + 1) - 1
  have hdata : ∀ r ∈ lost, (f r).Prime ∧ n + 1 = (f r + 1) * (r + 1) ∧
      ∀ q, q.Prime → q ∣ r + 1 → f r ≤ q := by
    intro r hr
    obtain ⟨p, hp, heq, hfac⟩ := lost_remainder_iff.1 (Finset.mem_filter.1 hr)
    have hf : f r = p := by
      dsimp [f]
      rw [heq, Nat.mul_div_cancel _ (by omega)]
      omega
    rw [hf]
    exact ⟨hp, heq, hfac⟩
  have hle : lost.card ≤ (insert 2 (oddDropPrimes n)).card := by
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro r hr
      obtain ⟨hp, heq, hfac⟩ := hdata r hr
      change f r ∈ insert 2 (oddDropPrimes n)
      by_cases h2 : f r = 2
      · exact Finset.mem_insert.2 (Or.inl h2)
      · apply Finset.mem_insert_of_mem
        have hp2 := hp.two_le
        refine mem_oddDropPrimes.2 ⟨by omega, hp, ⟨r + 1, heq⟩, fun q hq hqd => hfac q hq ?_⟩
        rwa [heq, Nat.mul_div_cancel_left _ (by omega)] at hqd
    · intro r hr r' hr' he
      have e := (hdata r hr).2.1
      have e' := (hdata r' hr').2.1
      rw [he] at e
      have hmul := e.symm.trans e'
      have hcancel := Nat.eq_of_mul_eq_mul_left (by omega) hmul
      omega
  have hcount := remainderCount_succ_add_card_lost hn
  change remainderCount (n + 1) + lost.card = remainderCount n + 1 at hcount
  have hinsert := Finset.card_insert_le 2 (oddDropPrimes n)
  omega

/-- **Long chains.** For all `J` and `B` there are a prime `p > B` and a set of `J` primes `q`
with `q + 1 ∣ p + 1` such that `(p + 1)/(q + 1)` has no prime factor below `q`. Each step
applies Dirichlet's theorem to the progression `p' ≡ p (mod (p + 1) (p - 1)!)`. -/
private theorem exists_prime_chain (J B : ℕ) : ∃ p, B < p ∧ p.Prime ∧ ∃ P : Finset ℕ,
    P.card = J ∧ ∀ q ∈ P, q.Prime ∧ q + 1 ∣ p + 1 ∧
      ∀ r, r.Prime → r ∣ (p + 1) / (q + 1) → q ≤ r := by
  induction J generalizing B with
  | zero =>
    obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (B + 1)
    exact ⟨p, by omega, hp2, ∅, rfl, by simp⟩
  | succ J ih =>
    obtain ⟨p, hBp, hp, P, hcard, hP⟩ := ih B
    have hp2 := hp.two_le
    obtain ⟨F, hF⟩ : ∃ F, F = Nat.factorial (p - 1) := ⟨_, rfl⟩
    have hN0 : (p + 1) * F ≠ 0 := by
      rw [hF]
      exact Nat.mul_ne_zero (by omega) (Nat.factorial_ne_zero _)
    have hcop : p.Coprime ((p + 1) * F) := by
      refine Nat.Coprime.mul_right (Nat.coprime_self_add_right.2 (Nat.coprime_one_right p)) ?_
      refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_
      rw [hF] at h
      have := (Nat.Prime.dvd_factorial hp).1 h
      omega
    obtain ⟨p', hpp', hp', hmod⟩ := Nat.forall_exists_prime_gt_and_modEq p hN0 hcop
    obtain ⟨x, hx⟩ := (Nat.modEq_iff_dvd' hpp'.le).1 hmod.symm
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = 1 + F * x := ⟨_, rfl⟩
    have hp'eq : p' + 1 = (p + 1) * Q := by
      have h1 : p' = p + (p + 1) * F * x := by omega
      rw [h1, hQ]
      ring
    have hQfac : ∀ r, r.Prime → r ∣ Q → p ≤ r := by
      intro r hr hrQ
      by_contra hlt
      have hrF : r ∣ F * x := by
        rw [hF]
        exact (Nat.dvd_factorial hr.pos (by omega)).mul_right x
      have hr1 : r ∣ Q - F * x := Nat.dvd_sub hrQ hrF
      rw [show Q - F * x = 1 by omega] at hr1
      exact hr.one_lt.ne' (Nat.dvd_one.1 hr1)
    have hPle : ∀ q ∈ P, q ≤ p := fun q hq => by
      have := Nat.le_of_dvd (by omega) (hP q hq).2.1
      omega
    have hnot : p' ∉ P := fun h => by
      have := hPle p' h
      omega
    refine ⟨p', by omega, hp', insert p' P, by rw [Finset.card_insert_of_notMem hnot, hcard],
      fun q hqP => ?_⟩
    rcases Finset.mem_insert.1 hqP with rfl | hqP
    · refine ⟨hp', dvd_rfl, fun r hr hrdvd => ?_⟩
      rw [Nat.div_self (by omega)] at hrdvd
      exact absurd (Nat.dvd_one.1 hrdvd) hr.one_lt.ne'
    · obtain ⟨hq, ⟨e, he⟩, hqfac⟩ := hP q hqP
      have hq1 : 0 < q + 1 := by omega
      have hp'q : p' + 1 = (q + 1) * (e * Q) := by rw [hp'eq, he, mul_assoc]
      refine ⟨hq, ⟨e * Q, hp'q⟩, fun r hr hrdvd => ?_⟩
      rw [hp'q, Nat.mul_div_cancel_left _ hq1] at hrdvd
      rcases hr.dvd_mul.1 hrdvd with hre | hrQ
      · refine hqfac r hr ?_
        rwa [he, Nat.mul_div_cancel_left _ hq1]
      · have := hQfac r hr hrQ
        have := hPle q hqP
        omega

/-- **Unbounded drops in the number of remainders.** Let $s(n)$ be the number of distinct
remainders $n \bmod k$ with $1 \le k \le \lfloor n/2 \rfloor$. For every natural number $M$
there are infinitely many $n$ with $s(n+1) + M \le s(n)$; equivalently,
$\liminf_{n \to \infty} (s(n+1) - s(n)) = -\infty$.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Proposition 17 (`prop:diffs_unbounded`). -/
public theorem remainderCount_drops_unbounded (M : ℕ) :
    ∃ᶠ n in Filter.atTop, remainderCount (n + 1) + M ≤ remainderCount n := by
  rw [Filter.frequently_atTop]
  intro a
  obtain ⟨p, hap, -, P, hcard, hP⟩ := exists_prime_chain (M + 1) a
  refine ⟨p, hap.le, ?_⟩
  have := remainderCount_succ_add_card_le P hP
  omega


-- Odd lost-remainder primes are sparse: consecutive candidates grow at least by squaring.
private theorem sq_le_of_odd_remainder_candidates {N p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hp₂ : p ≠ 2) (hpq : p < q)
    (hpd : p + 1 ∣ N) (hqd : q + 1 ∣ N)
    (hpr : ∀ r, r.Prime → r ∣ N / (p + 1) → p ≤ r)
    (hqr : ∀ r, r.Prime → r ∣ N / (q + 1) → q ≤ r) : p ^ 2 ≤ q := by
  have hp2 := hp.two_le
  have hpq' : p + 1 < q := by
    have hpo := hp.odd_of_ne_two hp₂
    have hqo := hq.odd_of_ne_two (by omega)
    obtain ⟨a, ha⟩ := hpo
    obtain ⟨b, hb⟩ := hqo
    omega
  have hcop : Nat.Coprime (p + 1) (N / (q + 1)) := by
    by_contra hn
    obtain ⟨r, hr, hrp, hrN⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    have hrle := Nat.le_of_dvd (by omega : 0 < p + 1) hrp
    have := hqr r hr hrN
    omega
  have hqeq : (q + 1) * (N / (q + 1)) = N := Nat.mul_div_cancel' hqd
  have hd : p + 1 ∣ (q + 1) * (N / (q + 1)) := by rwa [hqeq]
  obtain ⟨t, ht⟩ := hcop.dvd_of_dvd_mul_right hd
  have ht₂ : 2 ≤ t := by
    by_contra hn
    have h : t = 0 ∨ t = 1 := by omega
    rcases h with rfl | rfl
    · simp at ht
    · simp only [Nat.mul_one] at ht
      omega
  have htdvd : t ∣ N / (p + 1) := by
    refine ⟨N / (q + 1), ?_⟩
    have h : N = (p + 1) * (t * (N / (q + 1))) := calc
      N = (q + 1) * (N / (q + 1)) := hqeq.symm
      _ = ((p + 1) * t) * (N / (q + 1)) :=
        congrArg (fun j => j * (N / (q + 1))) ht
      _ = _ := mul_assoc _ _ _
    calc
      N / (p + 1) = ((p + 1) * (t * (N / (q + 1)))) / (p + 1) :=
        congrArg (· / (p + 1)) h
      _ = _ := Nat.mul_div_cancel_left _ (by omega)
  have hpt : p ≤ t :=
    (hpr t.minFac (Nat.minFac_prime (by omega)) ((Nat.minFac_dvd t).trans htdvd)).trans
      (Nat.minFac_le (by omega))
  have hb := Nat.mul_le_mul_left (p + 1) hpt
  rw [← ht, Nat.add_mul, Nat.one_mul, ← pow_two] at hb
  omega

-- A finite increasing chain with each next element at least the previous square
-- grows by two exponentials in its length.
private theorem tower_le_of_squared_growth {P : Finset ℕ} {N : ℕ}
    (hN : 2 ≤ N) (hP : ∀ p ∈ P, 2 ≤ p ∧ p ≤ N)
    (hsq : ∀ p ∈ P, ∀ q ∈ P, p < q → p ^ 2 ≤ q) :
    2 ^ (2 ^ (P.card - 1)) ≤ N := by
  let e : Fin P.card ↪o ℕ := P.orderEmbOfFin rfl
  have he (i : Fin P.card) : e i ∈ P := P.orderEmbOfFin_mem rfl i
  have hg (i : ℕ) (hi : i < P.card) : 2 ^ (2 ^ i) ≤ e ⟨i, hi⟩ := by
    induction i with
    | zero => simpa using (hP _ (he ⟨0, hi⟩)).1
    | succ i ih =>
      have hi' : i < P.card := Nat.lt_of_succ_lt hi
      have hei : e ⟨i, hi'⟩ < e ⟨i + 1, hi⟩ := e.strictMono (by exact Nat.lt_succ_self i)
      have h := hsq _ (he ⟨i, hi'⟩) _ (he ⟨i + 1, hi⟩) hei
      rw [pow_succ (2 : ℕ) i, pow_mul]
      exact (Nat.pow_le_pow_left (ih hi') 2).trans h
  by_cases hc : P.card = 0
  · simpa [hc] using hN
  · have ht : P.card - 1 < P.card := by omega
    exact (hg _ ht).trans (hP _ (he ⟨_, ht⟩)).2

private theorem card_add_one_le_log_log_of_tower {n c : ℕ} (hn : 2 ≤ n)
    (hlog : 1 ≤ Real.log (Real.log (n : ℝ))) (h : 2 ^ (2 ^ (c - 1)) ≤ n + 1) :
    (c : ℝ) + 1 ≤
      ((1 + |Real.log 2 - Real.log (Real.log 2)| + 2 * Real.log 2) / Real.log 2) *
        Real.log (Real.log (n : ℝ)) := by
  let k := c - 1
  have hl₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hln : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hp : (2 : ℝ) ^ (2 ^ k : ℕ) ≤ (n : ℝ) + 1 := by exact_mod_cast h
  have h₁ := Real.log_le_log (show 0 < (2 : ℝ) ^ (2 ^ k : ℕ) by positivity) hp
  rw [Real.log_pow, Nat.cast_pow, Nat.cast_ofNat] at h₁
  have h₂ : Real.log ((n : ℝ) + 1) ≤ 2 * Real.log (n : ℝ) := by
    calc
      _ ≤ Real.log (2 * (n : ℝ)) := Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + Real.log (n : ℝ) := Real.log_mul (by norm_num) (by positivity)
      _ ≤ _ := by linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn₂]
  have h₃ := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ k * Real.log 2) (h₁.trans h₂)
  rw [Real.log_mul (by positivity) hl₂.ne', Real.log_pow,
    Real.log_mul (by norm_num) hln.ne'] at h₃
  have hc : (c : ℝ) ≤ (k : ℝ) + 1 := by
    exact_mod_cast (show c ≤ k + 1 by dsimp [k]; omega)
  rw [div_mul_eq_mul_div, le_div_iff₀ hl₂]
  have h₄ := mul_le_mul_of_nonneg_right hc hl₂.le
  have h₅ := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ |Real.log 2 - Real.log (Real.log 2)| + 2 * Real.log 2 by positivity)
  rw [mul_one, add_mul] at h₅
  rw [add_mul, add_mul, one_mul] at *
  linarith [le_abs_self (Real.log 2 - Real.log (Real.log 2))]

open Filter in
private theorem eventually_two_le_and_one_le_log_log :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧ 1 ≤ Real.log (Real.log (n : ℝ)) := by
  have h : Tendsto (fun n : ℕ => Real.log (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact (eventually_ge_atTop 2).and ((tendsto_atTop.1 h) 1)

private theorem sub_bound_of_nat_bound {a b c : ℕ} {y : ℝ}
    (h : a ≤ b + c + 1) (hc : (c : ℝ) + 1 ≤ y) : (a : ℝ) - y ≤ b := by
  have hab : (a : ℝ) ≤ (b : ℝ) + (c : ℝ) + 1 := by exact_mod_cast h
  linarith

/-- **Consecutive differences of the number of remainders.** Let $s(n)$ be the number of
distinct remainders $n \bmod k$ with $1 \le k \le \lfloor n/2 \rfloor$. Then
$s(n+1) \le s(n) + 1$ for every $n \ge 1$; there is a real constant $C$ with
$s(n) - C \log \log n \le s(n+1)$ for all sufficiently large $n$; and for every natural number
$M$ there are infinitely many $n$ with $s(n+1) + M \le s(n)$, that is,
$\liminf_{n \to \infty} (s(n+1) - s(n)) = -\infty$.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Theorem 2 (`thm:diffs`). -/
public theorem remainderCount_consecutive_differences :
    (∀ n, 1 ≤ n → remainderCount (n + 1) ≤ remainderCount n + 1) ∧
      (∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
        (remainderCount n : ℝ) - C * Real.log (Real.log n) ≤ remainderCount (n + 1)) ∧
      ∀ M : ℕ, ∃ᶠ n in Filter.atTop, remainderCount (n + 1) + M ≤ remainderCount n := by
  refine ⟨fun n _ => remainderCount_succ_le n, ?_, remainderCount_drops_unbounded⟩
  refine ⟨(1 + |Real.log 2 - Real.log (Real.log 2)| + 2 * Real.log 2) / Real.log 2, ?_⟩
  filter_upwards [eventually_two_le_and_one_le_log_log] with n hn
  have htower : 2 ^ (2 ^ ((oddDropPrimes n).card - 1)) ≤ n + 1 := by
    apply tower_le_of_squared_growth (by omega) ?_ ?_
    · intro p hp
      obtain ⟨hp₃, _, hd, _⟩ := mem_oddDropPrimes.mp hp
      have := Nat.le_of_dvd (by omega) hd
      omega
    · intro p hp q hq hpq
      obtain ⟨hp₃, hprime, hd, hrough⟩ := mem_oddDropPrimes.mp hp
      obtain ⟨_, hprime', hd', hrough'⟩ := mem_oddDropPrimes.mp hq
      exact sq_le_of_odd_remainder_candidates hprime hprime' (by omega) hpq hd hd' hrough hrough'
  have hcount := remainderCount_le_succ_add_card_oddDropPrimes (n := n) (by omega)
  exact sub_bound_of_nat_bound (by omega : remainderCount n ≤
    remainderCount (n + 1) + (oddDropPrimes n).card + 1)
    (card_add_one_le_log_log_of_tower hn.1 hn.2 htower)

end

end MetaMathlibExt
