/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.CarmichaelNumber
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Carmichael numbers with a prime number of prime factors in a range

Assuming Heath-Brown's conjecture on the least prime in an arithmetic progression, and a lower
bound for the number of primes `q` with `q - 1` smooth, this file proves
`MetaMathlibExt.exists_carmichael_prime_cardFactors_between_of_heathBrown`: for every large `y`
there is a Carmichael number `n` with `e^{(γ/4) y^θ log y} ≤ n ≤ e^{e^{19 θ y}}` whose number of
prime factors counted with multiplicity is prime.

Statements from Thomas Wright, *Carmichael Numbers with a Prime Number of Prime Factors*,
INTEGERS 24 (2024), Article A97 (arXiv:2206.07254). Heath-Brown's conjecture (Conjecture 3 of the
paper: the least prime `≡ c (mod d)`, `gcd(c, d) = 1`, is `≪ d log² d`) enters as a hypothesis.

The proof follows the construction of Alford, Granville and Pomerance as used in the paper, with
three changes that keep it self-contained.
* The pool of primes `p = d k₀ + 1` with `d ∣ L` comes from the Heath-Brown hypothesis and the
  pigeonhole principle instead of estimates for primes in arithmetic progressions.
* Zero-sum subsequences come from a character-sum bound: if `φ(M) (1 - 1/m) ^ k < 1`, where `m`
  is an exponent of `(ZMod M)ˣ`, then any `k` units modulo `M` have a nonempty subfamily with
  product `1`.
* Pairwise disjoint zero-sum blocks are extracted greedily and grouped by size; the Heath-Brown
  hypothesis then gives a prime number `ℓ = a j + 1` of prime factors, using `j` blocks of
  size `a` and the extra prime `P = L k₀ k₁ + 1`.
-/

namespace MetaMathlibExt

namespace exists_carmichael_prime_cardFactors_between_of_heathBrown

open ArithmeticFunction Filter

/-- For a sequence with no nonempty subsequence of product `1`, the character sum of
`∏ (1 - ξ i χ (g i))` is `φ n`: only the empty subsequence contributes. -/
private theorem sum_prod_one_sub_eq {n : ℕ} [NeZero n] {ι : Type*}
    (I : Finset ι) (g : ι → ZMod n) (ξ : ι → ℂ)
    (hfree : ∀ T ⊆ I, T.Nonempty → ∏ i ∈ T, g i ≠ 1) :
    ∑ χ : DirichletCharacter ℂ n, ∏ i ∈ I, (1 - ξ i * χ (g i)) = n.totient := by
  classical
  have hexp : ∀ χ : DirichletCharacter ℂ n, ∏ i ∈ I, (1 - ξ i * χ (g i)) =
      ∑ T ∈ I.powerset, (∏ i ∈ T, (-ξ i)) * χ (∏ i ∈ T, g i) := by
    intro χ
    have h := Finset.prod_add (fun i => -ξ i * χ (g i)) (fun _ => (1 : ℂ)) I
    simp only [Finset.prod_const_one, mul_one] at h
    rw [show (∏ i ∈ I, (1 - ξ i * χ (g i))) = ∏ i ∈ I, (-ξ i * χ (g i) + 1) from
      Finset.prod_congr rfl fun i _ => by ring, h]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [Finset.prod_mul_distrib, map_prod]
  simp_rw [hexp]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, DirichletCharacter.sum_characters_eq]
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro T hT hne
    have h := hfree T (Finset.mem_powerset.mp hT) (Finset.nonempty_iff_ne_empty.mpr hne)
    simp [h]
  · intro h
    exact absurd (Finset.empty_mem_powerset I) h

private theorem card_dirichletCharacter (n : ℕ) [NeZero n] :
    Fintype.card (DirichletCharacter ℂ n) = n.totient := by
  rw [← Nat.card_eq_fintype_card]
  exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ n

/-- Greedy choice of roots of unity: each factor `1 - ξ χ (g i)` kills at least a `1 / m`
proportion of the surviving characters. -/
private theorem exists_xi {n : ℕ} [NeZero n] {m : ℕ} (hm : 0 < m)
    (hexp : ∀ u : (ZMod n)ˣ, u ^ m = 1) {ι : Type*} (I : Finset ι)
    (g : ι → ZMod n) (hg : ∀ i ∈ I, IsUnit (g i)) :
    ∃ ξ : ι → ℂ, ((Finset.univ.filter fun χ : DirichletCharacter ℂ n =>
        ∏ i ∈ I, (1 - ξ i * χ (g i)) ≠ 0).card : ℝ) ≤ n.totient * (1 - 1 / m) ^ I.card := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨0, ?_⟩
    simp only [Finset.prod_empty, ne_eq, one_ne_zero, not_false_eq_true, Finset.filter_true,
      Finset.card_univ, card_dirichletCharacter, Finset.card_empty, pow_zero, mul_one, le_refl]
  | insert a I ha ih =>
    obtain ⟨ξ, hξ⟩ := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    set S := Finset.univ.filter fun χ : DirichletCharacter ℂ n =>
      ∏ i ∈ I, (1 - ξ i * χ (g i)) ≠ 0 with hS
    have hga : g a ^ m = 1 := by
      have h1 := hexp (hg a (Finset.mem_insert_self a I)).unit
      have h2 := congrArg Units.val h1
      simpa using h2
    set t := Polynomial.nthRootsFinset m (1 : ℂ) with ht
    have hval : ∀ χ ∈ S, χ (g a) ∈ t := by
      intro χ _
      rw [ht, Polynomial.mem_nthRootsFinset hm, ← map_pow, hga, map_one]
    have htcard : t.card ≤ m := by
      rw [ht, Polynomial.nthRootsFinset]
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots m 1)
    have htne : t.Nonempty := ⟨1, by rw [ht, Polynomial.mem_nthRootsFinset hm, one_pow]⟩
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    obtain ⟨w, hw, hcard⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hval htne
      (b := (S.card : ℝ) / m) (by
        rw [nsmul_eq_mul]
        calc (t.card : ℝ) * (S.card / m) ≤ m * (S.card / m) := by
              gcongr
          _ = S.card := by field_simp)
    have hw0 : w ≠ 0 := by
      rintro rfl
      rw [ht, Polynomial.mem_nthRootsFinset hm, zero_pow hm.ne'] at hw
      exact zero_ne_one hw
    refine ⟨Function.update ξ a w⁻¹, ?_⟩
    have hfilter : (Finset.univ.filter fun χ : DirichletCharacter ℂ n =>
        ∏ i ∈ insert a I, (1 - Function.update ξ a w⁻¹ i * χ (g i)) ≠ 0) =
        S.filter fun χ => χ (g a) ≠ w := by
      ext χ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hS]
      rw [Finset.prod_insert ha, Function.update_self]
      have hI : ∏ i ∈ I, (1 - Function.update ξ a w⁻¹ i * χ (g i)) =
          ∏ i ∈ I, (1 - ξ i * χ (g i)) := by
        refine Finset.prod_congr rfl fun i hi => ?_
        rw [Function.update_of_ne (by rintro rfl; exact ha hi)]
      rw [hI, mul_ne_zero_iff]
      have : (1 - w⁻¹ * χ (g a) ≠ 0) ↔ χ (g a) ≠ w := by
        constructor
        · intro h1 h2; apply h1; rw [h2, inv_mul_cancel₀ hw0, sub_self]
        · intro h1 h2; apply h1
          have h3 : w⁻¹ * χ (g a) = 1 := by linear_combination -h2
          calc χ (g a) = w * (w⁻¹ * χ (g a)) := by field_simp
            _ = w := by rw [h3, mul_one]
      rw [this, and_comm]
    rw [hfilter, Finset.card_insert_of_notMem ha, pow_succ, ← mul_assoc]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := S) (fun χ : DirichletCharacter ℂ n => χ (g a) = w)
    have hsplitR : ((S.filter fun χ => χ (g a) = w).card : ℝ) +
        ((S.filter fun χ => ¬ χ (g a) = w).card : ℝ) = S.card := by exact_mod_cast hsplit
    have h1m : (0 : ℝ) ≤ 1 - 1 / m := by
      rw [sub_nonneg, div_le_one hmR]; exact_mod_cast hm
    calc ((S.filter fun χ => χ (g a) ≠ w).card : ℝ)
        = S.card - (S.filter fun χ => χ (g a) = w).card := by linarith
      _ ≤ S.card - S.card / m := by linarith
      _ = S.card * (1 - 1 / m) := by ring
      _ ≤ n.totient * (1 - 1 / m) ^ I.card * (1 - 1 / m) := by gcongr

/-- A zero-sum bound for units modulo `n`: if `φ n (1 - 1 / m) ^ k < 1`, where `m` is an
exponent of `(ZMod n)ˣ`, then any `k` units have a nonempty subfamily with product `1`. -/
private theorem exists_prod_eq_one {n : ℕ} [NeZero n] {m : ℕ} (hm : 0 < m)
    (hexp : ∀ u : (ZMod n)ˣ, u ^ m = 1) {ι : Type*} (I : Finset ι)
    (g : ι → ZMod n) (hg : ∀ i ∈ I, IsUnit (g i))
    (hI : (n.totient : ℝ) * (1 - 1 / m) ^ I.card < 1) :
    ∃ T ⊆ I, T.Nonempty ∧ ∏ i ∈ T, g i = 1 := by
  by_contra! hfree
  obtain ⟨ξ, hξ⟩ := exists_xi hm hexp I g hg
  have hcard : (Finset.univ.filter fun χ : DirichletCharacter ℂ n =>
      ∏ i ∈ I, (1 - ξ i * χ (g i)) ≠ 0).card = 0 := by
    have h := hξ.trans_lt hI
    exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast h)
  have hall : ∀ χ : DirichletCharacter ℂ n, ∏ i ∈ I, (1 - ξ i * χ (g i)) = 0 := by
    intro χ
    by_contra h
    have hmem : χ ∈ Finset.univ.filter fun χ : DirichletCharacter ℂ n =>
        ∏ i ∈ I, (1 - ξ i * χ (g i)) ≠ 0 := by simp [h]
    rw [Finset.card_eq_zero] at hcard
    simp [hcard] at hmem
  have hsum := sum_prod_one_sub_eq I g ξ hfree
  simp only [hall, Finset.sum_const_zero] at hsum
  have hpos : 0 < n.totient := Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have : (n.totient : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  exact this hsum.symm

private theorem cardFactors_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    cardFactors (∏ p ∈ s, p) = s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have has : a.Prime := hs a (Finset.mem_insert_self a s)
    have hs' : ∀ p ∈ s, p.Prime := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert ha, cardFactors_mul has.ne_zero
      (Finset.prod_ne_zero_iff.mpr fun p hp => (hs' p hp).ne_zero),
      cardFactors_apply_prime has, ih hs', Finset.card_insert_of_notMem ha, add_comm]

private theorem squarefree_prod_primes (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  have h := Nat.squarefree_prod_primeFactors (∏ p ∈ s, p)
  rwa [Nat.primeFactors_prod hs] at h

/-- Korselt assembly: a prime `P` times distinct primes `p` with `p - 1 ∣ P - 1` and product
`1` modulo `P - 1` is a Carmichael number. -/
private theorem carmichael_of_blocks (P : ℕ) (hP : P.Prime) (U : Finset ℕ)
    (hU : ∀ p ∈ U, p.Prime ∧ p - 1 ∣ P - 1) (hPU : P ∉ U) (hUne : U.Nonempty)
    (hprod : ∏ p ∈ U, (p : ZMod (P - 1)) = 1) :
    (P * ∏ p ∈ U, p).IsCarmichael ∧ cardFactors (P * ∏ p ∈ U, p) = U.card + 1 := by
  have hprimes : ∀ p ∈ insert P U, p.Prime := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hP
    · exact (hU p hp).1
  have hn : P * ∏ p ∈ U, p = ∏ p ∈ insert P U, p := by rw [Finset.prod_insert hPU]
  refine ⟨?_, ?_⟩
  · rw [Nat.isCarmichael_iff_korselt]
    obtain ⟨q, hq⟩ := hUne
    have hqp := (hU q hq).1
    have hUprod : 2 ≤ ∏ p ∈ U, p := by
      have : q ∣ ∏ p ∈ U, p := Finset.dvd_prod_of_mem _ hq
      exact hqp.two_le.trans (Nat.le_of_dvd (Finset.prod_pos fun p hp => (hU p hp).1.pos) this)
    refine ⟨?_, ?_, ?_, ?_⟩
    · nlinarith [hP.two_le]
    · exact Nat.not_prime_mul hP.one_lt.ne' (by omega)
    · rw [hn]; exact squarefree_prod_primes _ hprimes
    · intro r hr hrn
      rw [hn] at hrn
      have hrmem : r ∈ insert P U := by
        obtain ⟨p, hp, hrp⟩ := (Prime.dvd_finsetProd_iff hr.prime _).mp hrn
        rwa [(Nat.prime_dvd_prime_iff_eq hr (hprimes p hp)).mp hrp]
      have h1 : r - 1 ∣ P - 1 := by
        rcases Finset.mem_insert.mp hrmem with rfl | hr'
        · exact dvd_rfl
        · exact (hU r hr').2
      refine h1.trans ?_
      have hPcast : (P : ZMod (P - 1)) = 1 := by
        have h0 : ((P - 1 : ℕ) : ZMod (P - 1)) = 0 := ZMod.natCast_self _
        rw [Nat.cast_sub hP.one_lt.le, Nat.cast_one, sub_eq_zero] at h0
        exact h0
      have hcast : ((P * ∏ p ∈ U, p : ℕ) : ZMod (P - 1)) = ((1 : ℕ) : ZMod (P - 1)) := by
        push_cast
        rw [hprod, hPcast, mul_one]
      rw [ZMod.natCast_eq_natCast_iff] at hcast
      exact (Nat.modEq_iff_dvd' (by nlinarith [hP.two_le])).mp hcast.symm
  · rw [hn, cardFactors_prod_primes _ hprimes, Finset.card_insert_of_notMem hPU]

/-- Greedy extraction of pairwise disjoint zero-sum blocks of size at most `D`. -/
private theorem exists_blocks {M : ℕ} (S : Finset ℕ) (D : ℕ)
    (hD : ∀ T ⊆ S, T.card = D → ∃ B ⊆ T, B.Nonempty ∧ ∏ p ∈ B, (p : ZMod M) = 1) :
    ∀ b : ℕ, b * D ≤ S.card → ∃ 𝔅 : Finset (Finset ℕ), 𝔅.card = b ∧
      (∀ B ∈ 𝔅, B ⊆ S ∧ B.Nonempty ∧ B.card ≤ D ∧ ∏ p ∈ B, (p : ZMod M) = 1) ∧
      (𝔅 : Set (Finset ℕ)).PairwiseDisjoint id := by
  intro b
  induction b with
  | zero => intro _; exact ⟨∅, by simp, by simp, by simp⟩
  | succ b ih =>
    intro hb
    have hb' : b * D + D ≤ S.card := by rw [add_mul, one_mul] at hb; exact hb
    obtain ⟨𝔅, hcard, hmem, hdisj⟩ := ih (by omega)
    set U := 𝔅.biUnion id with hU
    have hUcard : U.card ≤ b * D := by
      calc U.card ≤ ∑ B ∈ 𝔅, (id B).card := Finset.card_biUnion_le
        _ ≤ ∑ _B ∈ 𝔅, D := Finset.sum_le_sum fun B hB => (hmem B hB).2.2.1
        _ = b * D := by rw [Finset.sum_const, hcard, smul_eq_mul]
    have hUS : U ⊆ S := Finset.biUnion_subset.mpr fun B hB => (hmem B hB).1
    have hrem : D ≤ (S \ U).card := by
      rw [Finset.card_sdiff_of_subset hUS]
      omega
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hrem
    obtain ⟨B, hBT, hBne, hBprod⟩ := hD T (hTsub.trans Finset.sdiff_subset) hTcard
    have hBU : Disjoint B U :=
      Finset.disjoint_of_subset_left (hBT.trans hTsub) Finset.sdiff_disjoint
    have hBnot : B ∉ 𝔅 := by
      intro hB
      have : B ⊆ U := Finset.subset_biUnion_of_mem id hB
      obtain ⟨x, hx⟩ := hBne
      exact Finset.disjoint_left.mp hBU hx (this hx)
    refine ⟨insert B 𝔅, by rw [Finset.card_insert_of_notMem hBnot, hcard], ?_, ?_⟩
    · intro B' hB'
      rcases Finset.mem_insert.mp hB' with rfl | hB'
      · exact ⟨hBT.trans (hTsub.trans Finset.sdiff_subset), hBne,
          hTcard ▸ Finset.card_le_card hBT, hBprod⟩
      · exact hmem B' hB'
    · rw [Finset.coe_insert]
      refine hdisj.insert fun B' hB' _ => ?_
      exact Finset.disjoint_of_subset_right (Finset.subset_biUnion_of_mem id hB') hBU

/-- The Carmichael function of `L k`, for `L` a product of distinct primes `q` with
`q - 1 ∣ E`, is at most `E k ^ 2`. -/
private theorem carmichael_mul_le (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (E : ℕ) (hE0 : E ≠ 0)
    (hE : ∀ q ∈ Q, q - 1 ∣ E) (k : ℕ) (hk : 0 < k) :
    carmichael ((∏ q ∈ Q, q) * k) ≤ E * k ^ 2 := by
  set L := ∏ q ∈ Q, q with hLdef
  have hLsq : Squarefree L := squarefree_prod_primes Q hQ
  have hL0 : L ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q hq => (hQ q hq).ne_zero
  have hdvd : L * k ∣ Nat.lcm L (k ^ 2) := by
    have hg : Nat.gcd L (k ^ 2) ∣ k := by
      have h1 : Squarefree (Nat.gcd L (k ^ 2)) := hLsq.squarefree_of_dvd (Nat.gcd_dvd_left _ _)
      exact (h1.dvd_pow_iff_dvd two_ne_zero).mp (Nat.gcd_dvd_right _ _)
    have hgpos : 0 < Nat.gcd L (k ^ 2) := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hL0)
    have hgl := Nat.gcd_mul_lcm L (k ^ 2)
    have h2 : L * k * Nat.gcd L (k ^ 2) ∣ Nat.lcm L (k ^ 2) * Nat.gcd L (k ^ 2) := by
      rw [mul_comm (Nat.lcm _ _), hgl, show L * k ^ 2 = L * k * k by ring]
      exact mul_dvd_mul_left _ hg
    exact Nat.dvd_of_mul_dvd_mul_right hgpos h2
  have hcL : carmichael L ∣ E := by
    have hpair : Set.Pairwise (Q : Set ℕ) (Nat.Coprime.onFun fun q : ℕ => q) := by
      intro p hp q hq hpq
      exact (Nat.coprime_primes (hQ p hp) (hQ q hq)).mpr hpq
    rw [hLdef, carmichael_finsetProd hpair]
    refine Finset.lcm_dvd fun q hq => ?_
    simp only [Function.comp_apply, carmichael_of_prime (hQ q hq)]
    exact hE q hq
  have h1 : carmichael (L * k) ∣ E * (k ^ 2).totient := by
    refine (carmichael_dvd hdvd).trans ?_
    rw [carmichael_lcm]
    exact (Nat.lcm_dvd_mul _ _).trans (mul_dvd_mul hcL (carmichael_dvd_totient _))
  have hpos : 0 < E * (k ^ 2).totient :=
    Nat.mul_pos (Nat.pos_of_ne_zero hE0) (Nat.totient_pos.mpr (by positivity))
  calc carmichael (L * k) ≤ E * (k ^ 2).totient := Nat.le_of_dvd hpos h1
    _ ≤ E * k ^ 2 := Nat.mul_le_mul_left _ (Nat.totient_le _)

/-- A `Y`-smooth number below `(Y + 1) ^ 2` divides `lcm(1, ..., Y) ^ 3`. -/
private theorem dvd_lcmUpto_pow_three {n Y : ℕ} (hn : n ≠ 0)
    (hsmooth : ∀ r, r.Prime → r ∣ n → r ≤ Y) (hle : n < (Y + 1) ^ 2) :
    n ∣ Y.lcmUpto ^ 3 := by
  rw [← Nat.factorization_le_iff_dvd hn (pow_ne_zero _ (Nat.lcmUpto_ne_zero Y))]
  intro r
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  by_cases hr : r.Prime
  · rw [Nat.factorization_lcmUpto Y hr]
    by_cases hrn : r ∣ n
    · have hrY := hsmooth r hr hrn
      have ha : 0 < Nat.log r Y := Nat.log_pos hr.one_lt hrY
      have hrv : r ^ n.factorization r ≤ n := Nat.ordProj_le r hn
      have hYa : Y < r ^ (Nat.log r Y + 1) := Nat.lt_pow_succ_log_self hr.one_lt Y
      have hlt : r ^ n.factorization r < r ^ (2 * Nat.log r Y + 2) := by
        calc r ^ n.factorization r ≤ n := hrv
          _ < (Y + 1) ^ 2 := hle
          _ ≤ (r ^ (Nat.log r Y + 1)) ^ 2 := Nat.pow_le_pow_left hYa 2
          _ = r ^ (2 * Nat.log r Y + 2) := by rw [← pow_mul]; ring_nf
      have := (Nat.pow_lt_pow_iff_right hr.one_lt).mp hlt
      omega
    · rw [Nat.factorization_eq_zero_of_not_dvd hrn]; exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime n hr]; exact Nat.zero_le _

/-- The pool: by the Heath-Brown hypothesis and the pigeonhole principle, some `k₀ ≤ K` has
at least `R` primes of the form `d k₀ + 1` with `d ∣ L`. -/
private theorem exists_pool (C : ℝ) (hCpos : 0 < C)
    (hC : ∀ d : ℕ, 2 ≤ d → ∀ c : ℕ, Nat.Coprime c d →
      ∃ p : ℕ, p.Prime ∧ p ≡ c [MOD d] ∧ (p : ℝ) ≤ C * d * Real.log d ^ 2)
    (Q : Finset ℕ) (hQp : ∀ q ∈ Q, q.Prime) (hQne : Q.Nonempty)
    (L : ℕ) (hL : L = ∏ q ∈ Q, q) (K : ℕ) (hK0 : C * Real.log L ^ 2 ≤ K)
    (R : ℕ) (hR : K * R ≤ 2 ^ Q.card - 1) :
    ∃ k0 : ℕ, 1 ≤ k0 ∧ k0 ≤ K ∧ ∃ pool : Finset ℕ, R ≤ pool.card ∧
      ∀ p ∈ pool, p.Prime ∧ ∃ d, d ∣ L ∧ p = d * k0 + 1 := by
  classical
  have hdsub : ∀ A ⊆ Q, (∏ q ∈ A, q) ∣ L := fun A hA =>
    hL ▸ Finset.prod_dvd_prod_of_subset _ _ _ hA
  have hL0 : 0 < L := hL ▸ Finset.prod_pos fun q hq => (hQp q hq).pos
  have hdA2 : ∀ A ⊆ Q, A.Nonempty → 2 ≤ ∏ q ∈ A, q := by
    intro A hA ⟨q, hq⟩
    exact (hQp q (hA hq)).two_le.trans (Nat.le_of_dvd
      (Finset.prod_pos fun r hr => (hQp r (hA hr)).pos) (Finset.dvd_prod_of_mem _ hq))
  set 𝒜 := Q.powerset.filter Finset.Nonempty with h𝒜
  have hmem𝒜 : ∀ A ∈ 𝒜, A ⊆ Q ∧ A.Nonempty := fun A hA => by
    simpa [h𝒜] using hA
  have hex : ∀ A ∈ 𝒜, ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD ∏ q ∈ A, q] ∧
      (p : ℝ) ≤ C * (∏ q ∈ A, q : ℕ) * Real.log (∏ q ∈ A, q : ℕ) ^ 2 := fun A hA =>
    hC _ (hdA2 A (hmem𝒜 A hA).1 (hmem𝒜 A hA).2) 1 (Nat.coprime_one_left _)
  choose! pA hpA using hex
  set kA : Finset ℕ → ℕ := fun A => (pA A - 1) / ∏ q ∈ A, q with hkA
  have hkA_eq : ∀ A ∈ 𝒜, pA A = (∏ q ∈ A, q) * kA A + 1 := by
    intro A hA
    have hp := hpA A hA
    have hdvd : (∏ q ∈ A, q) ∣ pA A - 1 :=
      (Nat.modEq_iff_dvd' hp.1.one_lt.le).mp hp.2.1.symm
    rw [hkA, Nat.mul_div_cancel' hdvd, Nat.sub_add_cancel hp.1.one_lt.le]
  have hkA_pos : ∀ A ∈ 𝒜, 1 ≤ kA A := by
    intro A hA
    have h1 := hkA_eq A hA
    have h2 := (hpA A hA).1.two_le
    by_contra! h
    have h0 : kA A = 0 := Nat.lt_one_iff.mp h
    rw [h0, mul_zero, zero_add] at h1
    omega
  have hkA_le : ∀ A ∈ 𝒜, kA A ≤ K := by
    intro A hA
    have h2 := hdA2 A (hmem𝒜 A hA).1 (hmem𝒜 A hA).2
    have hd : (0 : ℝ) < (∏ q ∈ A, q : ℕ) := by exact_mod_cast (by omega : 0 < ∏ q ∈ A, q)
    have hle := (hpA A hA).2.2
    rw [hkA_eq A hA] at hle
    push_cast at hle
    have hlt : (kA A : ℝ) < C * Real.log (∏ q ∈ A, q : ℕ) ^ 2 := by
      by_contra! hcon
      have := mul_le_mul_of_nonneg_left hcon hd.le
      push_cast at this
      nlinarith
    have hmono : C * Real.log (∏ q ∈ A, q : ℕ) ^ 2 ≤ C * Real.log L ^ 2 := by
      gcongr
      exact_mod_cast Nat.le_of_dvd hL0 (hdsub A (hmem𝒜 A hA).1)
    have : (kA A : ℝ) < K := lt_of_lt_of_le hlt (hmono.trans hK0)
    exact_mod_cast this.le
  have h𝒜card : 𝒜.card = 2 ^ Q.card - 1 := by
    have : 𝒜 = Q.powerset.erase ∅ := by
      ext A
      simp [h𝒜, Finset.nonempty_iff_ne_empty, and_comm]
    rw [this, Finset.card_erase_of_mem (Finset.empty_mem_powerset Q), Finset.card_powerset]
  have hQmem : Q ∈ 𝒜 := by simp [h𝒜, hQne]
  have hK1le : 1 ≤ K := (hkA_pos Q hQmem).trans (hkA_le Q hQmem)
  obtain ⟨k0, hk0mem, hk0card⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := 𝒜) (t := Finset.Icc 1 K) (f := kA) (n := R)
    (fun A hA => Finset.mem_Icc.mpr ⟨hkA_pos A hA, hkA_le A hA⟩)
    ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hK1le⟩⟩
    (by rw [Nat.card_Icc, Nat.add_sub_cancel, h𝒜card]; exact hR)
  obtain ⟨hk01, hk0K⟩ := Finset.mem_Icc.mp hk0mem
  set 𝒜₀ := 𝒜.filter fun A => kA A = k0 with h𝒜₀
  have hmem𝒜₀ : ∀ A ∈ 𝒜₀, A ∈ 𝒜 ∧ kA A = k0 := fun A hA => Finset.mem_filter.mp hA
  have hinj : Set.InjOn pA 𝒜₀ := by
    intro A hA B hB hAB
    have hA' := hmem𝒜₀ A hA
    have hB' := hmem𝒜₀ B hB
    have h1 := hkA_eq A hA'.1
    have h2 := hkA_eq B hB'.1
    rw [hA'.2] at h1
    rw [hB'.2] at h2
    have h3 : (∏ q ∈ A, q) * k0 = (∏ q ∈ B, q) * k0 := by omega
    have h4 : (∏ q ∈ A, q) = ∏ q ∈ B, q := Nat.eq_of_mul_eq_mul_right (by omega) h3
    have hAp : ∀ p ∈ A, p.Prime := fun p hp => hQp p ((hmem𝒜 A hA'.1).1 hp)
    have hBp : ∀ p ∈ B, p.Prime := fun p hp => hQp p ((hmem𝒜 B hB'.1).1 hp)
    rw [← Nat.primeFactors_prod hAp, ← Nat.primeFactors_prod hBp, h4]
  refine ⟨k0, hk01, hk0K, 𝒜₀.image pA, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hinj]; exact hk0card
  · intro p hp
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hp
    have hA' := hmem𝒜₀ A hA
    refine ⟨(hpA A hA'.1).1, ∏ q ∈ A, q, hdsub A (hmem𝒜 A hA'.1).1, ?_⟩
    rw [hkA_eq A hA'.1, hA'.2]

/-- The extra prime `P = L k₀ k₁ + 1`, with `k₁ ≤ K`, from the Heath-Brown hypothesis. -/
private theorem exists_extra_prime (C : ℝ) (hCpos : 0 < C)
    (hC : ∀ d : ℕ, 2 ≤ d → ∀ c : ℕ, Nat.Coprime c d →
      ∃ p : ℕ, p.Prime ∧ p ≡ c [MOD d] ∧ (p : ℝ) ≤ C * d * Real.log d ^ 2)
    (L k0 K : ℕ) (hL : 2 ≤ L) (hk0 : 1 ≤ k0) (hk0K : k0 ≤ K)
    (hK1 : C * Real.log (L * K) ^ 2 ≤ K) :
    ∃ P k1 : ℕ, P.Prime ∧ P - 1 = L * (k0 * k1) ∧ 1 ≤ k1 ∧ k1 ≤ K := by
  have hLk0 : 2 ≤ L * k0 := by nlinarith
  obtain ⟨P, hPp, hPmod, hPle⟩ := hC (L * k0) hLk0 1 (Nat.coprime_one_left _)
  have hPdvd : L * k0 ∣ P - 1 := (Nat.modEq_iff_dvd' hPp.one_lt.le).mp hPmod.symm
  obtain ⟨k1, hk1⟩ := hPdvd
  refine ⟨P, k1, hPp, by rw [hk1, mul_assoc], ?_, ?_⟩
  · by_contra! h
    have h0 : k1 = 0 := Nat.lt_one_iff.mp h
    rw [h0, mul_zero] at hk1
    have := hPp.two_le
    omega
  · have hpos : (0 : ℝ) < (L * k0 : ℕ) := by exact_mod_cast (by omega : 0 < L * k0)
    have hPeq : (P : ℝ) = (L * k0 : ℕ) * k1 + 1 := by
      have : P = L * k0 * k1 + 1 := by rw [← hk1, Nat.sub_add_cancel hPp.one_lt.le]
      rw [this]; push_cast; ring
    have hlt : (k1 : ℝ) < C * Real.log (L * k0 : ℕ) ^ 2 := by
      by_contra! hcon
      have := mul_le_mul_of_nonneg_left hcon hpos.le
      rw [hPeq] at hPle
      nlinarith
    have hmono : C * Real.log (L * k0 : ℕ) ^ 2 ≤ C * Real.log (L * K) ^ 2 := by
      have hlog0 : 0 ≤ Real.log (L * k0 : ℕ) := Real.log_nonneg (by exact_mod_cast (by omega))
      gcongr
      push_cast
      exact_mod_cast Nat.mul_le_mul_left L hk0K
    exact_mod_cast (lt_of_lt_of_le hlt (hmono.trans hK1)).le

/-- The numerical condition of the zero-sum bound for the modulus `P - 1`. -/
private theorem totient_mul_lt_one (M m L K E D : ℕ) (hm : 0 < m) (hM : M ≤ L * K ^ 2)
    (hmle : m ≤ E * K ^ 4) (hL : 1 ≤ L) (hK : 1 ≤ K) (hE : E ≠ 0)
    (hD : Real.log (L * K ^ 2) * (E * K ^ 4) < D) :
    (M.totient : ℝ) * (1 - 1 / m) ^ D < 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hEK : (0 : ℝ) < (E * K ^ 4 : ℕ) := by
    exact_mod_cast Nat.mul_pos (Nat.pos_of_ne_zero hE) (by positivity)
  have hLK : (0 : ℝ) < L * K ^ 2 := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    have : (0 : ℝ) < K := by exact_mod_cast hK
    positivity
  have h1 : (M.totient : ℝ) ≤ L * K ^ 2 := by
    exact_mod_cast (Nat.totient_le M).trans hM
  have h0 : 0 ≤ 1 - 1 / (m : ℝ) := by
    rw [sub_nonneg, div_le_one hmR]; exact_mod_cast hm
  have h2 : (1 - 1 / (m : ℝ)) ^ D ≤ Real.exp (-(D / (E * K ^ 4 : ℕ))) := by
    calc (1 - 1 / (m : ℝ)) ^ D ≤ Real.exp (-(1 / m)) ^ D :=
          pow_le_pow_left₀ h0 (Real.one_sub_le_exp_neg _) D
      _ = Real.exp (-(D / m)) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ Real.exp (-(D / (E * K ^ 4 : ℕ))) := by
          gcongr
  have h3 : Real.log (L * K ^ 2) < D / (E * K ^ 4 : ℕ) := by
    rw [lt_div_iff₀ hEK]; push_cast; exact hD
  calc (M.totient : ℝ) * (1 - 1 / m) ^ D ≤ (L * K ^ 2) * Real.exp (-(D / (E * K ^ 4 : ℕ))) :=
        mul_le_mul h1 h2 (pow_nonneg h0 D) hLK.le
    _ = Real.exp (Real.log (L * K ^ 2) - D / (E * K ^ 4 : ℕ)) := by
        rw [Real.exp_sub, Real.exp_log hLK, Real.exp_neg]
        exact (div_eq_mul_inv _ _).symm
    _ < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

/-- Only few pool primes divide `L k₀ k₁` or equal `P`. -/
private theorem card_le_card_filter_coprime (Q pool : Finset ℕ) (hQp : ∀ q ∈ Q, q.Prime)
    (L k0 k1 K P : ℕ) (hL : L = ∏ q ∈ Q, q) (hk1 : 1 ≤ k1) (hk1K : k1 ≤ K)
    (hpool : ∀ p ∈ pool, p.Prime ∧ ∃ d, d ∣ L ∧ p = d * k0 + 1) :
    pool.card ≤
      (pool.filter fun p => Nat.Coprime p (L * (k0 * k1)) ∧ p ≠ P).card + (Q.card + K + 2) := by
  classical
  have hbad : (pool.filter fun p => ¬ (Nat.Coprime p (L * (k0 * k1)) ∧ p ≠ P)) ⊆
      (Q ∪ Finset.range (K + 1)) ∪ {P} := by
    intro p hp
    obtain ⟨hp, hpbad⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpprime, d, -, hpd⟩ := hpool p hp
    by_cases hPP : p = P
    · simp [hPP]
    · have hncop : ¬ Nat.Coprime p (L * (k0 * k1)) := fun h => hpbad ⟨h, hPP⟩
      rw [Nat.Prime.coprime_iff_not_dvd hpprime, not_not] at hncop
      rcases (Nat.Prime.dvd_mul hpprime).mp hncop with hpL | hpk
      · have : p ∈ Q := by
          rw [hL] at hpL
          obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hpprime.prime _).mp hpL
          rwa [(Nat.prime_dvd_prime_iff_eq hpprime (hQp q hq)).mp hpq]
        simp [this]
      · rcases (Nat.Prime.dvd_mul hpprime).mp hpk with hpk0 | hpk1
        · exfalso
          have h1 : p ∣ d * k0 := dvd_mul_of_dvd_right hpk0 _
          have h3 : p ∣ d * k0 + 1 := by rw [← hpd]
          have h2 : p ∣ 1 := (Nat.dvd_add_right h1).mp h3
          exact hpprime.one_lt.ne' (Nat.dvd_one.mp h2)
        · have : p ≤ K := (Nat.le_of_dvd hk1 hpk1).trans hk1K
          simp [Finset.mem_range, Nat.lt_succ_of_le this]
  have h1 := Finset.card_filter_add_card_filter_not (s := pool)
    (fun p => Nat.Coprime p (L * (k0 * k1)) ∧ p ≠ P)
  have h2 := Finset.card_le_card hbad
  have h3 : ((Q ∪ Finset.range (K + 1)) ∪ {P}).card ≤ Q.card + (K + 1) + 1 := by
    calc ((Q ∪ Finset.range (K + 1)) ∪ {P}).card ≤ (Q ∪ Finset.range (K + 1)).card + 1 := by
          simpa using Finset.card_union_le (Q ∪ Finset.range (K + 1)) {P}
      _ ≤ Q.card + (K + 1) + 1 := by
          have := Finset.card_union_le Q (Finset.range (K + 1))
          rw [Finset.card_range] at this
          omega
  omega

/-- The Heath-Brown hypothesis gives a prime `ℓ = a j + 1` with `T ≤ j ≤ J`. -/
private theorem exists_prime_count (C : ℝ) (hCpos : 0 < C)
    (hC : ∀ d : ℕ, 2 ≤ d → ∀ c : ℕ, Nat.Coprime c d →
      ∃ p : ℕ, p.Prime ∧ p ≡ c [MOD d] ∧ (p : ℝ) ≤ C * d * Real.log d ^ 2)
    (a T D J : ℕ) (ha : 1 ≤ a) (haD : a ≤ D) (hT : 2 ≤ T)
    (hJ : C * T * Real.log (D * T) ^ 2 ≤ J) :
    ∃ ℓ j : ℕ, ℓ.Prime ∧ ℓ = a * j + 1 ∧ T ≤ j ∧ j ≤ J ∧
      (ℓ : ℝ) ≤ C * D * T * Real.log (D * T) ^ 2 := by
  have haT : 2 ≤ a * T := by
    calc 2 = 1 * 2 := by ring
      _ ≤ a * T := Nat.mul_le_mul ha hT
  obtain ⟨ℓ, hℓp, hℓmod, hℓle⟩ := hC (a * T) haT 1 (Nat.coprime_one_left _)
  have hℓdvd : a * T ∣ ℓ - 1 := (Nat.modEq_iff_dvd' hℓp.one_lt.le).mp hℓmod.symm
  obtain ⟨j', hj'⟩ := hℓdvd
  have hj'pos : 1 ≤ j' := by
    by_contra! h
    have h0 : j' = 0 := Nat.lt_one_iff.mp h
    rw [h0, mul_zero] at hj'
    have := hℓp.two_le
    omega
  have hℓeq : ℓ = a * (T * j') + 1 := by
    rw [← mul_assoc, ← hj', Nat.sub_add_cancel hℓp.one_lt.le]
  have haTR : (0 : ℝ) < (a * T : ℕ) := by exact_mod_cast (by omega : 0 < a * T)
  have hlogaT : 0 ≤ Real.log (a * T : ℕ) := Real.log_nonneg (by exact_mod_cast (by omega))
  have hDT : ((a * T : ℕ) : ℝ) ≤ D * T := by
    push_cast
    exact_mod_cast Nat.mul_le_mul_right T haD
  refine ⟨ℓ, T * j', hℓp, hℓeq, Nat.le_mul_of_pos_right T hj'pos, ?_, ?_⟩
  · have hlt : ((T * j' : ℕ) : ℝ) < C * T * Real.log (a * T : ℕ) ^ 2 := by
      have h1 : (ℓ : ℝ) = (a * T : ℕ) * j' + 1 := by
        rw [hℓeq]; push_cast; ring
      have h3 : (j' : ℝ) < C * Real.log (a * T : ℕ) ^ 2 := by
        by_contra! hcon
        have := mul_le_mul_of_nonneg_left hcon haTR.le
        nlinarith
      have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
      calc ((T * j' : ℕ) : ℝ) = T * j' := by push_cast; ring
        _ < T * (C * Real.log (a * T : ℕ) ^ 2) := mul_lt_mul_of_pos_left h3 hT0
        _ = C * T * Real.log (a * T : ℕ) ^ 2 := by ring
    have hmono : C * T * Real.log (a * T : ℕ) ^ 2 ≤ C * T * Real.log (D * T) ^ 2 := by
      gcongr
    exact_mod_cast (lt_of_lt_of_le hlt (hmono.trans hJ)).le
  · calc (ℓ : ℝ) ≤ C * (a * T : ℕ) * Real.log (a * T : ℕ) ^ 2 := hℓle
      _ ≤ C * (D * T) * Real.log (D * T) ^ 2 := by gcongr
      _ = C * D * T * Real.log (D * T) ^ 2 := by ring

private theorem prod_insert_le_pow (P : ℕ) (U : Finset ℕ) (B : ℕ) (hPU : P ∉ U) (hP : P ≤ B)
    (hU : ∀ p ∈ U, p ≤ B) : P * ∏ p ∈ U, p ≤ B ^ (U.card + 1) := by
  have hall : ∀ p ∈ insert P U, p ≤ B := by
    intro p hp
    rcases Finset.mem_insert.mp hp with h | h
    · rw [h]; exact hP
    · exact hU p h
  have := Finset.prod_le_pow_card (insert P U) (fun p => p) B hall
  rwa [Finset.prod_insert hPU, Finset.card_insert_of_notMem hPU] at this

private theorem two_pow_le_prod_insert (P : ℕ) (U : Finset ℕ) (hPU : P ∉ U) (hP : 2 ≤ P)
    (hU : ∀ p ∈ U, 2 ≤ p) : 2 ^ (U.card + 1) ≤ P * ∏ p ∈ U, p := by
  have hall : ∀ p ∈ insert P U, 2 ≤ p := by
    intro p hp
    rcases Finset.mem_insert.mp hp with h | h
    · rw [h]; exact hP
    · exact hU p h
  have := Finset.pow_card_le_prod (insert P U) (fun p => p) 2 hall
  rwa [Finset.prod_insert hPU, Finset.card_insert_of_notMem hPU] at this

/-- The construction for fixed parameters. -/
private theorem main_construction (C : ℝ) (hCpos : 0 < C)
    (hC : ∀ d : ℕ, 2 ≤ d → ∀ c : ℕ, Nat.Coprime c d →
      ∃ p : ℕ, p.Prime ∧ p ≡ c [MOD d] ∧ (p : ℝ) ≤ C * d * Real.log d ^ 2)
    (Q : Finset ℕ) (hQp : ∀ q ∈ Q, q.Prime) (hQne : Q.Nonempty)
    (L : ℕ) (hL : L = ∏ q ∈ Q, q)
    (E : ℕ) (hE0 : E ≠ 0) (hE : ∀ q ∈ Q, q - 1 ∣ E)
    (K : ℕ) (hK0 : C * Real.log L ^ 2 ≤ K) (hK1 : C * Real.log (L * K) ^ 2 ≤ K)
    (D : ℕ) (hD : Real.log (L * K ^ 2) * (E * K ^ 4) < D)
    (T : ℕ) (hT : 2 ≤ T)
    (J : ℕ) (hJ : C * T * Real.log (D * T) ^ 2 ≤ J)
    (hpool : K * (D * D * J + Q.card + K + 2) ≤ 2 ^ Q.card - 1) :
    ∃ n ℓ : ℕ, n.IsCarmichael ∧ cardFactors n = ℓ ∧ ℓ.Prime ∧ T < ℓ ∧
      (ℓ : ℝ) ≤ C * D * T * Real.log (D * T) ^ 2 ∧
      n ≤ (L * K ^ 2 + 1) ^ ℓ ∧ 2 ^ ℓ ≤ n := by
  classical
  have hL0 : 0 < L := hL ▸ Finset.prod_pos fun q hq => (hQp q hq).pos
  have hL2 : 2 ≤ L := by
    obtain ⟨q, hq⟩ := hQne
    exact (hQp q hq).two_le.trans (Nat.le_of_dvd hL0 (hL ▸ Finset.dvd_prod_of_mem _ hq))
  -- The pool of primes `d k₀ + 1` with `d ∣ L`.
  obtain ⟨k0, hk01, hk0K, pool, hpoolcard, hpoolmem⟩ :=
    exists_pool C hCpos hC Q hQp hQne L hL K hK0 _ hpool
  have hK1le : 1 ≤ K := hk01.trans hk0K
  -- The extra prime `P = L k₀ k₁ + 1`.
  obtain ⟨P, k1, hPp, hPeq, hk1pos, hk1K⟩ :=
    exists_extra_prime C hCpos hC L k0 K hL2 hk01 hk0K hK1
  have hM0 : 0 < P - 1 := by rw [hPeq]; positivity
  have : NeZero (P - 1) := ⟨hM0.ne'⟩
  -- The exponent of `(ZMod (P - 1))ˣ`.
  have hmpos : 0 < carmichael (P - 1) :=
    Nat.pos_of_dvd_of_pos (carmichael_dvd_totient _) (Nat.totient_pos.mpr hM0)
  have hmle : carmichael (P - 1) ≤ E * K ^ 4 := by
    have h1 : carmichael (P - 1) ≤ E * (k0 * k1) ^ 2 := by
      rw [hPeq, hL]
      exact carmichael_mul_le Q hQp E hE0 hE _ (by positivity)
    calc carmichael (P - 1) ≤ E * (k0 * k1) ^ 2 := h1
      _ ≤ E * (K * K) ^ 2 := by gcongr
      _ = E * K ^ 4 := by ring
  have hMle : P - 1 ≤ L * K ^ 2 := by
    rw [hPeq, pow_two]
    exact Nat.mul_le_mul_left L (Nat.mul_le_mul hk0K hk1K)
  have hdav := totient_mul_lt_one (P - 1) _ L K E D hmpos hMle hmle hL0 hK1le hE0 hD
  -- Remove the pool primes that divide `P - 1` or equal `P`.
  set pool' := pool.filter fun p => Nat.Coprime p (P - 1) ∧ p ≠ P with hpool'
  have hpool'card : D * D * J ≤ pool'.card := by
    have h := card_le_card_filter_coprime Q pool hQp L k0 k1 K P hL hk1pos hk1K hpoolmem
    rw [← hPeq] at h
    change pool.card ≤ pool'.card + _ at h
    omega
  have hD1 : 1 ≤ D := by
    by_contra! h
    have h0 : D = 0 := Nat.lt_one_iff.mp h
    rw [h0] at hD
    have hlog : 0 ≤ Real.log (L * K ^ 2) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ L := by exact_mod_cast hL0
      have : (1 : ℝ) ≤ K := by exact_mod_cast hK1le
      nlinarith)
    have : (0 : ℝ) ≤ (E : ℝ) * K ^ 4 := by positivity
    push_cast at hD
    nlinarith
  -- Disjoint zero-sum blocks.
  have hDav : ∀ T' ⊆ pool', T'.card = D →
      ∃ B ⊆ T', B.Nonempty ∧ ∏ p ∈ B, (p : ZMod (P - 1)) = 1 := by
    intro T' hT' hcard
    refine exists_prod_eq_one hmpos (fun u => pow_carmichael u) T' (fun p => (p : ZMod (P - 1)))
      ?_ (hcard ▸ hdav)
    intro p hp
    exact (ZMod.isUnit_iff_coprime p (P - 1)).mpr (Finset.mem_filter.mp (hT' hp)).2.1
  obtain ⟨𝔅, h𝔅card, h𝔅mem, h𝔅disj⟩ :=
    exists_blocks pool' D hDav (D * J) (by
      calc D * J * D = D * D * J := by ring
        _ ≤ pool'.card := hpool'card)
  -- Pigeonhole on block sizes.
  obtain ⟨a, ha, hacard⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := 𝔅) (t := Finset.Icc 1 D) (f := Finset.card) (n := J)
    (fun B hB => Finset.mem_Icc.mpr ⟨Finset.card_pos.mpr (h𝔅mem B hB).2.1, (h𝔅mem B hB).2.2.1⟩)
    ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hD1⟩⟩
    (by rw [Nat.card_Icc, Nat.add_sub_cancel, h𝔅card])
  obtain ⟨ha1, haD⟩ := Finset.mem_Icc.mp ha
  -- A prime number `ℓ = a j + 1` of prime factors.
  obtain ⟨ℓ, j, hℓp, hℓeq, hTj, hjJ, hℓle⟩ :=
    exists_prime_count C hCpos hC a T D J ha1 haD hT hJ
  obtain ⟨𝔅', h𝔅'sub, h𝔅'card⟩ := Finset.exists_subset_card_eq (hjJ.trans hacard)
  have h𝔅'mem : ∀ B ∈ 𝔅', B ∈ 𝔅 ∧ B.card = a := fun B hB => Finset.mem_filter.mp (h𝔅'sub hB)
  have h𝔅'disj : (𝔅' : Set (Finset ℕ)).PairwiseDisjoint id :=
    h𝔅disj.subset fun B hB => (h𝔅'mem B hB).1
  set U := 𝔅'.biUnion id with hU
  have hUcard : U.card + 1 = ℓ := by
    have h1 : U.card = ∑ B ∈ 𝔅', (id B).card := Finset.card_biUnion h𝔅'disj
    have h2 : ∑ B ∈ 𝔅', (id B).card = ∑ _B ∈ 𝔅', a :=
      Finset.sum_congr rfl fun B hB => (h𝔅'mem B hB).2
    rw [h1, h2, Finset.sum_const, h𝔅'card, smul_eq_mul, hℓeq, mul_comm]
  have hUsub : U ⊆ pool' := Finset.biUnion_subset.mpr fun B hB => (h𝔅mem B (h𝔅'mem B hB).1).1
  have hUprod : ∏ p ∈ U, (p : ZMod (P - 1)) = 1 := by
    rw [hU, Finset.prod_biUnion h𝔅'disj]
    exact Finset.prod_eq_one fun B hB => (h𝔅mem B (h𝔅'mem B hB).1).2.2.2
  have hUne : U.Nonempty := by
    rw [← Finset.card_pos]
    have := hℓp.two_le
    omega
  have hUprop : ∀ p ∈ U, p.Prime ∧ p - 1 ∣ P - 1 := by
    intro p hp
    obtain ⟨hpprime, d, hdL, hpd⟩ := hpoolmem p (Finset.mem_filter.mp (hUsub hp)).1
    refine ⟨hpprime, ?_⟩
    rw [hpd, Nat.add_sub_cancel, hPeq, ← mul_assoc]
    exact Dvd.dvd.mul_right (Nat.mul_dvd_mul_right hdL k0) k1
  have hPU : P ∉ U := fun h => (Finset.mem_filter.mp (hUsub h)).2.2 rfl
  obtain ⟨hcarm, hcard⟩ := carmichael_of_blocks P hPp U hUprop hPU hUne hUprod
  refine ⟨P * ∏ p ∈ U, p, ℓ, hcarm, by rw [hcard, hUcard], hℓp, ?_, hℓle, ?_, ?_⟩
  · rw [hℓeq]; nlinarith
  · have hPle : P ≤ L * K ^ 2 + 1 := by
      have : P = (P - 1) + 1 := (Nat.sub_add_cancel hPp.one_lt.le).symm
      omega
    have hall : ∀ p ∈ U, p ≤ L * K ^ 2 + 1 := by
      intro p hp
      obtain ⟨-, d, hdL, hpd⟩ := hpoolmem p (Finset.mem_filter.mp (hUsub hp)).1
      have h1 : d ≤ L := Nat.le_of_dvd hL0 hdL
      have h2 : d * k0 ≤ L * K ^ 2 := by
        calc d * k0 ≤ L * K := Nat.mul_le_mul h1 hk0K
          _ ≤ L * K ^ 2 := Nat.mul_le_mul_left L (Nat.le_self_pow two_ne_zero K)
      omega
    rw [← hUcard]
    exact prod_insert_le_pow P U _ hPU hPle hall
  · rw [← hUcard]
    exact two_pow_le_prod_insert P U hPU hPp.two_le fun p hp => (hUprop p hp).1.two_le

/-- Polynomials are eventually below exponentials. -/
private theorem eventually_mul_pow_le_exp (A : ℝ) (k : ℕ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ y in atTop, A * y ^ k ≤ Real.exp (b * y) := by
  have h := (isLittleO_pow_exp_pos_mul_atTop k hb).bound (c := 1 / (|A| + 1)) (by positivity)
  filter_upwards [h, eventually_ge_atTop 0] with y hy hy0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hy0 k),
    abs_of_pos (Real.exp_pos _)] at hy
  have hk := pow_nonneg hy0 k
  calc A * y ^ k ≤ (|A| + 1) * y ^ k := by
        have := le_abs_self A
        nlinarith
    _ ≤ (|A| + 1) * (1 / (|A| + 1) * Real.exp (b * y)) := by gcongr
    _ = Real.exp (b * y) := by field_simp

/-- For `θ > 1`, `y` is eventually small compared with `y ^ θ / log y`. -/
private theorem eventually_mul_le_rpow_div_log (B : ℝ) {κ θ : ℝ} (hκ : 0 < κ) (hθ : 1 < θ) :
    ∀ᶠ y in atTop, B * y ≤ κ * y ^ θ / Real.log y := by
  have h := (isLittleO_log_rpow_atTop (sub_pos.mpr hθ)).bound (c := κ / (|B| + 1))
    (by positivity)
  filter_upwards [h, eventually_gt_atTop 1] with y hy hy1
  have hlog : 0 < Real.log y := Real.log_pos hy1
  have hy0 : 0 < y := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlog,
    abs_of_pos (Real.rpow_pos_of_pos hy0 _)] at hy
  rw [le_div_iff₀ hlog]
  have hyθ : y ^ θ = y * y ^ (θ - 1) := by
    rw [← Real.rpow_one_add' hy0.le (by linarith), add_sub_cancel]
  have hB : B * y * Real.log y ≤ (|B| + 1) * y * Real.log y := by
    have := le_abs_self B
    have : 0 ≤ y * Real.log y := by positivity
    nlinarith
  calc B * y * Real.log y ≤ (|B| + 1) * y * Real.log y := hB
    _ ≤ (|B| + 1) * y * (κ / (|B| + 1) * y ^ (θ - 1)) := by gcongr
    _ = κ * y ^ θ := by rw [hyθ]; field_simp

/-- Chebyshev's bound for `lcm(1, ..., ⌊y⌋) ^ 3`. -/
private theorem lcmUpto_pow_three_le {y : ℝ} (hy : 0 ≤ y) :
    ((⌊y⌋₊.lcmUpto ^ 3 : ℕ) : ℝ) ≤ Real.exp (3 * (Real.log 4 + 4) * y) := by
  have h1 := Chebyshev.psi_eq_log_lcmUpto ⌊y⌋₊
  have h2 := Chebyshev.psi_le_const_mul_self (x := (⌊y⌋₊ : ℝ)) (Nat.cast_nonneg _)
  have h3 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy
  have hpos : (0 : ℝ) < ⌊y⌋₊.lcmUpto := by exact_mod_cast Nat.lcmUpto_pos _
  have h4 : (0 : ℝ) ≤ Real.log 4 + 4 := by positivity
  push_cast
  calc ((⌊y⌋₊.lcmUpto : ℕ) : ℝ) ^ 3 = Real.exp (Real.log ⌊y⌋₊.lcmUpto) ^ 3 := by
        rw [Real.exp_log hpos]
    _ = Real.exp (3 * Real.log ⌊y⌋₊.lcmUpto) := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ Real.exp (3 * (Real.log 4 + 4) * y) := by
        apply Real.exp_le_exp.mpr
        rw [← h1]
        nlinarith

private theorem three_mul_log_four_add_four_lt : 3 * (Real.log 4 + 4) < 19 := by
  have h := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [h4]
  norm_num at h ⊢
  linarith

/-- The bound for the multipliers `k₀` and `k₁`. -/
private noncomputable def bdK (C y : ℝ) : ℕ := ⌈5 * C * y ^ 6⌉₊
/-- An exponent for the units modulo the primes `q`. -/
private noncomputable def bdE (y : ℝ) : ℕ := ⌊y⌋₊.lcmUpto ^ 3
/-- The length of sequences with a nonempty zero-sum subsequence. -/
private noncomputable def bdD (C y : ℝ) : ℕ := ⌊3 * y ^ 3 * bdE y * bdK C y ^ 4⌋₊ + 1
/-- The lower bound for the number of prime factors. -/
private noncomputable def bdT (θ γ y : ℝ) : ℕ := ⌈γ * y ^ θ * Real.log y / (4 * Real.log 2)⌉₊ + 2
/-- The number of blocks of a common size needed. -/
private noncomputable def bdJ (C θ γ y : ℝ) : ℕ :=
  ⌈C * bdT θ γ y * Real.log (bdD C y * bdT θ γ y) ^ 2⌉₊

private theorem bdK_le {C y : ℝ} (hC : 1 ≤ C) (hy : 1 ≤ y) : (bdK C y : ℝ) ≤ 6 * C * y ^ 6 := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ 5 * C * y ^ 6 by positivity)
  have : 1 ≤ C * y ^ 6 := one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hy)
  unfold bdK; linarith

private theorem one_le_bdK {C y : ℝ} (hC : 1 ≤ C) (hy : 1 ≤ y) : 1 ≤ bdK C y := by
  unfold bdK
  exact Nat.ceil_pos.mpr (by positivity)

private theorem bdD_le {C y : ℝ} (hC : 1 ≤ C) (hy : 1 ≤ y) :
    (bdD C y : ℝ) ≤ 3889 * C ^ 4 * y ^ 27 * Real.exp (3 * (Real.log 4 + 4) * y) := by
  have hK := bdK_le hC hy
  have hE : (bdE y : ℝ) ≤ Real.exp (3 * (Real.log 4 + 4) * y) :=
    lcmUpto_pow_three_le (by linarith)
  have hfl := Nat.floor_le (show 0 ≤ 3 * y ^ 3 * (bdE y : ℝ) * (bdK C y : ℝ) ^ 4 by positivity)
  have hexp1 : 1 ≤ Real.exp (3 * (Real.log 4 + 4) * y) := Real.one_le_exp (by positivity)
  have h1 : 1 ≤ C ^ 4 * y ^ 27 * Real.exp (3 * (Real.log 4 + 4) * y) :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC) (one_le_pow₀ hy)) hexp1
  have hK0 : (0 : ℝ) ≤ bdK C y := Nat.cast_nonneg _
  have h2 : 3 * y ^ 3 * (bdE y : ℝ) * (bdK C y : ℝ) ^ 4 ≤
      3 * y ^ 3 * Real.exp (3 * (Real.log 4 + 4) * y) * (6 * C * y ^ 6) ^ 4 := by
    gcongr
  unfold bdD
  push_cast
  calc (⌊3 * y ^ 3 * (bdE y : ℝ) * (bdK C y : ℝ) ^ 4⌋₊ : ℝ) + 1
      ≤ 3 * y ^ 3 * Real.exp (3 * (Real.log 4 + 4) * y) * (6 * C * y ^ 6) ^ 4 + 1 := by
        linarith
    _ = 3888 * (C ^ 4 * y ^ 27 * Real.exp (3 * (Real.log 4 + 4) * y)) + 1 := by ring
    _ ≤ 3889 * C ^ 4 * y ^ 27 * Real.exp (3 * (Real.log 4 + 4) * y) := by linarith

private theorem bdT_le {θ γ y : ℝ} (hθ : θ ≤ 2) (hγ : 0 < γ) (hy : 1 ≤ y) :
    (bdT θ γ y : ℝ) ≤ (γ + 3) * y ^ 3 := by
  have hlog2 : 1 ≤ 4 * Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  have hlogy' : Real.log y ≤ y := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hyθ : y ^ θ ≤ y ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hy hθ
    simpa using this
  have hx0 : 0 ≤ γ * y ^ θ * Real.log y / (4 * Real.log 2) := by positivity
  have hx : γ * y ^ θ * Real.log y / (4 * Real.log 2) ≤ γ * y ^ 3 := by
    rw [div_le_iff₀ (by linarith)]
    have : γ * y ^ θ * Real.log y ≤ γ * y ^ 2 * y := by gcongr
    have h3 : γ * y ^ 2 * y = γ * y ^ 3 := by ring
    have h4 : γ * y ^ 3 ≤ γ * y ^ 3 * (4 * Real.log 2) :=
      le_mul_of_one_le_right (by positivity) hlog2
    linarith
  have h := Nat.ceil_lt_add_one hx0
  have hy3 : 1 ≤ y ^ 3 := one_le_pow₀ hy
  unfold bdT
  push_cast
  nlinarith

private theorem two_le_bdT (θ γ y : ℝ) : 2 ≤ bdT θ γ y := by unfold bdT; omega

private theorem one_le_bdD (C y : ℝ) : 1 ≤ bdD C y := by unfold bdD; omega

private theorem eventually_log_bdK_le {C : ℝ} (hC : 1 ≤ C) :
    ∀ᶠ y in atTop, Real.log (bdK C y) ≤ y ^ 3 := by
  filter_upwards [eventually_mul_pow_le_exp (6 * C) 6 one_pos, eventually_ge_atTop 1]
    with y hy hy1
  have hK := bdK_le hC hy1
  have hK1 : (1 : ℝ) ≤ bdK C y := by exact_mod_cast one_le_bdK hC hy1
  calc Real.log (bdK C y) ≤ Real.log (Real.exp (1 * y)) :=
        Real.log_le_log (by linarith) (hK.trans hy)
    _ = y := by rw [Real.log_exp, one_mul]
    _ ≤ y ^ 3 := by
        calc y = y ^ 1 := (pow_one y).symm
          _ ≤ y ^ 3 := pow_le_pow_right₀ hy1 (by norm_num)

private theorem eventually_log_bdD_mul_bdT_le {C θ γ : ℝ} (hC : 1 ≤ C) (hθ : θ ≤ 2) (hγ : 0 < γ) :
    ∀ᶠ y in atTop, Real.log (bdD C y * bdT θ γ y) ≤ (3 * (Real.log 4 + 4) + 1) * y := by
  filter_upwards [eventually_mul_pow_le_exp (3889 * C ^ 4 * (γ + 3)) 30 one_pos,
    eventually_ge_atTop 1] with y hy hy1
  have hD := bdD_le hC hy1
  have hT := bdT_le hθ hγ hy1
  have hD1 : (1 : ℝ) ≤ bdD C y := by exact_mod_cast one_le_bdD C y
  have hT1 : (2 : ℝ) ≤ bdT θ γ y := by exact_mod_cast two_le_bdT θ γ y
  have hprod : (bdD C y : ℝ) * bdT θ γ y ≤
      Real.exp ((3 * (Real.log 4 + 4) + 1) * y) := by
    calc (bdD C y : ℝ) * bdT θ γ y
        ≤ (3889 * C ^ 4 * y ^ 27 * Real.exp (3 * (Real.log 4 + 4) * y)) * ((γ + 3) * y ^ 3) := by
          gcongr
      _ = (3889 * C ^ 4 * (γ + 3) * y ^ 30) * Real.exp (3 * (Real.log 4 + 4) * y) := by ring
      _ ≤ Real.exp (1 * y) * Real.exp (3 * (Real.log 4 + 4) * y) := by gcongr
      _ = Real.exp ((3 * (Real.log 4 + 4) + 1) * y) := by rw [← Real.exp_add]; ring_nf
  calc Real.log (bdD C y * bdT θ γ y) ≤ Real.log (Real.exp ((3 * (Real.log 4 + 4) + 1) * y)) :=
        Real.log_le_log (by positivity) hprod
    _ = _ := Real.log_exp _

private theorem bdJ_le {C θ γ y : ℝ} (hC : 1 ≤ C) (hθ : θ ≤ 2) (hγ : 0 < γ) (hy : 1 ≤ y)
    (hlog : Real.log (bdD C y * bdT θ γ y) ≤ (3 * (Real.log 4 + 4) + 1) * y) :
    (bdJ C θ γ y : ℝ) ≤ (C * (γ + 3) * (3 * (Real.log 4 + 4) + 1) ^ 2 + 1) * y ^ 5 := by
  have hT := bdT_le hθ hγ hy
  have hD1 : (1 : ℝ) ≤ bdD C y := by exact_mod_cast one_le_bdD C y
  have hT1 : (2 : ℝ) ≤ bdT θ γ y := by exact_mod_cast two_le_bdT θ γ y
  have hlog0 : 0 ≤ Real.log (bdD C y * bdT θ γ y) := Real.log_nonneg (by nlinarith)
  have hx0 : 0 ≤ C * bdT θ γ y * Real.log (bdD C y * bdT θ γ y) ^ 2 := by positivity
  have h := Nat.ceil_lt_add_one hx0
  have h2 : C * bdT θ γ y * Real.log (bdD C y * bdT θ γ y) ^ 2 ≤
      C * ((γ + 3) * y ^ 3) * ((3 * (Real.log 4 + 4) + 1) * y) ^ 2 := by gcongr
  have hy5 : 1 ≤ y ^ 5 := one_le_pow₀ hy
  have h3 : C * ((γ + 3) * y ^ 3) * ((3 * (Real.log 4 + 4) + 1) * y) ^ 2 =
      C * (γ + 3) * (3 * (Real.log 4 + 4) + 1) ^ 2 * y ^ 5 := by ring
  unfold bdJ
  linarith

private theorem eventually_upper {C θ γ : ℝ} (hC : 1 ≤ C) (hθ : θ ∈ Set.Ioo 1 2) (hγ : 0 < γ) :
    ∀ᶠ y in atTop, C * bdD C y * bdT θ γ y * Real.log (bdD C y * bdT θ γ y) ^ 2 *
      (3 * y ^ 3 + 1) ≤ Real.exp (19 * θ * y) := by
  set c := 3 * (Real.log 4 + 4) with hc
  have hc0 : 0 ≤ c := by positivity
  have hc19 : c < 19 * θ := by
    have := three_mul_log_four_add_four_lt; have := hθ.1; nlinarith
  filter_upwards [eventually_log_bdD_mul_bdT_le hC hθ.2.le hγ,
    eventually_mul_pow_le_exp (4 * 3889 * C ^ 5 * (γ + 3) * (c + 1) ^ 2) 35 (sub_pos.mpr hc19),
    eventually_ge_atTop 1] with y hlog hA hy1
  have hD := bdD_le hC hy1
  have hT := bdT_le hθ.2.le hγ hy1
  have hD1 : (1 : ℝ) ≤ bdD C y := by exact_mod_cast one_le_bdD C y
  have hT1 : (2 : ℝ) ≤ bdT θ γ y := by exact_mod_cast two_le_bdT θ γ y
  have hlog0 : 0 ≤ Real.log (bdD C y * bdT θ γ y) := Real.log_nonneg (by nlinarith)
  have hy3 : 3 * y ^ 3 + 1 ≤ 4 * y ^ 3 := by
    have := one_le_pow₀ hy1 (n := 3); linarith
  calc C * bdD C y * bdT θ γ y * Real.log (bdD C y * bdT θ γ y) ^ 2 * (3 * y ^ 3 + 1)
      ≤ C * (3889 * C ^ 4 * y ^ 27 * Real.exp (c * y)) * ((γ + 3) * y ^ 3) *
          ((c + 1) * y) ^ 2 * (4 * y ^ 3) := by gcongr
    _ = (4 * 3889 * C ^ 5 * (γ + 3) * (c + 1) ^ 2 * y ^ 35) * Real.exp (c * y) := by ring
    _ ≤ Real.exp ((19 * θ - c) * y) * Real.exp (c * y) := by gcongr
    _ = Real.exp (19 * θ * y) := by rw [← Real.exp_add]; ring_nf

private theorem eventually_pool {C θ γ : ℝ} (hC : 1 ≤ C) (hθ : θ ∈ Set.Ioo 1 2) (hγ : 0 < γ) :
    ∀ᶠ y in atTop, (bdK C y : ℝ) * ((bdD C y : ℝ) * bdD C y * bdJ C θ γ y + y ^ θ +
      bdK C y + 2) + 1 ≤ (2 : ℝ) ^ (γ * y ^ θ / Real.log (y ^ θ)) := by
  set c := 3 * (Real.log 4 + 4) with hc
  have hc0 : 0 ≤ c := by positivity
  set A₁ := C * (γ + 3) * (c + 1) ^ 2 + 1 with hA₁
  have hA₁0 : 0 ≤ A₁ := by positivity
  set A₃ := 6 * C * (3889 ^ 2 * C ^ 8 * A₁ + 6 * C + 3) + 1 with hA₃
  have hκ : 0 < Real.log 2 * γ / θ := by
    have := Real.log_pos one_lt_two; have := hθ.1
    exact div_pos (mul_pos (by assumption) hγ) (by linarith)
  filter_upwards [eventually_log_bdD_mul_bdT_le hC hθ.2.le hγ,
    eventually_mul_pow_le_exp A₃ 65 one_pos,
    eventually_mul_le_rpow_div_log (2 * c + 1) hκ hθ.1,
    eventually_gt_atTop 1] with y hlog hA hB hy1'
  have hy1 : 1 ≤ y := hy1'.le
  have hy0 : 0 < y := by linarith
  have hK := bdK_le hC hy1
  have hD := bdD_le hC hy1
  have hJ := bdJ_le hC hθ.2.le hγ hy1 hlog
  have hyθ : y ^ θ ≤ y ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hy1 hθ.2.le
    simpa using this
  have he1 : 1 ≤ Real.exp (c * y) := Real.one_le_exp (by positivity)
  set e := Real.exp (c * y) with he
  have he2 : Real.exp (2 * c * y) = e * e := by rw [he, ← Real.exp_add]; ring_nf
  have hy6 : 1 ≤ y ^ 6 := one_le_pow₀ hy1
  have hy2 : y ^ 2 ≤ y ^ 6 := pow_le_pow_right₀ hy1 (by norm_num)
  have hy12 : y ^ 12 ≤ y ^ 65 := pow_le_pow_right₀ hy1 (by norm_num)
  have hy65 : 1 ≤ y ^ 65 := one_le_pow₀ hy1
  have hee : 1 ≤ e * e := one_le_mul_of_one_le_of_one_le he1 he1
  have hθ0 : 0 ≤ y ^ θ := Real.rpow_nonneg hy0.le _
  have hLHS : (bdK C y : ℝ) * ((bdD C y : ℝ) * bdD C y * bdJ C θ γ y + y ^ θ +
      bdK C y + 2) + 1 ≤ A₃ * y ^ 65 * Real.exp (2 * c * y) := by
    calc (bdK C y : ℝ) * ((bdD C y : ℝ) * bdD C y * bdJ C θ γ y + y ^ θ + bdK C y + 2) + 1
        ≤ (6 * C * y ^ 6) * ((3889 * C ^ 4 * y ^ 27 * e) * (3889 * C ^ 4 * y ^ 27 * e) *
            (A₁ * y ^ 5) + y ^ 2 + 6 * C * y ^ 6 + 2) + 1 := by gcongr
      _ = 6 * C * 3889 ^ 2 * C ^ 8 * A₁ * (y ^ 65 * (e * e)) +
            6 * C * y ^ 6 * (y ^ 2 + 6 * C * y ^ 6 + 2) + 1 := by ring
      _ ≤ 6 * C * 3889 ^ 2 * C ^ 8 * A₁ * (y ^ 65 * (e * e)) +
            6 * C * (6 * C + 3) * (y ^ 65 * (e * e)) + y ^ 65 * (e * e) := by
          have h1 : 6 * C * y ^ 6 * (y ^ 2 + 6 * C * y ^ 6 + 2) ≤
              6 * C * (6 * C + 3) * y ^ 12 := by
            have : y ^ 2 + 6 * C * y ^ 6 + 2 ≤ (6 * C + 3) * y ^ 6 := by nlinarith
            calc 6 * C * y ^ 6 * (y ^ 2 + 6 * C * y ^ 6 + 2)
                ≤ 6 * C * y ^ 6 * ((6 * C + 3) * y ^ 6) := by gcongr
              _ = 6 * C * (6 * C + 3) * y ^ 12 := by ring
          have h2 : y ^ 12 ≤ y ^ 65 * (e * e) := by nlinarith
          have h3 : (1 : ℝ) ≤ y ^ 65 * (e * e) := by nlinarith
          have h4 : 0 ≤ 6 * C * (6 * C + 3) := by positivity
          nlinarith
      _ = A₃ * y ^ 65 * Real.exp (2 * c * y) := by rw [he2, hA₃]; ring
  have hRHS : Real.exp ((2 * c + 1) * y) ≤ (2 : ℝ) ^ (γ * y ^ θ / Real.log (y ^ θ)) := by
    rw [Real.rpow_def_of_pos two_pos, Real.log_rpow hy0]
    apply Real.exp_le_exp.mpr
    have hlogy : 0 < Real.log y := Real.log_pos hy1'
    have hθ0 : 0 < θ := by linarith [hθ.1]
    have : Real.log 2 * (γ * y ^ θ / (θ * Real.log y)) =
        Real.log 2 * γ / θ * y ^ θ / Real.log y := by
      field_simp
    rw [this]
    linarith
  calc (bdK C y : ℝ) * ((bdD C y : ℝ) * bdD C y * bdJ C θ γ y + y ^ θ + bdK C y + 2) + 1
      ≤ A₃ * y ^ 65 * Real.exp (2 * c * y) := hLHS
    _ ≤ Real.exp (1 * y) * Real.exp (2 * c * y) := by gcongr
    _ = Real.exp ((2 * c + 1) * y) := by rw [← Real.exp_add]; ring_nf
    _ ≤ _ := hRHS

private theorem log_le_half {y : ℝ} (hy : 0 < y) : Real.log y ≤ y / 2 := by
  have h1 := Real.add_one_le_exp (Real.log y - 1)
  rw [sub_add_cancel, Real.exp_sub, Real.exp_log hy] at h1
  have he : 2 < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  rw [le_div_iff₀ hpos] at h1
  rcases le_or_gt (Real.log y) 0 with h | h
  · linarith
  · nlinarith

private theorem log_mul_sq_add_one_le {L K : ℕ} {b : ℝ} (hL : 1 ≤ L) (hK : 1 ≤ K)
    (h : Real.log (L * K ^ 2) ≤ b) : Real.log ((L * K ^ 2 + 1 : ℕ) : ℝ) ≤ b + 1 := by
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hLK : (1 : ℝ) ≤ L * K ^ 2 := one_le_mul_of_one_le_of_one_le hLR (one_le_pow₀ hKR)
  have hBpos : (0 : ℝ) < ((L * K ^ 2 + 1 : ℕ) : ℝ) := by positivity
  have h3 : ((L * K ^ 2 + 1 : ℕ) : ℝ) ≤ 2 * (L * K ^ 2) := by push_cast; linarith
  have h4 : Real.log ((L * K ^ 2 + 1 : ℕ) : ℝ) ≤ Real.log (2 * (L * K ^ 2)) :=
    Real.log_le_log hBpos h3
  rw [Real.log_mul (by norm_num) (by positivity)] at h4
  have h5 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  linarith

private theorem exp_le_of_two_pow_le {n ℓ T : ℕ} {a : ℝ} (hT : a / Real.log 2 ≤ T) (hTℓ : T < ℓ)
    (hn : 2 ^ ℓ ≤ n) : Real.exp a ≤ n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h1 : a ≤ T * Real.log 2 := by rwa [div_le_iff₀ hlog2] at hT
  have h2 : Real.exp (T * Real.log 2) = (2 : ℝ) ^ T := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos two_pos, mul_comm]
  have h3 : (2 : ℝ) ^ T ≤ (2 : ℝ) ^ ℓ := pow_le_pow_right₀ (by norm_num) hTℓ.le
  have h4 : ((2 ^ ℓ : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
  push_cast at h4
  calc Real.exp a ≤ Real.exp (T * Real.log 2) := Real.exp_le_exp.mpr h1
    _ = (2 : ℝ) ^ T := h2
    _ ≤ (2 : ℝ) ^ ℓ := h3
    _ ≤ n := h4

private theorem le_exp_of_le_pow {n ℓ B : ℕ} {F b u : ℝ} (hB : 1 ≤ B) (hn : n ≤ B ^ ℓ)
    (hlogB : Real.log B ≤ b) (hℓ : (ℓ : ℝ) ≤ F) (hFb : F * b ≤ u) : (n : ℝ) ≤ Real.exp u := by
  have hBR : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hBpos : (0 : ℝ) < B := by linarith
  have h1 : (n : ℝ) ≤ (B : ℝ) ^ ℓ := by exact_mod_cast hn
  have h2 : (B : ℝ) ^ ℓ = Real.exp (ℓ * Real.log B) := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hBpos ℓ)]
  have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg hBR
  have hb0 : 0 ≤ b := hlogB0.trans hlogB
  have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
  have h3 : (ℓ : ℝ) * Real.log B ≤ u :=
    (mul_le_mul hℓ hlogB hlogB0 (hℓ0.trans hℓ)).trans hFb
  rw [h2] at h1
  exact h1.trans (Real.exp_le_exp.mpr h3)

/-- The construction for a fixed large `y`. -/
private theorem exists_carmichael_at (C : ℝ) (hC1 : 1 ≤ C)
    (hC : ∀ d : ℕ, 2 ≤ d → ∀ c : ℕ, Nat.Coprime c d →
      ∃ p : ℕ, p.Prime ∧ p ≡ c [MOD d] ∧ (p : ℝ) ≤ C * d * Real.log d ^ 2)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo 1 2) (γ : ℝ) (hγ : 0 < γ) (y : ℝ) (hy : 1 < y)
    (hcount : γ * y ^ θ / Real.log (y ^ θ) ≤
        ({q : ℕ | q.Prime ∧ y ^ θ / Real.log y ≤ q ∧ (q : ℝ) ≤ y ^ θ ∧
          ∀ p : ℕ, p.Prime → p ∣ q - 1 → (p : ℝ) ≤ y}.ncard : ℝ))
    (hlogK : Real.log (bdK C y) ≤ y ^ 3)
    (hpoolR : (bdK C y : ℝ) * ((bdD C y : ℝ) * bdD C y * bdJ C θ γ y + y ^ θ +
      bdK C y + 2) + 1 ≤ (2 : ℝ) ^ (γ * y ^ θ / Real.log (y ^ θ)))
    (hupper : C * bdD C y * bdT θ γ y * Real.log (bdD C y * bdT θ γ y) ^ 2 *
      (3 * y ^ 3 + 1) ≤ Real.exp (19 * θ * y)) :
    ∃ n : ℕ, n.IsCarmichael ∧ (cardFactors n).Prime ∧
      Real.exp (γ / 4 * y ^ θ * Real.log y) ≤ n ∧ (n : ℝ) ≤ Real.exp (Real.exp (19 * θ * y)) := by
  classical
  have hy0 : 0 < y := by linarith
  have hθ0 : 0 < θ := by linarith [hθ.1]
  set X := y ^ θ with hX
  have hX1 : 1 < X := Real.one_lt_rpow hy hθ0
  have hX0 : 0 < X := by linarith
  have hXy : X ≤ y ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hy.le hθ.2.le
    simpa using this
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hlogX : Real.log X = θ * Real.log y := Real.log_rpow hy0 θ
  have hlogX0 : 0 < Real.log X := by rw [hlogX]; positivity
  have hlogXy : Real.log X ≤ y := by
    rw [hlogX]
    have := log_le_half hy0
    nlinarith [hθ.2]
  -- The finite set of primes `q` with `q - 1` smooth.
  set S := {q : ℕ | q.Prime ∧ X / Real.log y ≤ q ∧ (q : ℝ) ≤ X ∧
    ∀ p : ℕ, p.Prime → p ∣ q - 1 → (p : ℝ) ≤ y} with hS
  have hSsub : S ⊆ Set.Iic ⌊X⌋₊ := fun q hq => Set.mem_Iic.mpr (Nat.le_floor hq.2.2.1)
  have hfin : S.Finite := (Set.finite_Iic _).subset hSsub
  set Q := hfin.toFinset with hQdef
  have hmemQ : ∀ q, q ∈ Q ↔ q ∈ S := fun q => Set.Finite.mem_toFinset hfin
  have hQcard : (Q.card : ℝ) = (S.ncard : ℝ) := by
    rw [Set.ncard_eq_toFinset_card S hfin]
  have hQp : ∀ q ∈ Q, q.Prime := fun q hq => ((hmemQ q).mp hq).1
  have hQX : ∀ q ∈ Q, (q : ℝ) ≤ X := fun q hq => ((hmemQ q).mp hq).2.2.1
  have hcount' : γ * X / Real.log X ≤ Q.card := by rw [hQcard]; exact hcount
  have hQpos : 0 < Q.card := by
    have : 0 < γ * X / Real.log X := by positivity
    exact_mod_cast this.trans_le hcount'
  have hQne : Q.Nonempty := Finset.card_pos.mp hQpos
  have hQcardX : (Q.card : ℝ) ≤ X := by
    have hsub : Q ⊆ Finset.Icc 1 ⌊X⌋₊ := by
      intro q hq
      exact Finset.mem_Icc.mpr ⟨(hQp q hq).one_lt.le, Nat.le_floor (hQX q hq)⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact (Nat.cast_le.mpr this).trans (Nat.floor_le hX0.le)
  -- The product `L` of the primes of `Q`.
  set L := ∏ q ∈ Q, q with hLdef
  have hL1 : 1 ≤ L := Finset.one_le_prod fun q hq => (hQp q hq).one_lt.le
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg hLR
  have hlogL : Real.log L ≤ y ^ 3 := by
    have h1 : Real.log L = ∑ q ∈ Q, Real.log q := by
      rw [hLdef, Nat.cast_prod, Real.log_prod]
      intro q hq; exact_mod_cast (hQp q hq).ne_zero
    have h2 : ∑ q ∈ Q, Real.log q ≤ ∑ _q ∈ Q, Real.log X :=
      Finset.sum_le_sum fun q hq => Real.log_le_log (by exact_mod_cast (hQp q hq).pos) (hQX q hq)
    rw [Finset.sum_const, nsmul_eq_mul] at h2
    have h3 : (Q.card : ℝ) * Real.log X ≤ X * Real.log X :=
      mul_le_mul_of_nonneg_right hQcardX hlogX0.le
    have h4 : X * Real.log X ≤ y ^ 2 * y := mul_le_mul hXy hlogXy hlogX0.le (by positivity)
    nlinarith
  -- The parameters.
  set K := bdK C y with hKdef
  have hK1 : 1 ≤ K := one_le_bdK hC1 hy.le
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hlogK0 : 0 ≤ Real.log K := Real.log_nonneg hKR
  have hKge : 5 * C * y ^ 6 ≤ K := Nat.le_ceil _
  have hy6 : 0 ≤ y ^ 6 := by positivity
  have hK0 : C * Real.log L ^ 2 ≤ K := by
    have : Real.log L ^ 2 ≤ (y ^ 3) ^ 2 := pow_le_pow_left₀ hlogL0 hlogL 2
    have : C * Real.log L ^ 2 ≤ C * y ^ 6 := by
      calc C * Real.log L ^ 2 ≤ C * (y ^ 3) ^ 2 := by gcongr
        _ = C * y ^ 6 := by ring
    nlinarith
  have hlogLK : Real.log (L * K) ≤ 2 * y ^ 3 := by
    rw [Real.log_mul (by positivity) (by positivity)]; linarith
  have hK1' : C * Real.log (L * K) ^ 2 ≤ K := by
    have h0 : 0 ≤ Real.log (L * K) := Real.log_nonneg (by nlinarith)
    have : C * Real.log (L * K) ^ 2 ≤ C * (2 * y ^ 3) ^ 2 := by gcongr
    nlinarith
  set E := bdE y with hEdef
  have hE0 : E ≠ 0 := pow_ne_zero _ (Nat.lcmUpto_ne_zero _)
  have hE : ∀ q ∈ Q, q - 1 ∣ E := by
    intro q hq
    have hqS := (hmemQ q).mp hq
    have hq2 := hqS.1.two_le
    refine dvd_lcmUpto_pow_three (by omega) (fun r hr hrq => Nat.le_floor (hqS.2.2.2 r hr hrq)) ?_
    have h1 : (q : ℝ) < ((⌊y⌋₊ + 1 : ℕ) : ℝ) ^ 2 := by
      have h2 : y < ((⌊y⌋₊ + 1 : ℕ) : ℝ) := by push_cast; exact Nat.lt_floor_add_one y
      calc (q : ℝ) ≤ X := hqS.2.2.1
        _ ≤ y ^ 2 := hXy
        _ < ((⌊y⌋₊ + 1 : ℕ) : ℝ) ^ 2 := by gcongr
    have h3 : q < (⌊y⌋₊ + 1) ^ 2 := by exact_mod_cast h1
    omega
  set D := bdD C y with hDdef
  have hlogLK2 : Real.log (L * K ^ 2) ≤ 3 * y ^ 3 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]; push_cast; linarith
  have hD : Real.log (L * K ^ 2) * (E * K ^ 4) < D := by
    have hEK : (0 : ℝ) ≤ (E : ℝ) * K ^ 4 := by positivity
    have h1 : Real.log (L * K ^ 2) * (E * K ^ 4) ≤ 3 * y ^ 3 * E * K ^ 4 := by
      have := mul_le_mul_of_nonneg_right hlogLK2 hEK
      linarith
    have h2 := Nat.lt_floor_add_one (3 * y ^ 3 * (E : ℝ) * (K : ℝ) ^ 4)
    rw [hDdef, bdD]
    push_cast
    linarith
  set T := bdT θ γ y with hTdef
  have hT : 2 ≤ T := two_le_bdT θ γ y
  set J := bdJ C θ γ y with hJdef
  have hJ : C * T * Real.log (D * T) ^ 2 ≤ J := Nat.le_ceil _
  have hpool : K * (D * D * J + Q.card + K + 2) ≤ 2 ^ Q.card - 1 := by
    have h1 : (2 : ℝ) ^ (γ * X / Real.log X) ≤ (2 : ℝ) ^ (Q.card : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hcount'
    rw [Real.rpow_natCast] at h1
    have h2 : ((K * (D * D * J + Q.card + K + 2) + 1 : ℕ) : ℝ) ≤ ((2 ^ Q.card : ℕ) : ℝ) := by
      push_cast
      have : (K : ℝ) * ((D : ℝ) * D * J + Q.card + K + 2) ≤
          (K : ℝ) * ((D : ℝ) * D * J + X + K + 2) := by gcongr
      linarith
    have h3 := Nat.cast_le.mp h2
    omega
  obtain ⟨n, ℓ, hcarm, hΩ, hℓp, hTℓ, hℓle, hnle, hnge⟩ :=
    main_construction C (by linarith) hC Q hQp hQne L rfl E hE0 hE K hK0 hK1' D hD T hT J hJ hpool
  refine ⟨n, hcarm, hΩ ▸ hℓp, ?_, ?_⟩
  · -- lower bound
    have hTge : γ * X * Real.log y / (4 * Real.log 2) ≤ T := by
      have := Nat.le_ceil (γ * X * Real.log y / (4 * Real.log 2))
      rw [hTdef, bdT]; push_cast; linarith
    refine exp_le_of_two_pow_le (T := T) ?_ hTℓ hnge
    have : γ / 4 * X * Real.log y / Real.log 2 = γ * X * Real.log y / (4 * Real.log 2) := by
      field_simp
    rw [this]; exact hTge
  · -- upper bound
    exact le_exp_of_le_pow (Nat.le_add_left 1 _) hnle (log_mul_sq_add_one_le hL1 hK1 hlogLK2)
      hℓle hupper

end exists_carmichael_prime_cardFactors_between_of_heathBrown

open exists_carmichael_prime_cardFactors_between_of_heathBrown Filter

/-- **Carmichael numbers with a prime number of prime factors in a range.** Assume Heath-Brown's
conjecture in the following form: there is a real constant $C$ such that for every natural
number $d \ge 2$ and every natural number $c$ coprime to $d$ there is a prime $p \equiv c
\pmod{d}$ with $p \le C d (\log d)^2$. Let $1 < \theta < 2$, and let $\gamma > 0$ be such that
for all sufficiently large real $y$, the number of primes $q$ with
$y^\theta / \log y \le q \le y^\theta$ such that every prime divisor of $q - 1$ is at most $y$
is at least $\gamma y^\theta / \log(y^\theta)$. Then there is a real $Y$ such that for every real
$y > Y$ there is a Carmichael number $n$ with $e^{(\gamma/4) y^\theta \log y} \le n \le
e^{e^{19 \theta y}}$ whose number of prime factors counted with multiplicity, $\Omega(n)$, is
prime.

The paper's proof uses its Lemma 2, which assumes Heath-Brown's conjecture (the paper's
Conjecture 3); here that assumption is an explicit hypothesis, as in Theorem 1.

Source: Thomas Wright, *Carmichael Numbers with a Prime Number of Prime Factors*, INTEGERS 24
(2024), Article A97, Theorem 3 (`integers-2024-A97-thm-3`). -/
public theorem exists_carmichael_prime_cardFactors_between_of_heathBrown
    (hHB : ∃ C : ℝ, ∀ d : ℕ, 2 ≤ d → ∀ c : ℕ, Nat.Coprime c d →
      ∃ p : ℕ, p.Prime ∧ p ≡ c [MOD d] ∧ (p : ℝ) ≤ C * d * Real.log d ^ 2)
    (θ : ℝ) (hθ : θ ∈ Set.Ioo 1 2) (γ : ℝ) (hγ : 0 < γ)
    (hQ : ∃ Y : ℝ, ∀ y : ℝ, Y < y →
      γ * y ^ θ / Real.log (y ^ θ) ≤
        ({q : ℕ | q.Prime ∧ y ^ θ / Real.log y ≤ q ∧ (q : ℝ) ≤ y ^ θ ∧
          ∀ p : ℕ, p.Prime → p ∣ q - 1 → (p : ℝ) ≤ y}.ncard : ℝ)) :
    ∃ Y : ℝ, ∀ y : ℝ, Y < y → ∃ n : ℕ, n.IsCarmichael ∧
      (ArithmeticFunction.cardFactors n).Prime ∧
      Real.exp (γ / 4 * y ^ θ * Real.log y) ≤ n ∧
      (n : ℝ) ≤ Real.exp (Real.exp (19 * θ * y)) := by
  obtain ⟨C₀, hC₀⟩ := hHB
  have hC1 : 1 ≤ max C₀ 1 := le_max_right _ _
  have hC : ∀ d : ℕ, 2 ≤ d → ∀ c : ℕ, Nat.Coprime c d →
      ∃ p : ℕ, p.Prime ∧ p ≡ c [MOD d] ∧ (p : ℝ) ≤ max C₀ 1 * d * Real.log d ^ 2 := by
    intro d hd c hc
    obtain ⟨p, hp, hpc, hple⟩ := hC₀ d hd c hc
    refine ⟨p, hp, hpc, hple.trans ?_⟩
    have : 0 ≤ (d : ℝ) * Real.log d ^ 2 := by positivity
    calc C₀ * d * Real.log d ^ 2 = C₀ * (d * Real.log d ^ 2) := by ring
      _ ≤ max C₀ 1 * (d * Real.log d ^ 2) := mul_le_mul_of_nonneg_right (le_max_left _ _) this
      _ = max C₀ 1 * d * Real.log d ^ 2 := by ring
  obtain ⟨Y₀, hY₀⟩ := hQ
  have hev : ∀ᶠ y in atTop, ∃ n : ℕ, n.IsCarmichael ∧ (ArithmeticFunction.cardFactors n).Prime ∧
      Real.exp (γ / 4 * y ^ θ * Real.log y) ≤ n ∧
      (n : ℝ) ≤ Real.exp (Real.exp (19 * θ * y)) := by
    filter_upwards [eventually_log_bdK_le hC1, eventually_pool hC1 hθ hγ,
      eventually_upper hC1 hθ hγ, eventually_gt_atTop (max Y₀ 1)] with y hlogK hpoolR hupper hy
    exact exists_carmichael_at (max C₀ 1) hC1 hC θ hθ γ hγ y
      (lt_of_le_of_lt (le_max_right _ _) hy) (hY₀ y (lt_of_le_of_lt (le_max_left _ _) hy))
      hlogK hpoolR hupper
  obtain ⟨Y, hY⟩ := eventually_atTop.mp hev
  exact ⟨Y, fun y hy => hY y hy.le⟩

end MetaMathlibExt
