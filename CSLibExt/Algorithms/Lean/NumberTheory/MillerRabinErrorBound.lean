/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.NumberTheory.MillerRabin
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.Index
public import Mathlib.NumberTheory.CarmichaelNumber

import Mathlib.NumberTheory.Multiplicity

/-!
# The Miller–Rabin error bound

CLRS, third edition, Theorem 31.38: if `n` is an odd composite number, the number of witnesses to
the compositeness of `n` is at least `(n - 1) / 2`. Equivalently, at most `(n - 1) / 2` of the
bases `1, …, n - 1` are *non-witnesses* (`card_nonwitnesses_le`), so one uniformly random base
fails to expose `n` with probability at most `1/2`, and `s` independent bases all fail with
probability at most `2^(-s)` (CLRS Theorem 31.39; `card_millerRabin_errors_le` counts the failing
`s`-tuples).

The proof follows CLRS: the non-witnesses lie in a proper subgroup `B` of `(ℤ/nℤ)ˣ`, so they are
at most `φ(n)/2 ≤ (n - 1)/2`.

* If some unit `x` has `x^(n-1) ≠ 1`, take `B = {x : x^(n-1) = 1}` (case 1).
* Otherwise `n` is a Carmichael number (Mathlib's `Nat.IsCarmichael`). Carmichael numbers are
  squarefree (`Nat.IsCarmichael.squarefree`), so not prime powers, so `n = n₁ n₂` with coprime
  `n₁, n₂ > 1`. With `j` the largest
  index such that some `v` has `v^(2^j u) ≡ -1`, take `B = {x : x^(2^j u) = ±1}`; the Chinese
  remainder theorem gives `w ≡ v (mod n₁)`, `w ≡ 1 (mod n₂)` outside `B` (case 2).

## The `1/4` bound

`card_nonwitnesses_le_quarter` sharpens this to at most `(n - 1) / 4` non-witnesses (the bound of
Monier and of Rabin, 1980), and `card_millerRabin_errors_le_quarter` turns it into error
probability at most `4^(-s)` for `s` bases. The proof finds a subgroup of index at least `4`
holding the non-witnesses, or counts them directly:

* `n = p^k` with `k ≥ 2` (`card_nonwitnesses_le_quarter_of_prime_pow`): non-witnesses satisfy
  `a^(n-1) ≡ 1`, and two of them that agree modulo `p` agree modulo `n` (their quotient `x` has
  `x^(p^(k-1)) = 1` by lifting the exponent, and `x^(n-1) = 1`), so there are at most
  `p - 1 ≤ (n - 1) / 4`.
* `n` not a prime power, with a unit `z` such that `z^(n-1) ≠ 1`
  (`card_nonwitnesses_le_quarter_of_pow_ne_one`): with `B = {x : x^m = ±1}` and `w` as in case 2,
  `w^(2m) = 1` but `z^(2m) ≠ 1`, so `w`, `z`, `w z` and `w⁻¹ z` all lie outside `B` and give four
  distinct cosets.
* Carmichael numbers (`card_nonwitnesses_le_quarter_of_carmichael`): they have three pairwise
  coprime factors `n₁ n₂ n₃ = n` (Mathlib's `Nat.IsCarmichael.three_le_card_primeFactors`), and
  `w₁ ≡ v (mod n₁)`, `w₂ ≡ v (mod n₂)` (each `≡ 1` modulo the other factors) give four distinct
  cosets of `B` in the same way.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MillerRabin

open Cslib.Algorithms.Lean TimeM

/-! ## Counting through a subgroup -/

/-- Residues in `1, …, n - 1` whose units lie in a subgroup of index at least `k` number at most
`(n - 1) / k`. -/
private theorem card_le_of_mem_subgroup_index {n k : ℕ} (hn : 1 < n) (hk : 0 < k)
    (B : Subgroup (ZMod n)ˣ) (hB : k ≤ B.index) (S : Finset ℕ) (hS : ∀ a ∈ S, 0 < a ∧ a < n)
    (hmem : ∀ a ∈ S, ∃ h : a.Coprime n, ZMod.unitOfCoprime a h ∈ B) :
    S.card ≤ (n - 1) / k := by
  have : NeZero n := ⟨by omega⟩
  classical
  let f : ℕ → (ZMod n)ˣ := fun a => if h : a.Coprime n then ZMod.unitOfCoprime a h else 1
  have hcard : S.card ≤ (Finset.univ.filter (· ∈ B)).card := by
    refine Finset.card_le_card_of_injOn f (fun a ha => ?_) (fun a ha b hb hab => ?_)
    · obtain ⟨h, hB⟩ := hmem a ha
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, f]
      rwa [dite_eq_left h]
    · obtain ⟨ha', _⟩ := hmem a ha
      obtain ⟨hb', _⟩ := hmem b hb
      have hcoe := congrArg (fun u : (ZMod n)ˣ => (u : ZMod n)) hab
      simp only [f] at hcoe
      rw [dite_eq_left ha', dite_eq_left hb', ZMod.coe_unitOfCoprime,
        ZMod.coe_unitOfCoprime] at hcoe
      have := (ZMod.natCast_eq_natCast_iff' a b n).1 hcoe
      rwa [Nat.mod_eq_of_lt (hS a ha).2, Nat.mod_eq_of_lt (hS b hb).2] at this
  have hBk : k * Nat.card B ≤ n - 1 := by
    have hmul := B.card_mul_index
    have hG : Nat.card (ZMod n)ˣ ≤ n - 1 := by
      rw [Nat.card_eq_fintype_card]
      exact Nat.card_units_zmod_lt_sub_one hn
    have : Nat.card B * k ≤ Nat.card B * B.index := Nat.mul_le_mul_left _ hB
    rw [Nat.mul_comm]
    omega
  have hfilter : (Finset.univ.filter (· ∈ B)).card = Nat.card B := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Nat.le_div_iff_mul_le hk, Nat.mul_comm]
  calc k * S.card ≤ k * Nat.card B := Nat.mul_le_mul_left _ (hfilter ▸ hcard)
    _ ≤ n - 1 := hBk

/-- Residues in `1, …, n - 1` whose units lie in a proper subgroup of `(ℤ/nℤ)ˣ` number at most
`(n - 1) / 2`. -/
private theorem card_le_of_mem_subgroup {n : ℕ} (hn : 1 < n) (B : Subgroup (ZMod n)ˣ) (hB : B ≠ ⊤)
    (S : Finset ℕ) (hS : ∀ a ∈ S, 0 < a ∧ a < n)
    (hmem : ∀ a ∈ S, ∃ h : a.Coprime n, ZMod.unitOfCoprime a h ∈ B) :
    S.card ≤ (n - 1) / 2 :=
  card_le_of_mem_subgroup_index hn (by norm_num) B (Subgroup.one_lt_index_of_ne_top hB) S hS hmem

/-! ## Residues and `ZMod n` -/

private theorem natCast_eq_one_iff {n x : ℕ} (hn : 1 < n) : (x : ZMod n) = 1 ↔ x % n = 1 := by
  rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff', Nat.one_mod_eq_one.2 (by omega)]

private theorem natCast_eq_neg_one_iff {n x : ℕ} (hn : 1 < n) :
    (x : ZMod n) = -1 ↔ x % n = n - 1 := by
  have h : ((n - 1 : ℕ) : ZMod n) = -1 := by
    rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]
  rw [← h, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (show n - 1 < n by omega)]

private theorem pow_two_pow_mod (n x i : ℕ) :
    (x * x % n) ^ (2 ^ i) % n = x ^ (2 ^ (i + 1)) % n := by
  rw [Nat.pow_mod, Nat.mod_mod, ← Nat.pow_mod, ← pow_two, ← pow_mul, ← pow_succ']

/-! ## Non-witnesses -/

/-- **When the squaring loop finds no witness.** Let $n$, $k$ and $x$ be natural numbers with
$x < n$. If the Miller–Rabin squaring loop modulo $n$, started at $x$ with $k$ squarings to
perform, reports no witness, then $x = 1$ or $x^{2^i} \equiv -1 \pmod n$ for some $i < k$. -/
theorem witnessLoop_eq_false_imp {n : ℕ} :
    ∀ k x, x < n → (witnessLoop n k x).ret = false →
      x = 1 ∨ ∃ i < k, x ^ (2 ^ i) % n = n - 1 := by
  intro k
  induction k with
  | zero =>
      intro x _ h
      simpa [witnessLoop] using h
  | succ k ih =>
      intro x hx h
      simp only [witnessLoop, ret_bind] at h
      split_ifs at h with hc
      · simp at h
      · rcases ih _ (Nat.mod_lt _ (by omega)) h with hy | ⟨i, hi, hy⟩
        · rcases not_and_or.1 hc with h1 | h1
          · exact absurd hy h1
          · rw [not_and_or, not_not, not_not] at h1
            rcases h1 with h1 | h1
            · exact Or.inl h1
            · exact Or.inr ⟨0, Nat.zero_lt_succ _, by simp [h1]⟩
        · exact Or.inr ⟨i + 1, by omega, by rwa [← pow_two_pow_mod]⟩

/-- **What a non-witness satisfies.** Let $n > 1$ and write $n - 1 = 2^t u$ with $u$ odd. If $a$ is
a natural number for which the Miller–Rabin witness test $\mathrm{WITNESS}(a, n)$ returns false,
then $a^u \equiv 1 \pmod n$, or $a^{2^i u} \equiv -1 \pmod n$ for some $i < t$. -/
theorem witness_eq_false_imp {n a : ℕ} (hn : 1 < n) (h : (witness a n).ret = false) :
    a ^ (twoAdicSplit (n - 1)).2 % n = 1 ∨
      ∃ i < (twoAdicSplit (n - 1)).1, a ^ (2 ^ i * (twoAdicSplit (n - 1)).2) % n = n - 1 := by
  obtain ⟨_, hodd⟩ := twoAdicSplit_spec (n - 1) (by omega)
  have hu : 0 < (twoAdicSplit (n - 1)).2 := by omega
  simp only [witness, ret_bind] at h
  rw [ModularExponentiation.modularExponentiation_correct a _ n hu (by omega)] at h
  rcases witnessLoop_eq_false_imp _ _ (Nat.mod_lt _ (by omega)) h with h1 | ⟨i, hi, h1⟩
  · exact Or.inl h1
  · refine Or.inr ⟨i, hi, ?_⟩
    rwa [← Nat.pow_mod, ← pow_mul, Nat.mul_comm] at h1

/-- **Non-witnesses pass Fermat's test and are units.** Let $n > 1$ and let $a$ be a natural number
such that the witness test $\mathrm{WITNESS}(a, n)$ returns false. Then $a^{n-1} \equiv 1 \pmod n$
and $a$ is coprime to $n$. -/
theorem coprime_of_witness_eq_false {n a : ℕ} (hn : 1 < n) (h : (witness a n).ret = false) :
    a ^ (n - 1) % n = 1 ∧ a.Coprime n := by
  have hf : a ^ (n - 1) % n = 1 := by
    by_contra hne
    simp [witness_of_pow_ne_one hn hne] at h
  refine ⟨hf, (ZMod.isUnit_iff_coprime a n).1 ?_⟩
  refine IsUnit.of_pow_eq_one (n := n - 1) ?_ (by omega)
  rw [← Nat.cast_pow, natCast_eq_one_iff hn]
  exact hf

/-- **Non-witnesses of a number.** For a natural number $n$, the non-witnesses of $n$ form the
finite set of bases $a$ with $0 < a < n$ for which the Miller–Rabin witness test
$\mathrm{WITNESS}(a, n)$ returns false, that is, the bases that do not witness the compositeness
of $n$. -/
def nonwitnesses (n : ℕ) : Finset ℕ := (Finset.Ioo 0 n).filter fun a => (witness a n).ret = false

/-! ## Case 1: some unit fails Fermat's test -/

/-- **At most half the bases are non-witnesses when some unit fails Fermat's test.** Let $n > 1$,
and suppose some $x$ coprime to $n$ has $x^{n-1} \not\equiv 1 \pmod n$. Then at most $(n - 1)/2$
of the bases $1, \dots, n - 1$ are non-witnesses for $n$.

The proof shows that the non-witnesses lie in the proper subgroup $\{y : y^{n-1} = 1\}$ of
$(\mathbb{Z}/n\mathbb{Z})^\times$. -/
theorem card_nonwitnesses_le_of_pow_ne_one {n x : ℕ} (hn : 1 < n) (hx : x.Coprime n)
    (hfx : x ^ (n - 1) % n ≠ 1) : (nonwitnesses n).card ≤ (n - 1) / 2 := by
  let B : Subgroup (ZMod n)ˣ := (powMonoidHom (n - 1) : (ZMod n)ˣ →* (ZMod n)ˣ).ker
  have hmemB : ∀ a (h : a.Coprime n), ZMod.unitOfCoprime a h ∈ B ↔ a ^ (n - 1) % n = 1 := by
    intro a h
    simp only [B, MonoidHom.mem_ker, powMonoidHom_apply, Units.ext_iff, Units.val_pow_eq_pow_val,
      ZMod.coe_unitOfCoprime, Units.val_one, ← Nat.cast_pow]
    exact natCast_eq_one_iff hn
  refine card_le_of_mem_subgroup hn B ?_ _ (fun a ha => ?_) (fun a ha => ?_)
  · intro htop
    have := (hmemB x hx).1 (htop ▸ Subgroup.mem_top _)
    exact hfx this
  · simp only [nonwitnesses, Finset.mem_filter, Finset.mem_Ioo] at ha
    exact ha.1
  · simp only [nonwitnesses, Finset.mem_filter, Finset.mem_Ioo] at ha
    obtain ⟨hf, hc⟩ := coprime_of_witness_eq_false hn ha.2
    exact ⟨hc, (hmemB a hc).2 hf⟩

/-! ## Case 2: Carmichael numbers -/

/-- A composite number that is not a prime power with exponent `≥ 2` splits into two coprime
factors larger than `1`. -/
private theorem exists_coprime_factors {n : ℕ} (hn : 1 < n) (hcomp : ¬ n.Prime)
    (hpow : ∀ p e, p.Prime → 2 ≤ e → n ≠ p ^ e) :
    ∃ n₁ n₂, 1 < n₁ ∧ 1 < n₂ ∧ n₁.Coprime n₂ ∧ n₁ * n₂ = n := by
  set p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hn0 : n ≠ 0 := by omega
  have hk : 0 < n.factorization p := hp.factorization_pos_of_dvd hn0 (Nat.minFac_dvd n)
  refine ⟨p ^ n.factorization p, n / p ^ n.factorization p, Nat.one_lt_pow hk.ne' hp.one_lt, ?_,
    Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hn0), Nat.ordProj_mul_ordCompl_eq_self n p⟩
  have hpos := Nat.ordCompl_pos p hn0
  by_contra hle
  have h1 : n / p ^ n.factorization p = 1 := by omega
  have heq : n = p ^ n.factorization p := by
    have := Nat.ordProj_mul_ordCompl_eq_self n p
    rw [h1, Nat.mul_one] at this
    exact this.symm
  rcases Nat.lt_or_ge (n.factorization p) 2 with h | h
  · have : n.factorization p = 1 := by omega
    rw [this, pow_one] at heq
    exact hcomp (heq ▸ hp)
  · exact hpow p _ hp h heq

/-- The subgroup `{g : g^m = ±1}` of `(ℤ/nℤ)ˣ`. -/
private def pmOnePowSubgroup (n m : ℕ) : Subgroup (ZMod n)ˣ where
  carrier := {g | g ^ m = 1 ∨ g ^ m = -1}
  one_mem' := Or.inl (one_pow m)
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb) <;> simp [mul_pow, ha, hb]
  inv_mem' := by
    rintro a (ha | ha) <;> simp [inv_pow, ha]

private theorem unitOfCoprime_mem_pmOnePowSubgroup {n m a : ℕ} (h : a.Coprime n) :
    ZMod.unitOfCoprime a h ∈ pmOnePowSubgroup n m ↔
      (a : ZMod n) ^ m = 1 ∨ (a : ZMod n) ^ m = -1 := by
  change (ZMod.unitOfCoprime a h) ^ m = 1 ∨ (ZMod.unitOfCoprime a h) ^ m = -1 ↔ _
  simp only [Units.ext_iff, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one,
    Units.val_neg]

private theorem natCast_sub_one {n : ℕ} (hn : 1 < n) : ((n - 1 : ℕ) : ZMod n) = -1 := by
  rw [Nat.cast_sub (by omega), ZMod.natCast_self, Nat.cast_one, zero_sub]

private theorem odd_of_dvd_odd {n d : ℕ} (hodd : n % 2 = 1) (hd : d ∣ n) : d % 2 = 1 := by
  by_contra h
  have h2 : 2 ∣ d := by omega
  have := dvd_trans h2 hd
  omega

/-- The subgroup that holds the non-witnesses (CLRS's `B` in case 2, for any odd `n`): with
`n - 1 = 2^t u` and `j` the largest index such that some unit `v` has `v^(2^j u) ≡ -1`, every
non-witness `a` has `a^m ≡ ±1` for `m = 2^j u`, and `2 m` divides `n - 1`. -/
private theorem exists_liar_subgroup {n : ℕ} (hn : 1 < n) (hodd : n % 2 = 1) :
    ∃ m v : ℕ, v.Coprime n ∧ (v : ZMod n) ^ m = -1 ∧ 2 * m ∣ n - 1 ∧
      ∀ a ∈ nonwitnesses n, ∃ h : a.Coprime n, ZMod.unitOfCoprime a h ∈ pmOnePowSubgroup n m := by
  obtain ⟨hsplit, hoddu⟩ := twoAdicSplit_spec (n - 1) (by omega)
  set t := (twoAdicSplit (n - 1)).1
  set u := (twoAdicSplit (n - 1)).2
  have ht : 1 ≤ t := by
    by_contra h0
    have ht0 : t = 0 := by omega
    rw [ht0, pow_zero, one_mul] at hsplit
    omega
  classical
  let P : ℕ → Prop := fun i => ∃ v < n, v.Coprime n ∧ v ^ (2 ^ i * u) % n = n - 1
  have hP0 : P 0 := by
    refine ⟨n - 1, by omega, (ZMod.isUnit_iff_coprime _ _).1 ?_, ?_⟩
    · rw [natCast_sub_one hn]
      exact isUnit_one.neg
    · rw [pow_zero, one_mul, ← natCast_eq_neg_one_iff hn, Nat.cast_pow, natCast_sub_one hn,
        Odd.neg_one_pow (Nat.odd_iff.2 hoddu)]
  set j := Nat.findGreatest P (t - 1)
  have hjP : P j := Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hjt : j ≤ t - 1 := Nat.findGreatest_le _
  obtain ⟨v, -, hvc, hvm⟩ := hjP
  refine ⟨2 ^ j * u, v, hvc, ?_, ?_, fun a ha => ?_⟩
  · rw [← Nat.cast_pow, natCast_eq_neg_one_iff hn]
    exact hvm
  · rw [hsplit, ← Nat.mul_assoc, ← pow_succ']
    exact Nat.mul_dvd_mul_right (pow_dvd_pow 2 (by omega)) u
  · simp only [nonwitnesses, Finset.mem_filter, Finset.mem_Ioo] at ha
    obtain ⟨-, hc⟩ := coprime_of_witness_eq_false hn ha.2
    refine ⟨hc, (unitOfCoprime_mem_pmOnePowSubgroup hc).2 ?_⟩
    rcases witness_eq_false_imp hn ha.2 with h1 | ⟨i, hi, h1⟩
    · left
      rw [Nat.mul_comm, pow_mul, ← Nat.cast_pow, (natCast_eq_one_iff hn).2 h1, one_pow]
    · have hij : i ≤ j := Nat.le_findGreatest (by omega) ⟨a, ha.1.2, hc, h1⟩
      have hai : (a : ZMod n) ^ (2 ^ i * u) = -1 := by
        rw [← Nat.cast_pow, natCast_eq_neg_one_iff hn]
        exact h1
      have hexp : 2 ^ j * u = 2 ^ i * u * 2 ^ (j - i) := by
        rw [Nat.mul_right_comm, ← pow_add, Nat.add_sub_cancel' hij]
      rw [hexp, pow_mul, hai]
      rcases Nat.eq_or_lt_of_le hij with hji | hji
      · right
        rw [← hji, Nat.sub_self, pow_zero, pow_one]
      · left
        exact Even.neg_one_pow (Nat.even_pow.2 ⟨even_two, by omega⟩)

/-- The Chinese remainder theorem for units: a unit `w` with `w ≡ v (mod n₁)` and
`w ≡ 1 (mod n₂)`. -/
private theorem exists_crt_unit {n n₁ n₂ v : ℕ} (hco : n₁.Coprime n₂) (hmul : n₁ * n₂ = n)
    (hvc : v.Coprime n) :
    ∃ w : ℕ, w.Coprime n ∧ (w : ZMod n₁) = v ∧ (w : ZMod n₂) = 1 := by
  have hd₁ : n₁ ∣ n := ⟨n₂, hmul.symm⟩
  obtain ⟨w, hw₁, hw₂⟩ := Nat.chineseRemainder hco v 1
  refine ⟨w, ?_, (ZMod.natCast_eq_natCast_iff' _ _ _).2 hw₁, ?_⟩
  · rw [← hmul]
    refine Nat.Coprime.mul_right ?_ ?_
    · rw [Nat.Coprime, Nat.ModEq.gcd_eq hw₁]
      exact Nat.Coprime.coprime_dvd_right hd₁ hvc
    · rw [Nat.Coprime, Nat.ModEq.gcd_eq hw₂, Nat.gcd_one_left]
  · rw [← Nat.cast_one]
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).2 hw₂

/-- A unit whose power `g^m` is `-1` modulo one factor of `n` and `1` modulo another (both larger
than `2`) is not in `{x : x^m = ±1}`. -/
private theorem not_mem_pmOnePowSubgroup {n na nb m : ℕ} (ha : na ∣ n) (hb : nb ∣ n)
    [Fact (2 < na)] [Fact (2 < nb)] (g : (ZMod n)ˣ)
    (hga : ZMod.castHom ha (ZMod na) ((g : ZMod n) ^ m) = -1)
    (hgb : ZMod.castHom hb (ZMod nb) ((g : ZMod n) ^ m) = 1) : g ∉ pmOnePowSubgroup n m := by
  rintro (h | h) <;> have h' := congrArg (fun x : (ZMod n)ˣ => (x : ZMod n)) h <;>
    simp only [Units.val_pow_eq_pow_val, Units.val_one, Units.val_neg] at h'
  · rw [h', map_one] at hga
    exact ZMod.neg_one_ne_one hga.symm
  · rw [h', map_neg, map_one] at hgb
    exact ZMod.neg_one_ne_one hgb

/-- **At most half the bases are non-witnesses for a Carmichael number.** Let $n$ be a Carmichael
number: $n > 2$, $n$ is not prime, and $b^{n-1} \equiv 1 \pmod n$ for every $b$ coprime to $n$.
Then at most $(n - 1)/2$ of the bases $1, \dots, n - 1$ are non-witnesses for $n$.

The proof shows that the non-witnesses lie in a proper subgroup of
$(\mathbb{Z}/n\mathbb{Z})^\times$.

Source: CLRS, third edition, Theorem 31.38, case 2. -/
theorem card_nonwitnesses_le_of_carmichael {n : ℕ} (hC : n.IsCarmichael) :
    (nonwitnesses n).card ≤ (n - 1) / 2 := by
  have hn : 1 < n := by have := hC.two_lt; omega
  have hodd : n % 2 = 1 := Nat.odd_iff.1 hC.odd
  -- Carmichael numbers are squarefree, so not prime powers, so they split into coprime factors
  obtain ⟨n₁, n₂, h₁, h₂, hco, hmul⟩ := exists_coprime_factors hn hC.not_prime (by
    intro p e hp he heq
    have hpp : p * p ∣ n := heq ▸ (pow_two p ▸ pow_dvd_pow p he)
    exact hp.one_lt.ne' (Nat.isUnit_iff.1 (hC.squarefree p hpp)))
  have hd₁ : n₁ ∣ n := ⟨n₂, hmul.symm⟩
  have hd₂ : n₂ ∣ n := ⟨n₁, by rw [← hmul, Nat.mul_comm]⟩
  have : Fact (2 < n₁) := ⟨by have := odd_of_dvd_odd hodd hd₁; omega⟩
  have : Fact (2 < n₂) := ⟨by have := odd_of_dvd_odd hodd hd₂; omega⟩
  -- `B = {x : x^m = ±1}` holds the non-witnesses; `w ≡ v (mod n₁)`, `w ≡ 1 (mod n₂)` is outside
  obtain ⟨m, v, hvc, hvm, -, hmem⟩ := exists_liar_subgroup hn hodd
  obtain ⟨w, hwc, hw₁, hw₂⟩ := exists_crt_unit hco hmul hvc
  refine card_le_of_mem_subgroup hn (pmOnePowSubgroup n m) (fun htop => ?_) _ (fun a ha => ?_)
    hmem
  · refine not_mem_pmOnePowSubgroup hd₁ hd₂ (ZMod.unitOfCoprime w hwc) ?_ ?_
      (htop ▸ Subgroup.mem_top _)
    · rw [map_pow, ZMod.coe_unitOfCoprime, map_natCast, hw₁]
      have := congrArg (ZMod.castHom hd₁ (ZMod n₁)) hvm
      rwa [map_pow, map_natCast, map_neg, map_one] at this
    · rw [map_pow, ZMod.coe_unitOfCoprime, map_natCast, hw₂, one_pow]
  · simp only [nonwitnesses, Finset.mem_filter, Finset.mem_Ioo] at ha
    exact ha.1

/-! ## The bound -/

/-- An odd composite `n` for which every unit `x` has `x^(n-1) ≡ 1` is a Carmichael number. -/
private theorem isCarmichael_of_forall {n : ℕ} (hn : 1 < n) (hodd : n % 2 = 1) (hcomp : ¬ n.Prime)
    (h : ∀ x, x.Coprime n → x ^ (n - 1) % n = 1) : n.IsCarmichael := by
  refine ⟨by omega, hcomp, fun b hb => ?_⟩
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · simp [Nat.coprime_zero_left] at hb
      omega
    · exact hb0
  rw [Nat.probablePrime_iff_modEq n hb1, Nat.ModEq, Nat.one_mod_eq_one.2 (by omega)]
  exact h b hb


/-- **At most half the bases are non-witnesses.** Let $n > 1$ be odd and not prime. Then at most
$(n - 1)/2$ of the bases $1, \dots, n - 1$ are non-witnesses for $n$; equivalently, at least
$(n - 1)/2$ of them are witnesses to the compositeness of $n$.

Source: CLRS, third edition, Theorem 31.38. -/
theorem card_nonwitnesses_le {n : ℕ} (hn : 1 < n) (hodd : n % 2 = 1) (hcomp : ¬ n.Prime) :
    (nonwitnesses n).card ≤ (n - 1) / 2 := by
  by_cases h : ∃ x, x.Coprime n ∧ x ^ (n - 1) % n ≠ 1
  · obtain ⟨x, hx, hfx⟩ := h
    exact card_nonwitnesses_le_of_pow_ne_one hn hx hfx
  · push Not at h
    exact card_nonwitnesses_le_of_carmichael (isCarmichael_of_forall hn hodd hcomp h)

/-- **Miller–Rabin answers prime exactly when no base is a witness.** For every natural number
$n$ and every list of bases, the Miller–Rabin test on $n$ with these bases answers *prime* if and
only if, for every base $a$ in the list, the witness test $\mathrm{WITNESS}(a, n)$ returns false,
that is, $a$ is not a witness to the compositeness of $n$. -/
theorem millerRabin_eq_true_iff (n : ℕ) :
    ∀ bases : List ℕ, (millerRabin n bases).ret = true ↔ ∀ a ∈ bases, (witness a n).ret = false
  | [] => by simp [millerRabin]
  | a :: as => by
      by_cases ha : (witness a n).ret = true
      · simp [millerRabin, ha]
      · simp only [Bool.not_eq_true] at ha
        simp [millerRabin, ha, millerRabin_eq_true_iff n as]

/-- The base lists on which `MILLER-RABIN` answers *prime* are the lists of non-witnesses. -/
private theorem millerRabin_errors_eq (n s : ℕ) :
    ((Fintype.piFinset fun _ : Fin s => Finset.Ioo 0 n).filter
        fun b => (millerRabin n (List.ofFn b)).ret = true) =
      Fintype.piFinset fun _ : Fin s => nonwitnesses n := by
  ext b
  simp only [Finset.mem_filter, Fintype.mem_piFinset, millerRabin_eq_true_iff, List.mem_ofFn,
    forall_exists_index, forall_apply_eq_imp_iff, nonwitnesses]
  exact ⟨fun ⟨h1, h2⟩ i => ⟨h1 i, h2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩

/-- **Half error bound for Miller–Rabin with several bases.** Let $n > 1$ be odd and not prime,
and let $s$ be a natural number. Among the $(n - 1)^s$ lists $(b_1, \dots, b_s)$ of bases with
$0 < b_i < n$, at most $((n - 1)/2)^s$ make the Miller–Rabin test of $n$ with bases
$b_1, \dots, b_s$ answer *prime*.

With uniformly random bases the error probability is therefore at most $2^{-s}$.

Source: CLRS, third edition, Theorem 31.39, in counting form. -/
theorem card_millerRabin_errors_le {n : ℕ} (hn : 1 < n) (hodd : n % 2 = 1) (hcomp : ¬ n.Prime)
    (s : ℕ) :
    ((Fintype.piFinset fun _ : Fin s => Finset.Ioo 0 n).filter
        fun b => (millerRabin n (List.ofFn b)).ret = true).card ≤ ((n - 1) / 2) ^ s := by
  rw [millerRabin_errors_eq, Fintype.card_piFinset_const]
  exact Nat.pow_le_pow_left (card_nonwitnesses_le hn hodd hcomp) s

theorem card_bases (n s : ℕ) :
    (Fintype.piFinset fun _ : Fin s => Finset.Ioo 0 n).card = (n - 1) ^ s := by
  rw [Fintype.card_piFinset_const, Nat.card_Ioo, Nat.sub_zero]

/-! ## The `1/4` bound -/

/-- A subgroup of a finite commutative group has index at least `4` if `g₁`, `g₂`, `g₁ g₂` and
`g₁⁻¹ g₂` all lie outside it: then `B`, `g₁ B`, `g₂ B` and `g₁ g₂ B` are four distinct cosets. -/
private theorem four_le_index {G : Type*} [CommGroup G] [Finite G] (B : Subgroup G) {g₁ g₂ : G}
    (h₁ : g₁ ∉ B) (h₂ : g₂ ∉ B) (h₁₂ : g₁ * g₂ ∉ B) (h₁₂' : g₁⁻¹ * g₂ ∉ B) : 4 ≤ B.index := by
  classical
  have := Fintype.ofFinite (G ⧸ B)
  have hne : ∀ a b : G, a⁻¹ * b ∉ B → (a : G ⧸ B) ≠ (b : G ⧸ B) :=
    fun a b h hab => h (QuotientGroup.eq.1 hab)
  have hc : (g₂ : G ⧸ B) ≠ ((g₁ * g₂ : G) : G ⧸ B) :=
    hne _ _ (by rwa [mul_comm g₁, inv_mul_cancel_left])
  have hb : (g₁ : G ⧸ B) ∉ ({(g₂ : G ⧸ B), ((g₁ * g₂ : G) : G ⧸ B)} : Finset (G ⧸ B)) := by
    rw [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hne _ _ h₁₂', hne _ _ (by rwa [inv_mul_cancel_left])⟩
  have ha : ((1 : G) : G ⧸ B) ∉
      ({(g₁ : G ⧸ B), (g₂ : G ⧸ B), ((g₁ * g₂ : G) : G ⧸ B)} : Finset (G ⧸ B)) := by
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton, not_or, not_or]
    exact ⟨hne _ _ (by rwa [inv_one, one_mul]), hne _ _ (by rwa [inv_one, one_mul]),
      hne _ _ (by rwa [inv_one, one_mul])⟩
  have hS := Finset.card_le_univ
    ({((1 : G) : G ⧸ B), (g₁ : G ⧸ B), (g₂ : G ⧸ B), ((g₁ * g₂ : G) : G ⧸ B)} : Finset (G ⧸ B))
  rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hb, Finset.card_pair hc] at hS
  rw [Subgroup.index, Nat.card_eq_fintype_card]
  exact hS

/-- A residue that is `1` modulo two coprime factors of `n` is `1` modulo `n`. -/
private theorem natCast_eq_one_of_coprime {n n₁ n₂ x : ℕ} (hco : n₁.Coprime n₂)
    (hmul : n₁ * n₂ = n) (h₁ : (x : ZMod n₁) = 1) (h₂ : (x : ZMod n₂) = 1) : (x : ZMod n) = 1 := by
  rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at h₁ h₂ ⊢
  rw [← hmul]
  exact (Nat.modEq_and_modEq_iff_modEq_mul hco).1 ⟨h₁, h₂⟩

private theorem pow_two_mul_eq_one_of_mem {n m : ℕ} {g : (ZMod n)ˣ}
    (hg : g ∈ pmOnePowSubgroup n m) : g ^ (2 * m) = 1 := by
  rcases hg with h | h <;> rw [Nat.mul_comm, pow_mul, h] <;> simp

/-- **At most a quarter of the bases are non-witnesses when some unit fails Fermat's test and the
modulus is not a prime power.** Let $n > 1$ be odd and not prime, and not of the form $p^e$ with
$p$ prime and $e \ge 2$. Suppose some $z$ coprime to $n$ has $z^{n-1} \not\equiv 1 \pmod n$. Then
at most $(n - 1)/4$ of the bases $1, \dots, n - 1$ are non-witnesses for $n$. -/
theorem card_nonwitnesses_le_quarter_of_pow_ne_one {n z : ℕ} (hn : 1 < n) (hodd : n % 2 = 1)
    (hcomp : ¬ n.Prime) (hpow : ∀ p e, p.Prime → 2 ≤ e → n ≠ p ^ e) (hz : z.Coprime n)
    (hfz : z ^ (n - 1) % n ≠ 1) : (nonwitnesses n).card ≤ (n - 1) / 4 := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨m, v, hvc, hvm, hdvd, hmem⟩ := exists_liar_subgroup hn hodd
  obtain ⟨n₁, n₂, h₁, h₂, hco, hmul⟩ := exists_coprime_factors hn hcomp hpow
  have hd₁ : n₁ ∣ n := ⟨n₂, hmul.symm⟩
  have hd₂ : n₂ ∣ n := ⟨n₁, by rw [← hmul, Nat.mul_comm]⟩
  have : Fact (2 < n₁) := ⟨by have := odd_of_dvd_odd hodd hd₁; omega⟩
  have : Fact (2 < n₂) := ⟨by have := odd_of_dvd_odd hodd hd₂; omega⟩
  obtain ⟨w, hwc, hw₁, hw₂⟩ := exists_crt_unit hco hmul hvc
  set W := ZMod.unitOfCoprime w hwc
  set Z := ZMod.unitOfCoprime z hz
  have hv₁ : (v : ZMod n₁) ^ m = -1 := by
    have := congrArg (ZMod.castHom hd₁ (ZMod n₁)) hvm
    rwa [map_pow, map_natCast, map_neg, map_one] at this
  have hW₁ : ZMod.castHom hd₁ (ZMod n₁) ((W : ZMod n) ^ m) = -1 := by
    rw [map_pow, ZMod.coe_unitOfCoprime, map_natCast, hw₁, hv₁]
  have hW₂ : ZMod.castHom hd₂ (ZMod n₂) ((W : ZMod n) ^ m) = 1 := by
    rw [map_pow, ZMod.coe_unitOfCoprime, map_natCast, hw₂, one_pow]
  have hWH : W ∉ pmOnePowSubgroup n m := not_mem_pmOnePowSubgroup hd₁ hd₂ W hW₁ hW₂
  -- `w^(2m) = 1`, componentwise
  have hW2 : W ^ (2 * m) = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one, ← Nat.cast_pow]
    refine natCast_eq_one_of_coprime hco hmul ?_ ?_
    · rw [Nat.cast_pow, hw₁, Nat.mul_comm, pow_mul, hv₁]
      simp
    · rw [Nat.cast_pow, hw₂, one_pow]
  -- `z^(2m) ≠ 1`, since `2m ∣ n - 1`
  have hZ2 : Z ^ (2 * m) ≠ 1 := by
    intro h
    apply hfz
    obtain ⟨c, hc⟩ := hdvd
    have hZn : Z ^ (n - 1) = 1 := by rw [hc, pow_mul, h, one_pow]
    have := congrArg (fun x : (ZMod n)ˣ => (x : ZMod n)) hZn
    simp only [Units.val_pow_eq_pow_val, Z, ZMod.coe_unitOfCoprime, Units.val_one,
      ← Nat.cast_pow] at this
    exact (natCast_eq_one_iff hn).1 this
  have hout : ∀ g : (ZMod n)ˣ, g ^ (2 * m) = 1 → g * Z ∉ pmOnePowSubgroup n m := by
    intro g hg hmemg
    apply hZ2
    have := pow_two_mul_eq_one_of_mem hmemg
    rwa [mul_pow, hg, one_mul] at this
  have hidx : 4 ≤ (pmOnePowSubgroup n m).index := by
    refine four_le_index _ hWH (by simpa using hout 1 (one_pow _)) (hout W hW2)
      (hout W⁻¹ (by rw [inv_pow, hW2, inv_one]))
  refine card_le_of_mem_subgroup_index hn (by norm_num) _ hidx _ (fun a ha => ?_) hmem
  simp only [nonwitnesses, Finset.mem_filter, Finset.mem_Ioo] at ha
  exact ha.1

/-- A Carmichael number splits into three pairwise coprime factors larger than `1`: it is
squarefree with at least three prime factors (`Nat.IsCarmichael.three_le_card_primeFactors`). -/
private theorem exists_three_coprime_factors {n : ℕ} (hC : n.IsCarmichael) :
    ∃ n₁ n₂ n₃, 1 < n₁ ∧ 1 < n₂ ∧ 1 < n₃ ∧ n₁.Coprime n₂ ∧ n₁.Coprime n₃ ∧ n₂.Coprime n₃ ∧
      n₁ * n₂ * n₃ = n := by
  have hn0 : n ≠ 0 := by have := hC.two_lt; omega
  obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ :=
    Finset.two_lt_card.1 (show 2 < n.primeFactors.card by
      have := hC.three_le_card_primeFactors; omega)
  rw [Nat.mem_primeFactors] at hp hq hr
  have hcpq : p.Coprime q := (Nat.coprime_primes hp.1 hq.1).2 hpq
  have hpqn : p * q ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcpq hp.2.1 hq.2.1
  obtain ⟨k, hk⟩ := hpqn
  have hsq := hC.squarefree
  have hpk : p.Coprime k := by
    refine (Nat.Prime.coprime_iff_not_dvd hp.1).2 fun hdvd => ?_
    have : p * p ∣ n := by
      rw [hk]
      exact Nat.mul_dvd_mul (dvd_mul_right p q) hdvd
    exact hp.1.one_lt.ne' (Nat.isUnit_iff.1 (hsq p this))
  have hqk : q.Coprime k := by
    refine (Nat.Prime.coprime_iff_not_dvd hq.1).2 fun hdvd => ?_
    have : q * q ∣ n := by
      rw [hk]
      exact Nat.mul_dvd_mul (dvd_mul_left q p) hdvd
    exact hq.1.one_lt.ne' (Nat.isUnit_iff.1 (hsq q this))
  have hrk : r ∣ k := by
    have hrpq : r.Coprime (p * q) :=
      Nat.Coprime.mul_right ((Nat.coprime_primes hr.1 hp.1).2 (Ne.symm hpr))
        ((Nat.coprime_primes hr.1 hq.1).2 (Ne.symm hqr))
    exact hrpq.dvd_of_dvd_mul_left (hk ▸ hr.2.1)
  have hk0 : k ≠ 0 := by rintro rfl; rw [Nat.mul_zero] at hk; exact hn0 hk
  exact ⟨p, q, k, hp.1.one_lt, hq.1.one_lt,
    lt_of_lt_of_le hr.1.one_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hrk), hcpq, hpk, hqk,
    hk.symm⟩

private theorem castHom_pow_mul {n d m : ℕ} (hd : d ∣ n) (g h : (ZMod n)ˣ) :
    ZMod.castHom hd (ZMod d) (((g * h : (ZMod n)ˣ) : ZMod n) ^ m) =
      ZMod.castHom hd (ZMod d) ((g : ZMod n) ^ m) *
        ZMod.castHom hd (ZMod d) ((h : ZMod n) ^ m) := by
  rw [Units.val_mul, mul_pow, map_mul]

private theorem castHom_pow_inv {n d m : ℕ} (hd : d ∣ n) (g : (ZMod n)ˣ)
    (h : ZMod.castHom hd (ZMod d) ((g : ZMod n) ^ m) = 1) :
    ZMod.castHom hd (ZMod d) (((g⁻¹ : (ZMod n)ˣ) : ZMod n) ^ m) = 1 := by
  have := castHom_pow_mul (m := m) hd g g⁻¹
  rw [mul_inv_cancel, Units.val_one, one_pow, map_one, h, one_mul] at this
  exact this.symm

/-- **At most a quarter of the bases are non-witnesses for a Carmichael number.** Let $n$ be a
Carmichael number: $n > 2$, $n$ is not prime, and $b^{n-1} \equiv 1 \pmod n$ for every $b$
coprime to $n$. Then at most $(n - 1)/4$ of the bases $1, \dots, n - 1$ are non-witnesses for
$n$.

The proof splits $n$ into three pairwise coprime factors greater than $1$ and finds four distinct
cosets of a subgroup of $(\mathbb{Z}/n\mathbb{Z})^\times$ that holds the non-witnesses. -/
theorem card_nonwitnesses_le_quarter_of_carmichael {n : ℕ} (hC : n.IsCarmichael) :
    (nonwitnesses n).card ≤ (n - 1) / 4 := by
  have hn : 1 < n := by have := hC.two_lt; omega
  have hodd : n % 2 = 1 := Nat.odd_iff.1 hC.odd
  have : NeZero n := ⟨by omega⟩
  obtain ⟨m, v, hvc, hvm, -, hmem⟩ := exists_liar_subgroup hn hodd
  obtain ⟨n₁, n₂, n₃, h₁, h₂, h₃, h₁₂, h₁₃, h₂₃, hmul⟩ := exists_three_coprime_factors hC
  have hd₁ : n₁ ∣ n := ⟨n₂ * n₃, by rw [← hmul, Nat.mul_assoc]⟩
  have hd₂ : n₂ ∣ n := ⟨n₁ * n₃, by rw [← hmul]; ring⟩
  have hd₃ : n₃ ∣ n := ⟨n₁ * n₂, by rw [← hmul]; ring⟩
  have : Fact (2 < n₁) := ⟨by have := odd_of_dvd_odd hodd hd₁; omega⟩
  have : Fact (2 < n₂) := ⟨by have := odd_of_dvd_odd hodd hd₂; omega⟩
  have : Fact (2 < n₃) := ⟨by have := odd_of_dvd_odd hodd hd₃; omega⟩
  obtain ⟨w₁, hw₁c, hw₁, hw₁'⟩ :=
    exists_crt_unit (n₁ := n₁) (n₂ := n₂ * n₃) (Nat.Coprime.mul_right h₁₂ h₁₃)
      (by rw [← hmul, Nat.mul_assoc]) hvc
  obtain ⟨w₂, hw₂c, hw₂, hw₂'⟩ :=
    exists_crt_unit (n₁ := n₂) (n₂ := n₁ * n₃) (Nat.Coprime.mul_right h₁₂.symm h₂₃)
      (by rw [← hmul]; ring) hvc
  -- the components of `w₁` and `w₂` modulo `n₁`, `n₂`, `n₃`
  have hsub : ∀ {a b : ℕ} (x : ℕ), (x : ZMod (a * b)) = 1 →
      (x : ZMod a) = 1 ∧ (x : ZMod b) = 1 := by
    intro a b x hx
    constructor
    · have := congrArg (ZMod.castHom (dvd_mul_right a b) (ZMod a)) hx
      rwa [map_natCast, map_one] at this
    · have := congrArg (ZMod.castHom (dvd_mul_left b a) (ZMod b)) hx
      rwa [map_natCast, map_one] at this
  obtain ⟨hw₁₂, hw₁₃⟩ := hsub w₁ hw₁'
  obtain ⟨hw₂₁, hw₂₃⟩ := hsub w₂ hw₂'
  have hv : ∀ {d : ℕ} (hd : d ∣ n), (v : ZMod d) ^ m = -1 := by
    intro d hd
    have := congrArg (ZMod.castHom hd (ZMod d)) hvm
    rwa [map_pow, map_natCast, map_neg, map_one] at this
  set W₁ := ZMod.unitOfCoprime w₁ hw₁c
  set W₂ := ZMod.unitOfCoprime w₂ hw₂c
  have comp : ∀ {d : ℕ} (hd : d ∣ n) (x : ℕ) (hx : x.Coprime n),
      ZMod.castHom hd (ZMod d) (((ZMod.unitOfCoprime x hx : (ZMod n)ˣ) : ZMod n) ^ m) =
        (x : ZMod d) ^ m := by
    intro d hd x hx
    rw [map_pow, ZMod.coe_unitOfCoprime, map_natCast]
  have c₁₁ : ZMod.castHom hd₁ (ZMod n₁) ((W₁ : ZMod n) ^ m) = -1 := by rw [comp, hw₁, hv hd₁]
  have c₁₂ : ZMod.castHom hd₂ (ZMod n₂) ((W₁ : ZMod n) ^ m) = 1 := by rw [comp, hw₁₂, one_pow]
  have c₁₃ : ZMod.castHom hd₃ (ZMod n₃) ((W₁ : ZMod n) ^ m) = 1 := by rw [comp, hw₁₃, one_pow]
  have c₂₁ : ZMod.castHom hd₁ (ZMod n₁) ((W₂ : ZMod n) ^ m) = 1 := by rw [comp, hw₂₁, one_pow]
  have c₂₂ : ZMod.castHom hd₂ (ZMod n₂) ((W₂ : ZMod n) ^ m) = -1 := by rw [comp, hw₂, hv hd₂]
  have c₂₃ : ZMod.castHom hd₃ (ZMod n₃) ((W₂ : ZMod n) ^ m) = 1 := by rw [comp, hw₂₃, one_pow]
  have hidx : 4 ≤ (pmOnePowSubgroup n m).index := by
    refine four_le_index _ (not_mem_pmOnePowSubgroup hd₁ hd₂ W₁ c₁₁ c₁₂)
      (not_mem_pmOnePowSubgroup hd₂ hd₁ W₂ c₂₂ c₂₁)
      (not_mem_pmOnePowSubgroup hd₁ hd₃ _ (by rw [castHom_pow_mul, c₁₁, c₂₁, mul_one])
        (by rw [castHom_pow_mul, c₁₃, c₂₃, mul_one]))
      (not_mem_pmOnePowSubgroup hd₂ hd₃ _
        (by rw [castHom_pow_mul, castHom_pow_inv hd₂ W₁ c₁₂, c₂₂, one_mul])
        (by rw [castHom_pow_mul, castHom_pow_inv hd₃ W₁ c₁₃, c₂₃, one_mul]))
  refine card_le_of_mem_subgroup_index hn (by norm_num) _ hidx _ (fun a ha => ?_) hmem
  simp only [nonwitnesses, Finset.mem_filter, Finset.mem_Ioo] at ha
  exact ha.1

/-- Lifting the exponent: for an odd prime `p` and `x ≡ y (mod p)` with `p ∤ x`,
`x^(p^(k-1)) ≡ y^(p^(k-1)) (mod p^k)`. -/
private theorem pow_modEq_of_modEq {p k x y : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k)
    (hx : ¬ p ∣ x) (hxy : x ≡ y [MOD p]) : x ^ p ^ (k - 1) ≡ y ^ p ^ (k - 1) [MOD p ^ k] := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hy : ¬ p ∣ y := fun h => hx ((Nat.ModEq.dvd_iff hxy (dvd_refl p)).2 h)
  -- the larger of the two plays `x` in `padicValNat.pow_sub_pow`
  have key : ∀ a b : ℕ, b < a → ¬ p ∣ a → a ≡ b [MOD p] →
      b ^ p ^ (k - 1) ≡ a ^ p ^ (k - 1) [MOD p ^ k] := by
    intro a b hba ha hab
    have hdvd : p ∣ a - b := (Nat.modEq_iff_dvd' hba.le).1 hab.symm
    have hN : p ^ (k - 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hv := padicValNat.pow_sub_pow (p := p) hodd hba hdvd ha hN
    rw [padicValNat.prime_pow] at hv
    have h1 : 1 ≤ padicValNat p (a - b) := one_le_padicValNat_of_dvd (by omega) hdvd
    have hne : a ^ p ^ (k - 1) - b ^ p ^ (k - 1) ≠ 0 :=
      Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_left hba hN)
    refine (Nat.modEq_iff_dvd' (Nat.pow_le_pow_left hba.le _)).2 ?_
    exact (pow_dvd_pow p (by omega)).trans pow_padicValNat_dvd
  rcases lt_trichotomy x y with h | rfl | h
  · exact key y x h hy hxy.symm
  · rfl
  · exact (key x y h hx hxy).symm

/-- **At most a quarter of the bases are non-witnesses for an odd prime power.** Let $p$ be a prime
and $k \ge 2$ with $p^k$ odd. Then at most $(p^k - 1)/4$ of the bases $1, \dots, p^k - 1$ are
non-witnesses for $p^k$.

The proof shows that there are at most $p - 1$ non-witnesses: they satisfy
$a^{p^k - 1} \equiv 1 \pmod{p^k}$, and two of them that agree modulo $p$ agree modulo $p^k$. -/
theorem card_nonwitnesses_le_quarter_of_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k)
    (hodd : p ^ k % 2 = 1) : (nonwitnesses (p ^ k)).card ≤ (p ^ k - 1) / 4 := by
  set n := p ^ k with hn_def
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
    omega
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpn : p ∣ n := dvd_pow_self p (by omega)
  have hn : 1 < n := Nat.one_lt_pow (by omega) hp.one_lt
  have : NeZero n := ⟨by omega⟩
  -- non-witnesses are units with `a^(n-1) = 1`
  have hfermat : ∀ a ∈ nonwitnesses n, a.Coprime n ∧ a ^ (n - 1) % n = 1 ∧ 0 < a ∧ a < n := by
    intro a ha
    simp only [nonwitnesses, Finset.mem_filter, Finset.mem_Ioo] at ha
    obtain ⟨hf, hc⟩ := coprime_of_witness_eq_false hn ha.2
    exact ⟨hc, hf, ha.1⟩
  -- reduction modulo `p` is injective on them
  have hinj : Set.InjOn (fun a => a % p) (nonwitnesses n : Set ℕ) := by
    intro a ha b hb hab
    obtain ⟨hac, haf, ha0, han⟩ := hfermat a ha
    obtain ⟨hbc, hbf, hb0, hbn⟩ := hfermat b hb
    have hpa : ¬ p ∣ a :=
      (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.coprime_dvd_right hpn hac).symm
    have hmod : a ^ p ^ (k - 1) ≡ b ^ p ^ (k - 1) [MOD n] :=
      pow_modEq_of_modEq hp hp2 (by omega) hpa hab
    let A := ZMod.unitOfCoprime a hac
    let B := ZMod.unitOfCoprime b hbc
    have hAB : A = B := by
      have h1 : (A⁻¹ * B) ^ p ^ (k - 1) = 1 := by
        rw [mul_pow, inv_pow, inv_mul_eq_one]
        refine Units.ext ?_
        simp only [Units.val_pow_eq_pow_val, A, B, ZMod.coe_unitOfCoprime, ← Nat.cast_pow]
        exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod
      have h2 : (A⁻¹ * B) ^ (n - 1) = 1 := by
        rw [mul_pow, inv_pow, inv_mul_eq_one]
        refine Units.ext ?_
        simp only [Units.val_pow_eq_pow_val, A, B, ZMod.coe_unitOfCoprime, ← Nat.cast_pow]
        rw [(natCast_eq_one_iff hn).2 haf, (natCast_eq_one_iff hn).2 hbf]
      have hcop : Nat.gcd (p ^ (k - 1)) (n - 1) = 1 := by
        refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_)
        have : p ∣ n - (n - 1) := Nat.dvd_sub hpn h
        rw [show n - (n - 1) = 1 by omega] at this
        exact hp.one_lt.ne' (Nat.dvd_one.1 this)
      have := pow_gcd_eq_one.2 ⟨h1, h2⟩
      rw [hcop, pow_one, inv_mul_eq_one] at this
      exact this
    have := congrArg (fun u : (ZMod n)ˣ => (u : ZMod n)) hAB
    simp only [A, B, ZMod.coe_unitOfCoprime] at this
    have := (ZMod.natCast_eq_natCast_iff' a b n).1 this
    rwa [Nat.mod_eq_of_lt han, Nat.mod_eq_of_lt hbn] at this
  have hmaps : ∀ a ∈ nonwitnesses n, a % p ∈ Finset.Ioo 0 p := by
    intro a ha
    obtain ⟨hac, -, -, -⟩ := hfermat a ha
    have hpa : ¬ p ∣ a :=
      (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.Coprime.coprime_dvd_right hpn hac).symm
    simp only [Finset.mem_Ioo]
    exact ⟨Nat.pos_of_ne_zero fun h => hpa (Nat.dvd_of_mod_eq_zero h), Nat.mod_lt _ hp.pos⟩
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Nat.card_Ioo] at hcard
  -- `4 (p - 1) ≤ p^2 - 1 ≤ p^k - 1`
  have hpk : p ^ 2 ≤ n := Nat.pow_le_pow_right hp.pos hk
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have : (p - 1) * 4 + 1 ≤ p ^ 2 := by
    obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    nlinarith
  calc (nonwitnesses n).card * 4 ≤ (p - 1 - 0) * 4 := Nat.mul_le_mul_right _ hcard
    _ ≤ n - 1 := by omega

/-- **At most a quarter of the bases are non-witnesses.** Let $n > 1$ be odd and not prime. Then
at most $(n - 1)/4$ of the bases $1, \dots, n - 1$ are non-witnesses for $n$, so one uniformly
random base fails to expose $n$ as composite with probability at most $1/4$. -/
theorem card_nonwitnesses_le_quarter {n : ℕ} (hn : 1 < n) (hodd : n % 2 = 1) (hcomp : ¬ n.Prime) :
    (nonwitnesses n).card ≤ (n - 1) / 4 := by
  by_cases hpow : ∃ p e, p.Prime ∧ 2 ≤ e ∧ n = p ^ e
  · obtain ⟨p, e, hp, he, rfl⟩ := hpow
    exact card_nonwitnesses_le_quarter_of_prime_pow hp he hodd
  · push Not at hpow
    by_cases h : ∃ x, x.Coprime n ∧ x ^ (n - 1) % n ≠ 1
    · obtain ⟨x, hx, hfx⟩ := h
      exact card_nonwitnesses_le_quarter_of_pow_ne_one hn hodd hcomp hpow hx hfx
    · push Not at h
      exact card_nonwitnesses_le_quarter_of_carmichael (isCarmichael_of_forall hn hodd hcomp h)

/-- **Quarter error bound for Miller–Rabin with several bases.** Let $n > 1$ be odd and not
prime, and let $s$ be a natural number. Among the $(n - 1)^s$ lists $(b_1, \dots, b_s)$ of bases
with $0 < b_i < n$, at most $\lfloor (n - 1)/4 \rfloor^s$ make the Miller–Rabin test of $n$ with
bases $b_1, \dots, b_s$ answer *prime*.

With uniformly random bases the error probability is therefore at most $4^{-s}$. -/
theorem card_millerRabin_errors_le_quarter {n : ℕ} (hn : 1 < n) (hodd : n % 2 = 1)
    (hcomp : ¬ n.Prime) (s : ℕ) :
    ((Fintype.piFinset fun _ : Fin s => Finset.Ioo 0 n).filter
        fun b => (millerRabin n (List.ofFn b)).ret = true).card ≤ ((n - 1) / 4) ^ s := by
  rw [millerRabin_errors_eq, Fintype.card_piFinset_const]
  exact Nat.pow_le_pow_left (card_nonwitnesses_le_quarter hn hodd hcomp) s

end Cslib.Algorithms.Lean.MillerRabin
