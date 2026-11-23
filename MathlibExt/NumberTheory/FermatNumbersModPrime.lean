/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Fermat
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.RingTheory.ZMod.Torsion
import Mathlib.Tactic.NormNum.Prime
import MathlibExt.NumberTheory.FermatResiduePeriod

/-!
# Fermat numbers modulo a prime

Results from Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of
Integer Sequences 28 (2025), Article 25.8.7, on the residues of the Fermat
numbers `F_n = Nat.fermatNumber n = 2 ^ 2 ^ n + 1` modulo a prime `p`.

The paper's preperiod `h(p)` and period `k(p)` of `n ↦ F_n mod p` are not
defined as functions. As in `Nat.fermatNumber_mod_prime_exact_preperiod_period`
(`MathlibExt/NumberTheory/FermatResiduePeriod.lean`), they are encoded by
hypotheses on the tails `n ↦ (F (h + n) : ZMod p)`: the tail from `h` has
period `k`, no earlier tail has a positive period, and every positive period
of the tail from `h` is a multiple of `k`. The index `ind_g(a)` with respect
to a primitive root `g` is encoded by an exponent `i` with `g ^ i = a`.

The heavy lifting is `Nat.fermatNumber_mod_prime_exact_preperiod_period`
(Aigner's theorem): if `ord_p(2) = 2^v w` with `w` odd, then the exact
preperiod is `v` and the primitive period is `ord_w(2)`. Around it:

* Lemmas 2 and 4 follow from pigeonhole and the recurrence
  `F_{n+1} - 1 = (F_n - 1)^2` (`Nat.cast_fermatNumber_succ`).
* Lemma 6 and Proposition 18 move a period of a later tail down to an earlier
  periodic tail (`Function.Periodic.tail_of_periodic_tail_of_le`).
* Lemma 8 is `IsOfFinOrder.orderOf_pow`. Proposition 11 replaces a primitive
  root `h` by `h ^ c`, with `c` chosen by Lemma 10. Corollary 14 rests on
  Proposition 13 and on the uniqueness of the decomposition `2^s t` with `t`
  odd (`Nat.two_pow_mul_odd_inj`). Theorem 15 uses Proposition 13 to get
  `ord_p(2) = 2^(r-s) (u/t)` and then applies Aigner's theorem.
* Theorem 22 combines Euler's criterion (`ZMod.euler_criterion`) with the
  second supplement to quadratic reciprocity (`ZMod.exists_sq_eq_two_iff`).
* Theorem 23 uses the witnesses `73`, `281` and `41` (`ord_p(2) = 9, 70, 20`)
  for the preperiods `0, 1, 2`. For `v ≥ 3` it uses any prime factor `p` of
  `F_{v-1}`: Lemma 17 gives `ord_p(2) = 2^v`, so `8 ∣ p - 1`.

Several statements are more general than in the paper: every modulus in
Lemmas 2 and 4, every exponent `i` in Lemma 8 and Proposition 13, no
positivity of `α, β` in Lemma 10, and a free starting point `h` in
Proposition 18. Each docstring records how. Lemma 6 keeps the paper's
hypothesis that `p` is prime although its proof does not use it.

## Main results

* `fermatNumber_modEq_exists_repeat` (Lemma 2),
  `fermatNumber_modEq_add` and `fermatNumber_not_modEq_add_of_le` (Lemma 4),
  `fermatNumber_modEq_iff_preperiod_period` (Lemma 6).
* `gcd_card_sub_one_exponent_eq_div_orderOf` (Lemma 8 (iv)),
  `exists_coprime_modEq_of_coprime` (Lemma 10),
  `exists_primitiveRoot_pow_card_sub_one_div_orderOf` (Proposition 11),
  `exponent_dvd_card_sub_one_iff` (Proposition 13),
  `existsUnique_twoAdic_index_of_two` (Corollary 14).
* `fermatNumber_mod_prime_preperiod_period_of_index` (Theorem 15).
* `prime_dvd_fermatNumber_iff_orderOf_two` (Lemma 17),
  `exists_prime_dvd_fermatNumber_iff_period_eq_one` (Proposition 18).
* `orderOf_two_twoAdic_of_mod_eight` (Theorem 22),
  `exists_prime_one_mod_eight_fermat_preperiod` (Theorem 23).

## References

* Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer Sequences
  28 (2025), Article 25.8.7
  (<https://cs.uwaterloo.ca/journals/JIS/VOL28/Klaska/klaska22.html>).
-/

namespace MetaMathlibExt

@[expose] public section

/-! ### Tails of sequences and their periods -/

/-- Starting a tail later keeps its periods: if `n ↦ f (h + n)` has period `c`
and `h ≤ i`, then `n ↦ f (i + n)` has period `c`. -/
theorem Function.Periodic.tail_of_le {α : Type*} {f : ℕ → α} {h i c : ℕ}
    (hhi : h ≤ i) (hf : Function.Periodic (fun n => f (h + n)) c) :
    Function.Periodic (fun n => f (i + n)) c := by
  intro n
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hhi
  simpa only [add_assoc] using hf (d + n)

/-- Shifting a period down to an earlier periodic tail: if `n ↦ f (h + n)` has
a positive period `k` and `n ↦ f (i + n)` has period `t` for some `i ≥ h`, then
`t` is also a period of `n ↦ f (h + n)`. -/
theorem Function.Periodic.tail_of_periodic_tail_of_le {α : Type*} {f : ℕ → α}
    {h i k t : ℕ} (hhi : h ≤ i) (hk : 0 < k)
    (hfk : Function.Periodic (fun n => f (h + n)) k)
    (hft : Function.Periodic (fun n => f (i + n)) t) :
    Function.Periodic (fun n => f (h + n)) t := by
  intro n
  change f (h + (n + t)) = f (h + n)
  -- Both points are moved past `i` by the multiple `m` of `k`.
  set m := (i - h) * k
  have hkm : Function.Periodic (fun n => f (h + n)) m := by
    simpa only [Nat.cast_id] using hfk.nat_mul (i - h)
  have hm : i ≤ h + (n + m) := by
    have : i - h ≤ m := Nat.le_mul_of_pos_right _ hk
    omega
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hm
  calc f (h + (n + t)) = f (h + (n + t + m)) := (hkm (n + t)).symm
    _ = f (i + (j + t)) := by congr 1; omega
    _ = f (i + j) := hft j
    _ = f (h + (n + m)) := by rw [hj]
    _ = f (h + n) := hkm n

/-! ### Arithmetic helpers -/

/-- The recurrence `F_{n+1} = (F_n - 1)^2 + 1`, cast to any commutative
ring. -/
theorem Nat.cast_fermatNumber_succ {R : Type*} [CommRing R] (n : ℕ) :
    (Nat.fermatNumber (n + 1) : R) =
      ((Nat.fermatNumber n : R) - 1) ^ 2 + 1 := by
  simp only [Nat.fermatNumber, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_one]
  rw [add_sub_cancel_right, ← pow_mul, ← pow_succ]

/-- The decomposition `2 ^ s * a` with `a` odd is unique. -/
theorem Nat.two_pow_mul_odd_inj {s t a b : ℕ} (ha : Odd a) (hb : Odd b) :
    2 ^ s * a = 2 ^ t * b ↔ s = t ∧ a = b := by
  refine ⟨fun h => ?_, fun ⟨hst, hab⟩ => hst ▸ hab ▸ rfl⟩
  have hst : s = t := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := congrArg (padicValNat 2) h
    rwa [padicValNat.mul (pow_ne_zero _ two_ne_zero) ha.pos.ne',
      padicValNat.mul (pow_ne_zero _ two_ne_zero) hb.pos.ne',
      padicValNat.prime_pow, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd ha.not_two_dvd_nat,
      padicValNat.eq_zero_of_not_dvd hb.not_two_dvd_nat, add_zero,
      add_zero] at this
  subst hst
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by positivity) h⟩

/-- If `d ∣ q ^ (e + 1) * m` for a prime `q` but `q ^ (e + 1) ∤ d`, then
`d ∣ q ^ e * m`. -/
theorem Nat.dvd_pow_mul_of_dvd_pow_succ_mul {q d e m : ℕ} (hq : q.Prime)
    (hd : d ∣ q ^ (e + 1) * m) (h : ¬ q ^ (e + 1) ∣ d) : d ∣ q ^ e * m := by
  have hg : Nat.gcd d (q ^ (e + 1)) ∣ q ^ e := by
    obtain ⟨j, hj, hj'⟩ :=
      (Nat.dvd_prime_pow hq).mp (Nat.gcd_dvd_right d (q ^ (e + 1)))
    have hje : j ≠ e + 1 := by
      rintro rfl
      exact h (hj' ▸ Nat.gcd_dvd_left d _)
    rw [hj']
    exact Nat.pow_dvd_pow q (by omega)
  exact (Nat.dvd_gcd_mul_iff_dvd_mul.mpr hd).trans (Nat.mul_dvd_mul_right hg m)

/-- `2` is nonzero modulo an odd prime. -/
private theorem two_ne_zero_zmod {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')

/-- `2` has order `1` modulo `n` exactly when `n = 1`. -/
private theorem orderOf_two_zmod_eq_one_iff {n : ℕ} :
    orderOf (2 : ZMod n) = 1 ↔ n = 1 := by
  rw [orderOf_eq_one_iff, ← sub_eq_zero,
    show (2 : ZMod n) - 1 = ((1 : ℕ) : ZMod n) by norm_num,
    ZMod.natCast_eq_zero_iff, Nat.dvd_one]

/-- `2` has positive order modulo an odd number. -/
private theorem orderOf_two_zmod_pos {w : ℕ} (hw : Odd w) :
    0 < orderOf (2 : ZMod w) := by
  have : NeZero w := ⟨hw.pos.ne'⟩
  have h := (ZMod.isUnit_iff_coprime 2 w).mpr hw.coprime_two_left
  rw [Nat.cast_ofNat] at h
  exact h.isOfFinOrder.orderOf_pos

/-! ### Preperiod and period -/

/-- Among `F_0, …, F_p` two Fermat numbers are congruent modulo `p`; stated
for every positive modulus (pigeonhole), the paper takes `p` prime.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer
Sequences 28 (2025), Article 25.8.7, Lemma 2 (`jis-2025-25.8.7-lem-2`).
Proves `Wanted` entry `fermatNumber_modEq_exists_repeat`. -/
theorem fermatNumber_modEq_exists_repeat (p : ℕ) (hp : 0 < p) :
    ∃ i j, i < j ∧ j ≤ p ∧ Nat.fermatNumber i ≡ Nat.fermatNumber j [MOD p] := by
  have hmaps : Set.MapsTo (fun n => Nat.fermatNumber n % p)
      (Finset.range (p + 1)) (Finset.range p) := by
    intro n _
    exact Finset.mem_range.mpr (Nat.mod_lt _ hp)
  obtain ⟨x, hx, y, hy, hxy, he⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by simp) hmaps
  rw [Finset.mem_range] at hx hy
  rcases hxy.lt_or_gt with h | h
  · exact ⟨x, y, h, by omega, he⟩
  · exact ⟨y, x, h, by omega, he.symm⟩

/-- A congruence `F_i ≡ F_j (mod m)` propagates to
`F_{i+t} ≡ F_{j+t} (mod m)` for every `t`; stated for every modulus and all
`i, j` (the paper takes `p` prime and `i < j`).

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer
Sequences 28 (2025), Article 25.8.7, Lemma 4 (i) (`jis-2025-25.8.7-lem-4`).
Proves `Wanted` entry `fermatNumber_modEq_add`. -/
theorem fermatNumber_modEq_add (m i j : ℕ)
    (h : Nat.fermatNumber i ≡ Nat.fermatNumber j [MOD m]) (t : ℕ) :
    Nat.fermatNumber (i + t) ≡ Nat.fermatNumber (j + t) [MOD m] := by
  induction t with
  | zero => exact h
  | succ t ih =>
    rw [← ZMod.natCast_eq_natCast_iff] at ih ⊢
    rw [← add_assoc, ← add_assoc, Nat.cast_fermatNumber_succ,
      Nat.cast_fermatNumber_succ, ih]

/-- If `F_j ≢ F_{j+t} (mod m)` for every `t ≥ 1` and `i ≤ j`, then
`F_i ≢ F_{i+t} (mod m)` for every `t ≥ 1`; stated for every modulus and
`i ≤ j` (the paper takes `p` prime and `i < j`).

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer
Sequences 28 (2025), Article 25.8.7, Lemma 4 (ii) (`jis-2025-25.8.7-lem-4`).
Proves `Wanted` entry `fermatNumber_not_modEq_add_of_le`. -/
theorem fermatNumber_not_modEq_add_of_le (m i j : ℕ) (hij : i ≤ j)
    (h : ∀ t, 0 < t →
      ¬ Nat.fermatNumber j ≡ Nat.fermatNumber (j + t) [MOD m]) :
    ∀ t, 0 < t → ¬ Nat.fermatNumber i ≡ Nat.fermatNumber (i + t) [MOD m] := by
  intro t ht hi
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  have := fermatNumber_modEq_add m i (i + t) hi d
  rw [add_right_comm] at this
  exact h t ht this

set_option linter.unusedVariables false in
/-- Coincidences among Fermat residues: if `h` and `k` are the preperiod and
period of `n ↦ F_n mod p` (tail from `h` periodic with period `k`, no earlier
tail periodic, every period of the tail from `h` a multiple of `k`), then for
`i < j`, `F_i ≡ F_j (mod p)` if and only if `i ≥ h` and `i ≡ j (mod k)`.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer
Sequences 28 (2025), Article 25.8.7, Lemma 6 (`jis-2025-25.8.7-lem-6`).
Proves `Wanted` entry `fermatNumber_modEq_iff_preperiod_period`. -/
theorem fermatNumber_modEq_iff_preperiod_period (p : ℕ) (hp : p.Prime)
    (h k : ℕ) (hk : 0 < k)
    (hper : Function.Periodic
      (fun n : ℕ => (Nat.fermatNumber (h + n) : ZMod p)) k)
    (hpre : ∀ h' < h, ¬ ∃ kp : ℕ, 0 < kp ∧
      Function.Periodic
        (fun n : ℕ => (Nat.fermatNumber (h' + n) : ZMod p)) kp)
    (hmin : ∀ kp : ℕ, 0 < kp →
      Function.Periodic
        (fun n : ℕ => (Nat.fermatNumber (h + n) : ZMod p)) kp → k ∣ kp)
    (i j : ℕ) (hij : i < j) :
    Nat.fermatNumber i ≡ Nat.fermatNumber j [MOD p] ↔
      h ≤ i ∧ i ≡ j [MOD k] := by
  constructor
  · intro hF
    -- By Lemma 4 (i), the tail from `i` has period `j - i`.
    have hti : Function.Periodic
        (fun n : ℕ => (Nat.fermatNumber (i + n) : ZMod p)) (j - i) := by
      intro n
      have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr
        (fermatNumber_modEq_add p i j hF n)
      change (Nat.fermatNumber (i + (n + (j - i))) : ZMod p) =
        Nat.fermatNumber (i + n)
      rw [show i + (n + (j - i)) = j + n by omega, this]
    have hhi : h ≤ i :=
      not_lt.mp fun hlt => hpre i hlt ⟨j - i, by omega, hti⟩
    refine ⟨hhi, (Nat.modEq_iff_dvd' hij.le).mpr (hmin _ (by omega) ?_)⟩
    exact Function.Periodic.tail_of_periodic_tail_of_le
      (f := fun n => (Nat.fermatNumber n : ZMod p)) hhi hk hper hti
  · rintro ⟨hhi, hijk⟩
    obtain ⟨q, hq⟩ := (Nat.modEq_iff_dvd' hij.le).mp hijk
    have := hper.nat_mul q (i - h)
    simp only [Nat.cast_id] at this
    rw [show h + (i - h + q * k) = j by rw [mul_comm] at hq; omega,
      show h + (i - h) = i by omega] at this
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp this.symm

/-! ### Indices with respect to primitive roots -/

/-- If `g` is a primitive root modulo the prime `p` and `g ^ i = a`, then
`gcd(p - 1, i) = (p - 1) / ord_p(a)`; stated for every exponent `i` with
`g ^ i = a` (the paper's `ind_g(a) ∈ {1, …, p - 1}` is one of them).

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer
Sequences 28 (2025), Article 25.8.7, Lemma 8 (iv) (`jis-2025-25.8.7-lem-8`).
Proves `Wanted` entry `gcd_card_sub_one_exponent_eq_div_orderOf`. -/
theorem gcd_card_sub_one_exponent_eq_div_orderOf (p : ℕ) (hp : p.Prime)
    (g a : ZMod p) (hg : IsPrimitiveRoot g (p - 1)) (i : ℕ)
    (hi : g ^ i = a) :
    Nat.gcd (p - 1) i = (p - 1) / orderOf a := by
  have hp1 : p - 1 ≠ 0 := by have := hp.two_le; omega
  rw [← hi, IsOfFinOrder.orderOf_pow _ _ (hg.isOfFinOrder hp1),
    ← hg.eq_orderOf, Nat.div_div_self (Nat.gcd_dvd_left _ _) hp1]

/-- For coprime `α, β` and every positive `γ` there is a positive `c` coprime
to `γ` with `c ≡ β (mod α)`; positivity of `α, β` is not needed.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer
Sequences 28 (2025), Article 25.8.7, Lemma 10 (`jis-2025-25.8.7-lem-10`).
Proves `Wanted` entry `exists_coprime_modEq_of_coprime`. -/
theorem exists_coprime_modEq_of_coprime (α β γ : ℕ) (hγ : 0 < γ)
    (hαβ : Nat.Coprime α β) :
    ∃ c, 0 < c ∧ Nat.Coprime c γ ∧ c ≡ β [MOD α] := by
  classical
  -- `c = β + α P`, where `P` is the product of the primes of `γ` not
  -- dividing `β`.
  set P := ∏ q ∈ γ.primeFactors with ¬ q ∣ β, q
  have hP : 0 < P := Finset.prod_pos fun q hq =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).pos
  refine ⟨β + α * P, ?_, ?_, Nat.add_mul_mod_self_left β α P⟩
  · rcases Nat.eq_zero_or_pos β with rfl | hβ
    · rw [Nat.coprime_zero_right] at hαβ
      rw [hαβ, zero_add, one_mul]
      exact hP
    · exact Nat.add_pos_left hβ _
  · refine Nat.coprime_of_dvd fun q hq hqc hqγ => ?_
    by_cases hqβ : q ∣ β
    · have hqα : ¬ q ∣ α := fun hqα =>
        hq.coprime_iff_not_dvd.mp (hαβ.coprime_dvd_left hqα) hqβ
      have hqP : q ∣ P :=
        (hq.dvd_mul.mp ((Nat.dvd_add_right hqβ).mp hqc)).resolve_left hqα
      obtain ⟨r, hr, hqr⟩ := hq.prime.exists_mem_finset_dvd hqP
      rw [Finset.mem_filter] at hr
      rw [(Nat.prime_dvd_prime_iff_eq hq
        (Nat.prime_of_mem_primeFactors hr.1)).mp hqr] at hqβ
      exact hr.2 hqβ
    · have hqP : q ∣ P := Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr
        ⟨Nat.mem_primeFactors.mpr ⟨hq, hqγ, hγ.ne'⟩, hqβ⟩)
      exact hqβ ((Nat.dvd_add_left (dvd_mul_of_dvd_right hqP α)).mp hqc)

/-- For a prime `p` and a nonzero residue `a`, some primitive root `g` modulo
`p` satisfies `ind_g(a) = (p - 1) / ord_p(a)`, i.e.
`g ^ ((p - 1) / ord_p(a)) = a`.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer
Sequences 28 (2025), Article 25.8.7, Proposition 11
(`jis-2025-25.8.7-prop-11`).
Proves `Wanted` entry `exists_primitiveRoot_pow_card_sub_one_div_orderOf`. -/
theorem exists_primitiveRoot_pow_card_sub_one_div_orderOf (p : ℕ)
    (hp : p.Prime) (a : ZMod p) (ha : a ≠ 0) :
    ∃ g : ZMod p, IsPrimitiveRoot g (p - 1) ∧
      g ^ ((p - 1) / orderOf a) = a := by
  have := Fact.mk hp
  have hp1 : p - 1 ≠ 0 := by have := hp.two_le; omega
  have : NeZero (p - 1) := ⟨hp1⟩
  obtain ⟨h, hh⟩ :=
    HasEnoughRootsOfUnity.exists_isPrimitiveRoot (ZMod p) (p - 1)
  obtain ⟨j, -, hj⟩ := hh.eq_pow_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one ha)
  have hgcd := gcd_card_sub_one_exponent_eq_div_orderOf p hp h a hh j hj
  set e := (p - 1) / orderOf a
  have hde : orderOf a * e = p - 1 :=
    Nat.mul_div_cancel' (ZMod.orderOf_dvd_card_sub_one ha)
  have he : 0 < e := hgcd ▸ Nat.gcd_pos_of_pos_left j (Nat.pos_of_ne_zero hp1)
  -- Write `j = e j'`; then `j'` is coprime to `ord_p(a)`.
  obtain ⟨j', hj'⟩ : e ∣ j := hgcd ▸ Nat.gcd_dvd_right _ _
  have hcop : Nat.Coprime (orderOf a) j' := by
    have h1 : Nat.gcd (orderOf a * e) (e * j') = e := by rw [hde, ← hj', hgcd]
    rw [mul_comm (orderOf a) e, Nat.gcd_mul_left] at h1
    exact Nat.eq_of_mul_eq_mul_left he (h1.trans (mul_one e).symm)
  -- Lemma 10 gives `c` coprime to `p - 1` with `c ≡ j' (mod ord_p(a))`;
  -- take `g = h ^ c`.
  obtain ⟨c, -, hc, hcj⟩ := exists_coprime_modEq_of_coprime (orderOf a) j'
    (p - 1) (Nat.pos_of_ne_zero hp1) hcop
  refine ⟨h ^ c, hh.pow_of_coprime c hc, ?_⟩
  rw [← pow_mul, ← hj, hj', (hh.isOfFinOrder hp1).pow_eq_pow_iff_modEq,
    ← hh.eq_orderOf, ← hde, mul_comm e j']
  exact hcj.mul_right' e

/-- If `g` is a primitive root modulo the prime `p` and `g ^ i = a`, then
`i ∣ p - 1` if and only if `i = (p - 1) / ord_p(a)`; stated for every exponent
`i` with `g ^ i = a` (for `i` outside the paper's range `{1, …, p - 1}` both
sides are false).

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer
Sequences 28 (2025), Article 25.8.7, Proposition 13
(`jis-2025-25.8.7-prop-13`).
Proves `Wanted` entry `exponent_dvd_card_sub_one_iff`. -/
theorem exponent_dvd_card_sub_one_iff (p : ℕ) (hp : p.Prime)
    (g a : ZMod p) (hg : IsPrimitiveRoot g (p - 1)) (i : ℕ)
    (hi : g ^ i = a) :
    i ∣ p - 1 ↔ i = (p - 1) / orderOf a := by
  rw [← gcd_card_sub_one_exponent_eq_div_orderOf p hp g a hg i hi]
  refine ⟨fun h => (Nat.gcd_eq_right h).symm, fun h => ?_⟩
  rw [h]
  exact Nat.gcd_dvd_left _ _

/-- For an odd prime `p` with `p - 1 = 2^r u`, `u` odd, there is exactly one
pair `(s, t)` with `s ≤ r`, `t ∣ u` and `2^s t = ind_g(2)` for some primitive
root `g` modulo `p` (encoded as `g ^ (2^s t) = 2`; `1 ≤ 2^s t ≤ p - 1` holds
because `2^s t ∣ p - 1`).

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer
Sequences 28 (2025), Article 25.8.7, Corollary 14 (`jis-2025-25.8.7-cor-14`);
also Theorem 15 (i).
Proves `Wanted` entry `existsUnique_twoAdic_index_of_two`. -/
theorem existsUnique_twoAdic_index_of_two (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (r u : ℕ) (hu : Odd u) (hpu : p - 1 = 2 ^ r * u) :
    ∃! st : ℕ × ℕ, st.1 ≤ r ∧ st.2 ∣ u ∧
      ∃ g : ZMod p, IsPrimitiveRoot g (p - 1) ∧ g ^ (2 ^ st.1 * st.2) = 2 := by
  have := Fact.mk hp
  have h2 := two_ne_zero_zmod hp hp2
  obtain ⟨g, hg, hg2⟩ :=
    exists_primitiveRoot_pow_card_sub_one_div_orderOf p hp 2 h2
  -- The index `(p - 1) / ord_p(2)` divides `2^r u`, so it is `2^s t` with
  -- `s ≤ r` and `t ∣ u`.
  have hdvd : (p - 1) / orderOf (2 : ZMod p) ∣ 2 ^ r * u :=
    hpu ▸ Nat.div_dvd_of_dvd (ZMod.orderOf_dvd_card_sub_one h2)
  obtain ⟨a, t, ha, ht, hat⟩ := Nat.dvd_mul.mp hdvd
  obtain ⟨s, hs, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ha
  refine ⟨(s, t), ⟨hs, ht, g, hg, hat ▸ hg2⟩, ?_⟩
  -- By Proposition 13 every such pair gives the same index.
  rintro ⟨s', t'⟩ ⟨hs', ht', g', hg', hg2'⟩
  have e := (exponent_dvd_card_sub_one_iff p hp g' 2 hg' _ hg2').mp
    (hpu ▸ Nat.mul_dvd_mul (Nat.pow_dvd_pow 2 hs') ht')
  obtain ⟨rfl, rfl⟩ :=
    (Nat.two_pow_mul_odd_inj (hu.of_dvd_nat ht') (hu.of_dvd_nat ht)).mp
      (e.trans hat.symm)
  rfl

/-- Preperiod and period of Fermat residues from the index of `2`: for an odd
prime `p` with `p - 1 = 2^r u`, `u` odd, and `s ≤ r`, `t ∣ u` with
`g ^ (2^s t) = 2` for a primitive root `g`, the sequence `n ↦ F_n mod p` has
exact preperiod `r - s` and primitive period `ord_{u/t}(2)`.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer
Sequences 28 (2025), Article 25.8.7, Theorem 15 (ii) and (iii)
(`jis-2025-25.8.7-thm-15`).
Proves `Wanted` entry `fermatNumber_mod_prime_preperiod_period_of_index`. -/
theorem fermatNumber_mod_prime_preperiod_period_of_index (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (r u : ℕ) (hu : Odd u)
    (hpu : p - 1 = 2 ^ r * u) (s t : ℕ) (hs : s ≤ r) (ht : t ∣ u)
    (g : ZMod p) (hg : IsPrimitiveRoot g (p - 1))
    (hgi : g ^ (2 ^ s * t) = 2) :
    Function.Periodic
        (fun n : ℕ => (Nat.fermatNumber (r - s + n) : ZMod p))
        (orderOf (2 : ZMod (u / t))) ∧
      (∀ h < r - s, ¬ ∃ kp : ℕ, 0 < kp ∧
        Function.Periodic
          (fun n : ℕ => (Nat.fermatNumber (h + n) : ZMod p)) kp) ∧
      (∀ kp : ℕ, 0 < kp →
        Function.Periodic
          (fun n : ℕ => (Nat.fermatNumber (r - s + n) : ZMod p)) kp →
          orderOf (2 : ZMod (u / t)) ∣ kp) := by
  have := Fact.mk hp
  have hp1 : p - 1 ≠ 0 := by have := hp.two_le; omega
  obtain ⟨m, rfl⟩ := ht
  have ht0 : 0 < t := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hu
  -- By Proposition 13, `2^s t = (p - 1) / ord_p(2)`, so
  -- `ord_p(2) = 2^(r-s) m`.
  have hidx := (exponent_dvd_card_sub_one_iff p hp g 2 hg _ hgi).mp
    (hpu ▸ Nat.mul_dvd_mul (Nat.pow_dvd_pow 2 hs) (dvd_mul_right t m))
  have hord : orderOf (2 : ZMod p) = 2 ^ (r - s) * m := by
    rw [← Nat.div_div_self
        (ZMod.orderOf_dvd_card_sub_one (two_ne_zero_zmod hp hp2)) hp1,
      ← hidx, hpu, ← pow_sub_mul_pow 2 hs,
      show 2 ^ (r - s) * 2 ^ s * (t * m) = 2 ^ (r - s) * m * (2 ^ s * t) by
        ring,
      Nat.mul_div_cancel _ (by positivity)]
  rw [Nat.mul_div_cancel_left m ht0]
  exact Nat.fermatNumber_mod_prime_exact_preperiod_period p (r - s) m hp hp2
    hord (Nat.Odd.of_mul_right hu)

/-! ### Primes dividing Fermat numbers -/

/-- An odd prime `p` divides `F_n` if and only if `ord_p(2) = 2^{n+1}`.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer
Sequences 28 (2025), Article 25.8.7, Lemma 17 (`jis-2025-25.8.7-lem-17`).
Proves `Wanted` entry `prime_dvd_fermatNumber_iff_orderOf_two`. -/
theorem prime_dvd_fermatNumber_iff_orderOf_two (n p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) :
    p ∣ Nat.fermatNumber n ↔ orderOf (2 : ZMod p) = 2 ^ (n + 1) := by
  have := Fact.mk hp
  have : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
  rw [← ZMod.natCast_eq_zero_iff, Nat.fermatNumber, Nat.cast_add, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_one, ← eq_neg_iff_add_eq_zero]
  constructor
  · intro h
    apply orderOf_eq_prime_pow
    · rw [h]
      exact ZMod.neg_one_ne_one
    · rw [pow_succ, pow_mul, h, neg_one_sq]
  · intro h
    have hx : (2 : ZMod p) ^ 2 ^ n * 2 ^ 2 ^ n = 1 := by
      rw [← pow_add, ← two_mul, ← pow_succ', ← h, pow_orderOf_eq_one]
    rcases mul_self_eq_one_iff.mp hx with h1 | h1
    · have := Nat.le_of_dvd (by positivity) (h ▸ orderOf_dvd_of_pow_eq_one h1)
      exact absurd this
        (Nat.not_le.mpr (Nat.pow_lt_pow_right (by norm_num) n.lt_succ_self))
    · exact h1

/-- An odd prime `p` divides some Fermat number if and only if the primitive
period `k(p)` of `n ↦ F_n mod p` equals `1`. The paper's set `F` is the set of
primes dividing some `F_n` (`n ≥ 0`). `k` is the primitive period of the tail
from `h`: that tail is periodic with period `k > 0` and every positive period
of it is a multiple of `k`. The paper takes `h = h(p)`, the pre-period; the
primitive period is the same for every `h ≥ h(p)` and no tail from `h < h(p)`
is periodic, so `h` is left free.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer
Sequences 28 (2025), Article 25.8.7, Proposition 18
(`jis-2025-25.8.7-prop-18`).
Proves `Wanted` entry `exists_prime_dvd_fermatNumber_iff_period_eq_one`. -/
theorem exists_prime_dvd_fermatNumber_iff_period_eq_one (p : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (h k : ℕ) (hk : 0 < k)
    (hper : Function.Periodic
      (fun n : ℕ => (Nat.fermatNumber (h + n) : ZMod p)) k)
    (hmin : ∀ kp : ℕ, 0 < kp →
      Function.Periodic
        (fun n : ℕ => (Nat.fermatNumber (h + n) : ZMod p)) kp → k ∣ kp) :
    (∃ n : ℕ, p ∣ Nat.fermatNumber n) ↔ k = 1 := by
  have := Fact.mk hp
  have h2 := two_ne_zero_zmod hp hp2
  have hord0 : orderOf (2 : ZMod p) ≠ 0 :=
    (isUnit_iff_ne_zero.mpr h2).isOfFinOrder.orderOf_pos.ne'
  obtain ⟨v, w, hw, hord⟩ := Nat.exists_eq_two_pow_mul_odd hord0
  obtain ⟨hpv, hprev, hminv⟩ :=
    Nat.fermatNumber_mod_prime_exact_preperiod_period p v w hp hp2 hord hw
  -- The tail from `h` starts after the preperiod `v`, and `k = ord_w(2)`.
  have hvh : v ≤ h := not_lt.mp fun hlt => hprev h hlt ⟨k, hk, hper⟩
  have hK := orderOf_two_zmod_pos hw
  have hkK : k = orderOf (2 : ZMod w) := Nat.dvd_antisymm
    (hmin _ hK (Function.Periodic.tail_of_le
      (f := fun n => (Nat.fermatNumber n : ZMod p)) hvh hpv))
    (hminv _ hk (Function.Periodic.tail_of_periodic_tail_of_le
      (f := fun n => (Nat.fermatNumber n : ZMod p)) hvh hK hpv hper))
  rw [hkK, orderOf_two_zmod_eq_one_iff,
    exists_congr fun n => prime_dvd_fermatNumber_iff_orderOf_two n p hp hp2,
    hord]
  constructor
  · rintro ⟨n, hn⟩
    exact ((Nat.two_pow_mul_odd_inj hw odd_one).mp
      (hn.trans (mul_one _).symm)).2
  · rintro rfl
    -- `v ≠ 0`, since `ord_p(2) ≠ 1`.
    have hv : v ≠ 0 := by
      rintro rfl
      rw [pow_zero, mul_one, orderOf_two_zmod_eq_one_iff] at hord
      exact hp.one_lt.ne' hord
    exact ⟨v - 1, by rw [mul_one, Nat.sub_add_cancel (Nat.pos_of_ne_zero hv)]⟩

/-! ### The order of `2` and residues modulo `8` -/

/-- The `2`-part of `ord_p(2)` by residue class: if `p ≡ 7 (mod 8)` then
`ord_p(2)` is odd; if `p ≡ 3 (mod 8)` then `2 ∥ ord_p(2)`; if `p ≡ 5 (mod 8)`
then `4 ∥ ord_p(2)`.

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer
Sequences 28 (2025), Article 25.8.7, Theorem 22, order statements
(`jis-2025-25.8.7-thm-22`).
Proves `Wanted` entry `orderOf_two_twoAdic_of_mod_eight`. -/
theorem orderOf_two_twoAdic_of_mod_eight (p : ℕ) (hp : p.Prime) :
    (p % 8 = 7 → ¬ 2 ∣ orderOf (2 : ZMod p)) ∧
      (p % 8 = 3 →
        2 ∣ orderOf (2 : ZMod p) ∧ ¬ 4 ∣ orderOf (2 : ZMod p)) ∧
      (p % 8 = 5 →
        4 ∣ orderOf (2 : ZMod p) ∧ ¬ 8 ∣ orderOf (2 : ZMod p)) := by
  have := Fact.mk hp
  -- Euler's criterion and the second supplement:
  -- `2 ^ (p / 2) = 1` iff `p ≡ ±1 (mod 8)`.
  have key (hp2 : p ≠ 2) :
      (2 : ZMod p) ^ (p / 2) = 1 ↔ p % 8 = 1 ∨ p % 8 = 7 :=
    (ZMod.euler_criterion p (two_ne_zero_zmod hp hp2)).symm.trans
      (ZMod.exists_sq_eq_two_iff hp2)
  have hdvd (hp2 : p ≠ 2) : orderOf (2 : ZMod p) ∣ p - 1 :=
    ZMod.orderOf_dvd_card_sub_one (two_ne_zero_zmod hp hp2)
  refine ⟨fun h7 => ?_, fun h3 => ?_, fun h5 => ?_⟩
  · have hp2 : p ≠ 2 := by omega
    have hd := orderOf_dvd_of_pow_eq_one ((key hp2).mpr (Or.inr h7))
    intro h2d
    have := h2d.trans hd
    omega
  · have hp2 : p ≠ 2 := by omega
    have hne : ¬ (2 : ZMod p) ^ (p / 2) = 1 := fun h => by
      have := (key hp2).mp h
      omega
    refine ⟨by_contra fun hn => hne (orderOf_dvd_iff_pow_eq_one.mp ?_),
      fun h4 => ?_⟩
    · have := Nat.dvd_pow_mul_of_dvd_pow_succ_mul (d := orderOf (2 : ZMod p))
        (e := 0) (m := p / 2) Nat.prime_two
        (by rw [show 2 ^ (0 + 1) * (p / 2) = p - 1 by omega]; exact hdvd hp2)
        (by simpa using hn)
      simpa using this
    · have := h4.trans (hdvd hp2)
      omega
  · have hp2 : p ≠ 2 := by omega
    have hne : ¬ (2 : ZMod p) ^ (p / 2) = 1 := fun h => by
      have := (key hp2).mp h
      omega
    refine ⟨by_contra fun hn => hne (orderOf_dvd_iff_pow_eq_one.mp ?_),
      fun h8 => ?_⟩
    · have := Nat.dvd_pow_mul_of_dvd_pow_succ_mul (d := orderOf (2 : ZMod p))
        (e := 1) (m := p / 4) Nat.prime_two
        (by rw [show 2 ^ (1 + 1) * (p / 4) = p - 1 by omega]; exact hdvd hp2)
        (by simpa using hn)
      rwa [show 2 ^ 1 * (p / 4) = p / 2 by omega] at this
    · have := h8.trans (hdvd hp2)
      omega

/-- Every preperiod occurs among primes `p ≡ 1 (mod 8)`: for every `v` there
is such a prime for which `n ↦ F_n mod p` has exact preperiod `v` (the tail
from `v` has a positive period and no earlier tail does).

Source: Jiří Klaška, *Fermat Numbers Modulo a Prime*, Journal of Integer
Sequences 28 (2025), Article 25.8.7, Theorem 23 (`jis-2025-25.8.7-thm-23`).
Proves `Wanted` entry `exists_prime_one_mod_eight_fermat_preperiod`. -/
theorem exists_prime_one_mod_eight_fermat_preperiod (v : ℕ) :
    ∃ p : ℕ, p.Prime ∧ p % 8 = 1 ∧
      (∃ k : ℕ, 0 < k ∧
        Function.Periodic
          (fun n : ℕ => (Nat.fermatNumber (v + n) : ZMod p)) k) ∧
      ∀ h < v, ¬ ∃ kp : ℕ, 0 < kp ∧
        Function.Periodic
          (fun n : ℕ => (Nat.fermatNumber (h + n) : ZMod p)) kp := by
  -- It suffices to find such a prime with `ord_p(2) = 2^v w`, `w` odd.
  suffices H : ∃ p w : ℕ, p.Prime ∧ p % 8 = 1 ∧ Odd w ∧
      orderOf (2 : ZMod p) = 2 ^ v * w by
    obtain ⟨p, w, hp, hp8, hw, hord⟩ := H
    obtain ⟨hper, hpre, -⟩ := Nat.fermatNumber_mod_prime_exact_preperiod_period
      p v w hp (by omega) hord hw
    exact ⟨p, hp, hp8, ⟨_, orderOf_two_zmod_pos hw, hper⟩, hpre⟩
  match v with
  | 0 => exact ⟨73, 9, by norm_num, by norm_num, by decide,
      (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩⟩
  | 1 => exact ⟨281, 35, by norm_num, by norm_num, by decide,
      (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩⟩
  | 2 => exact ⟨41, 5, by norm_num, by norm_num, by decide,
      (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩⟩
  | v + 3 =>
    -- Any prime factor `p` of `F_{v+2}` has `ord_p(2) = 2^(v+3)`, hence
    -- `8 ∣ p - 1`.
    obtain ⟨p, hp, hpF⟩ :=
      Nat.exists_prime_and_dvd (Nat.fermatNumber_ne_one (v + 2))
    have := Fact.mk hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (Nat.odd_fermatNumber _).not_two_dvd_nat hpF
    have hord :=
      (prime_dvd_fermatNumber_iff_orderOf_two (v + 2) p hp hp2).mp hpF
    have h8 : 2 ^ 3 ∣ p - 1 := (Nat.pow_dvd_pow 2 (by omega)).trans
      (hord ▸ ZMod.orderOf_dvd_card_sub_one (two_ne_zero_zmod hp hp2))
    have := hp.pos
    exact ⟨p, 1, hp, by omega, odd_one, by rw [hord, mul_one]⟩

end

end MetaMathlibExt
