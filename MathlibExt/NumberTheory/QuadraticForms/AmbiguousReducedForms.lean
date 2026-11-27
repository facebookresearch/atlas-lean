/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.QuadraticForms.Reduced
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Reduced forms of the ambiguous classes of a negative discriminant

Gauss and Oesterlé count the ambiguous classes of primitive positive definite binary quadratic
forms of discriminant $-d$ through their reduced forms, which are the primitive Gauss-reduced
forms $(a, b, c)$ of discriminant $-d$ with $b = 0$, $b = a$ or $a = c$. This file counts these
forms, following Oesterlé, *Le problème de Gauss sur le nombre de classes* (L'Enseignement
Mathématique 34 (1988)), §4, formula (9), and Gauss, *Disquisitiones Arithmeticae*,
arts. 257–259.

A form with $b = 0$ gives the factorization $d / 4 = a c$ into coprime factors $a \le c$. A form
with $b \ne 0$ gives the factorization $d = x y$ with $x = a$ and $y = 4c - a$ when $b = a$, and
with $x = 2a - b$ and $y = 2a + b$ when $a = c$; these are exactly the factorizations with
$x < y$, $4 \mid x + y$ and $\gcd(x, (x + y)/4) = 1$. Both kinds are counted through the subsets
of the prime factors, according to the residue of $d$ modulo $32$.
-/

@[expose] public section

namespace BinaryQuadraticForm

/-! ### Coprime factorizations -/

private lemma prod_ne_zero_of_subset (m : ℕ) {S : Finset ℕ} (hS : S ⊆ m.primeFactors) :
    ∏ p ∈ S, p ^ m.factorization p ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hp =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (hS hp)).ne_zero

private lemma primeFactors_prod_pow (m : ℕ) (S : Finset ℕ) (hS : S ⊆ m.primeFactors) :
    (∏ p ∈ S, p ^ m.factorization p).primeFactors = S := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨has, hs⟩ := Finset.insert_subset_iff.mp hS
    have hpa := Nat.prime_of_mem_primeFactors has
    have hfa : m.factorization a ≠ 0 := by
      rw [← Finsupp.mem_support_iff, Nat.support_factorization]
      exact has
    rw [Finset.prod_insert ha, Nat.primeFactors_mul (pow_ne_zero _ hpa.ne_zero)
      (prod_ne_zero_of_subset m hs), Nat.primeFactors_prime_pow hfa hpa, ih hs,
      Finset.insert_eq]

private lemma prod_mul_prod_sdiff (m : ℕ) (hm : m ≠ 0) {S : Finset ℕ}
    (hS : S ⊆ m.primeFactors) :
    (∏ p ∈ S, p ^ m.factorization p) * ∏ p ∈ m.primeFactors \ S, p ^ m.factorization p =
      m := by
  rw [mul_comm, Finset.prod_sdiff hS]
  exact Nat.prod_factorization_pow_eq_self hm

private lemma prod_pow_of_coprime {x y : ℕ} (hxy : Nat.Coprime x y) (hx : x ≠ 0)
    (hy : y ≠ 0) : ∏ p ∈ x.primeFactors, p ^ (x * y).factorization p = x := by
  rw [Nat.factorization_mul hx hy]
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hx]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpy : p ∉ y.primeFactors := Finset.disjoint_left.mp hxy.disjoint_primeFactors hp
  rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hpy
  simp [hpy]

private lemma card_coprime_antidiagonal (m : ℕ) (hm : m ≠ 0) :
    ((Nat.divisorsAntidiagonal m).filter (fun p => Nat.Coprime p.1 p.2)).card =
      2 ^ m.primeFactors.card := by
  rw [← Finset.card_powerset]
  refine Finset.card_nbij' (fun p => p.1.primeFactors)
    (fun S => (∏ p ∈ S, p ^ m.factorization p,
      ∏ p ∈ m.primeFactors \ S, p ^ m.factorization p)) ?_ ?_ ?_ ?_
  · rintro ⟨x, y⟩ h
    simp only [Finset.coe_filter, Nat.mem_divisorsAntidiagonal, Set.mem_ofPred_eq] at h
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
    exact Nat.primeFactors_mono (Dvd.intro y h.1.1) hm
  · intro S hS
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
      Finset.coe_subset] at hS
    simp only [Finset.coe_filter, Nat.mem_divisorsAntidiagonal, Set.mem_ofPred_eq]
    refine ⟨⟨prod_mul_prod_sdiff m hm hS, hm⟩, ?_⟩
    rw [← Nat.disjoint_primeFactors (prod_ne_zero_of_subset m hS)
      (prod_ne_zero_of_subset m Finset.sdiff_subset), primeFactors_prod_pow m S hS,
      primeFactors_prod_pow m _ Finset.sdiff_subset]
    exact Finset.disjoint_sdiff
  · rintro ⟨x, y⟩ h
    simp only [Finset.coe_filter, Nat.mem_divisorsAntidiagonal, Set.mem_ofPred_eq] at h
    obtain ⟨⟨hxy, -⟩, hco⟩ := h
    have hx : x ≠ 0 := by rintro rfl; simp at hxy; exact hm hxy.symm
    have hy : y ≠ 0 := by rintro rfl; simp at hxy; exact hm hxy.symm
    have h1 : ∏ p ∈ x.primeFactors, p ^ m.factorization p = x := by
      rw [← hxy]
      exact prod_pow_of_coprime hco hx hy
    have h2 := prod_mul_prod_sdiff m hm (Nat.primeFactors_mono (Dvd.intro y hxy) hm)
    rw [h1, ← hxy] at h2
    simp only [h1, Prod.mk.injEq, true_and]
    rw [← hxy]
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hx) h2
  · intro S hS
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
      Finset.coe_subset] at hS
    exact primeFactors_prod_pow m S hS

private lemma card_coprime_antidiagonal_lt (m : ℕ) (hm : 1 < m) :
    ((Nat.divisorsAntidiagonal m).filter (fun p => Nat.Coprime p.1 p.2 ∧ p.1 < p.2)).card =
      2 ^ (m.primeFactors.card - 1) := by
  have hall := card_coprime_antidiagonal m (by omega)
  have hsplit := Finset.card_filter_add_card_filter_not (s :=
    (Nat.divisorsAntidiagonal m).filter (fun p => Nat.Coprime p.1 p.2)) (fun p => p.1 < p.2)
  rw [Finset.filter_filter, Finset.filter_filter, hall] at hsplit
  have hswap : ((Nat.divisorsAntidiagonal m).filter
      (fun p => Nat.Coprime p.1 p.2 ∧ p.1 < p.2)).card =
      ((Nat.divisorsAntidiagonal m).filter
      (fun p => Nat.Coprime p.1 p.2 ∧ ¬ p.1 < p.2)).card := by
    refine Finset.card_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_
    · rintro ⟨x, y⟩ h
      simp only [Finset.coe_filter, Nat.mem_divisorsAntidiagonal, Set.mem_ofPred_eq,
        Prod.swap_prod_mk] at h ⊢
      exact ⟨⟨by rw [mul_comm]; exact h.1.1, h.1.2⟩, h.2.1.symm, by omega⟩
    · rintro ⟨x, y⟩ h
      simp only [Finset.coe_filter, Nat.mem_divisorsAntidiagonal, Set.mem_ofPred_eq,
        Prod.swap_prod_mk] at h ⊢
      refine ⟨⟨by rw [mul_comm]; exact h.1.1, h.1.2⟩, h.2.1.symm, ?_⟩
      rcases lt_or_eq_of_le (not_lt.mp h.2.2) with hlt | heq
      · exact hlt
      · subst heq
        have h1 : y = 1 := by simpa using h.2.1
        subst h1
        omega
    · intro p _
      exact Prod.swap_swap p
    · intro p _
      exact Prod.swap_swap p
  have hne : m.primeFactors.card ≠ 0 :=
    Finset.card_ne_zero.mpr (Nat.nonempty_primeFactors.mpr hm)
  have hpow : 2 ^ m.primeFactors.card = 2 * 2 ^ (m.primeFactors.card - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

private lemma card_coprime_antidiagonal_le (m : ℕ) (hm : 1 < m) :
    ((Nat.divisorsAntidiagonal m).filter (fun p => Nat.Coprime p.1 p.2 ∧ p.1 ≤ p.2)).card =
      2 ^ (m.primeFactors.card - 1) := by
  rw [← card_coprime_antidiagonal_lt m hm]
  congr 1
  refine Finset.filter_congr fun p hp => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hp
  refine ⟨fun h => ⟨h.1, lt_of_le_of_ne h.2 fun heq => ?_⟩, fun h => ⟨h.1, h.2.le⟩⟩
  obtain ⟨x, y⟩ := p
  simp only at heq h hp
  subst heq
  have h1 : x = 1 := by simpa using h.1
  subst h1
  omega

private lemma card_coprime_antidiagonal_le_one :
    ((Nat.divisorsAntidiagonal 1).filter (fun p => Nat.Coprime p.1 p.2 ∧ p.1 ≤ p.2)).card = 1 := by
  rw [Nat.divisorsAntidiagonal_one]
  rfl

private lemma card_coprime_antidiagonal_lt_one :
    ((Nat.divisorsAntidiagonal 1).filter (fun p => Nat.Coprime p.1 p.2 ∧ p.1 < p.2)).card = 0 := by
  rw [Nat.divisorsAntidiagonal_one]
  rfl

/-! ### Factorizations by residue class -/

private lemma coprime_four_of_mod_two_eq_one {x : ℕ} (hx : x % 2 = 1) : Nat.Coprime 4 x := by
  have h2 : Nat.Coprime 2 x := Nat.coprime_two_left.2 (Nat.odd_iff.2 hx)
  simpa using h2.pow_left 2

private lemma mod_two_eq_one_of_coprime {x t : ℕ} (hx : x % 2 = 0) (h : Nat.Coprime x t) :
    t % 2 = 1 := by
  by_contra ht
  have := Nat.eq_one_of_dvd_coprimes h (Nat.dvd_of_mod_eq_zero hx)
    (Nat.dvd_of_mod_eq_zero (by omega))
  omega

private lemma mod_two_of_mul_mod_two_eq_one {a b : ℕ} (h : a * b % 2 = 1) :
    a % 2 = 1 ∧ b % 2 = 1 := by
  have h' := Nat.mul_mod a b 2
  rcases Nat.mod_two_eq_zero_or_one a with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one b with h2 | h2 <;> rw [h1, h2] at h' <;> omega

private lemma mul_mod_two_eq_zero_of_add {a b : ℕ} (h : (a + b) % 2 = 1) : a * b % 2 = 0 := by
  have h' := Nat.mul_mod a b 2
  rcases Nat.mod_two_eq_zero_or_one a with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one b with h2 | h2 <;> rw [h1, h2] at h' <;> omega

private lemma mod_two_eq_zero_of_mul_of_add {a b : ℕ} (hs : (a + b) % 2 = 0)
    (hm : a * b % 2 = 0) : a % 2 = 0 ∧ b % 2 = 0 := by
  have h' := Nat.mul_mod a b 2
  rcases Nat.mod_two_eq_zero_or_one a with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one b with h2 | h2 <;> rw [h1, h2] at h' <;> omega

private lemma add_mod_two_of_coprime {a b : ℕ} (hc : Nat.Coprime a b) (hm : a * b % 2 = 0) :
    (a + b) % 2 = 1 := by
  have h' := Nat.mul_mod a b 2
  rcases Nat.mod_two_eq_zero_or_one a with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one b with h2 | h2
  · have := Nat.eq_one_of_dvd_coprimes hc (Nat.dvd_of_mod_eq_zero h1)
      (Nat.dvd_of_mod_eq_zero h2)
    omega
  all_goals rw [h1, h2] at h'; omega

private lemma mul_mod_four_eq_one_iff {a b : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1) :
    a * b % 4 = 1 ↔ a % 4 = b % 4 := by
  have h := Nat.mul_mod a b 4
  rcases (by omega : a % 4 = 1 ∨ a % 4 = 3) with h1 | h1 <;>
    rcases (by omega : b % 4 = 1 ∨ b % 4 = 3) with h2 | h2 <;> rw [h1, h2] at h <;> omega

/-- Shape of an element of the factorization set of `4 * n`. -/
private lemma ambF_four_mul_struct {n x y : ℕ} (hxy : x * y = 4 * n) (h4 : 4 ∣ x + y)
    (hc : Nat.Coprime x ((x + y) / 4)) :
    ∃ a b, x = 2 * a ∧ y = 2 * b ∧ (a + b) % 4 = 2 ∧ a * b = n ∧
      Nat.Coprime (2 * a) ((a + b) / 2) := by
  have hx : x % 2 = 0 := by
    by_contra hx
    have : 4 ∣ y := (coprime_four_of_mod_two_eq_one (by omega)).dvd_of_dvd_mul_left ⟨n, hxy⟩
    omega
  have hy : y % 2 = 0 := by
    by_contra hy
    have : 4 ∣ x := (coprime_four_of_mod_two_eq_one (by omega)).dvd_of_dvd_mul_right ⟨n, hxy⟩
    omega
  have ht := mod_two_eq_one_of_coprime hx hc
  obtain ⟨a, rfl⟩ : ∃ a, x = 2 * a := ⟨x / 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, y = 2 * b := ⟨y / 2, by omega⟩
  refine ⟨a, b, rfl, rfl, by omega, ?_, ?_⟩
  · have : 4 * (a * b) = 4 * n := by rw [← hxy]; ring
    omega
  · have : (2 * a + 2 * b) / 4 = (a + b) / 2 := by omega
    rwa [this] at hc

private lemma ambF_four_mul_struct_even {n x y : ℕ} (hn : n % 2 = 0) (hxy : x * y = 4 * n)
    (h4 : 4 ∣ x + y) (hc : Nat.Coprime x ((x + y) / 4)) :
    ∃ c e, x = 4 * c ∧ y = 4 * e ∧ (c + e) % 2 = 1 ∧ n = 4 * (c * e) ∧ Nat.Coprime c e := by
  obtain ⟨a, b, rfl, rfl, hs, hab, hc⟩ := ambF_four_mul_struct hxy h4 hc
  have hev := mod_two_eq_zero_of_mul_of_add (a := a) (b := b) (by omega) (by omega)
  obtain ⟨c, rfl⟩ : ∃ c, a = 2 * c := ⟨a / 2, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, b = 2 * e := ⟨b / 2, by omega⟩
  refine ⟨c, e, by ring, by ring, by omega, by rw [← hab]; ring, ?_⟩
  have h1 : (2 * c + 2 * e) / 2 = c + e := by omega
  rw [h1] at hc
  exact Nat.coprime_self_add_right.1 (Nat.Coprime.coprime_dvd_left ⟨4, by ring⟩ hc)

private lemma ambF_of_mod_four_eq_three (d : ℕ) (hd : d % 4 = 3) :
    ((Nat.divisorsAntidiagonal d).filter
      (fun p => p.1 < p.2 ∧ 4 ∣ p.1 + p.2 ∧ Nat.Coprime p.1 ((p.1 + p.2) / 4))) =
    (Nat.divisorsAntidiagonal d).filter (fun p => Nat.Coprime p.1 p.2 ∧ p.1 < p.2) := by
  refine Finset.filter_congr (fun p hp => ?_)
  obtain ⟨x, y⟩ := p
  simp only [Nat.mem_divisorsAntidiagonal] at hp
  obtain ⟨hxy, -⟩ := hp
  dsimp only
  have hodd := mod_two_of_mul_mod_two_eq_one (a := x) (b := y) (by omega)
  have hne : x % 4 ≠ y % 4 := fun h => by
    have := (mul_mod_four_eq_one_iff hodd.1 hodd.2).2 h
    omega
  obtain ⟨s, hs⟩ : 4 ∣ x + y := by omega
  have hdiv : (x + y) / 4 = s := by omega
  rw [hdiv]
  have key : Nat.Coprime x y ↔ Nat.Coprime x s := by
    rw [← Nat.coprime_add_self_right, add_comm, hs, Nat.coprime_mul_iff_right]
    exact ⟨fun h => h.2, fun h => ⟨(coprime_four_of_mod_two_eq_one hodd.1).symm, h⟩⟩
  exact ⟨fun h => ⟨key.2 h.2.2, h.1⟩, fun h => ⟨h.2, ⟨s, hs⟩, key.1 h.1⟩⟩

private lemma card_ambF_four_mul_of_mod_four_eq_one (n : ℕ) (hn : n % 4 = 1) :
    ((Nat.divisorsAntidiagonal (4 * n)).filter
      (fun p => p.1 < p.2 ∧ 4 ∣ p.1 + p.2 ∧ Nat.Coprime p.1 ((p.1 + p.2) / 4))).card =
    ((Nat.divisorsAntidiagonal n).filter (fun p => Nat.Coprime p.1 p.2 ∧ p.1 < p.2)).card := by
  refine Finset.card_nbij' (fun p => (p.1 / 2, p.2 / 2)) (fun p => (2 * p.1, 2 * p.2))
    ?_ ?_ ?_ ?_
  · rintro ⟨x, y⟩ hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_divisorsAntidiagonal] at hp ⊢
    obtain ⟨⟨hxy, -⟩, hlt, h4, hc⟩ := hp
    obtain ⟨a, b, rfl, rfl, hs, hab, hc⟩ := ambF_four_mul_struct hxy h4 hc
    have e1 : 2 * a / 2 = a := by omega
    have e2 : 2 * b / 2 = b := by omega
    rw [e1, e2]
    have hodd := mod_two_of_mul_mod_two_eq_one (a := a) (b := b) (by omega)
    refine ⟨⟨hab, by omega⟩, ?_, by omega⟩
    have hat : Nat.Coprime a ((a + b) / 2) := Nat.Coprime.coprime_dvd_left ⟨2, by ring⟩ hc
    have ha2 : Nat.Coprime a 2 := (Nat.coprime_two_left.2 (Nat.odd_iff.2 hodd.1)).symm
    have h2 : Nat.Coprime a (2 * ((a + b) / 2)) := Nat.coprime_mul_iff_right.2 ⟨ha2, hat⟩
    have e3 : 2 * ((a + b) / 2) = a + b := by omega
    rw [e3] at h2
    exact Nat.coprime_self_add_right.1 h2
  · rintro ⟨a, b⟩ hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_divisorsAntidiagonal] at hp ⊢
    obtain ⟨⟨hab, -⟩, hc, hlt⟩ := hp
    have hodd := mod_two_of_mul_mod_two_eq_one (a := a) (b := b) (by omega)
    have hmod := (mul_mod_four_eq_one_iff hodd.1 hodd.2).1 (by omega)
    have e1 : (2 * a + 2 * b) / 4 = (a + b) / 2 := by omega
    rw [e1]
    refine ⟨⟨by rw [← hab]; ring, by omega⟩, by omega, by omega, ?_⟩
    rw [Nat.coprime_mul_iff_left]
    refine ⟨Nat.coprime_two_left.2 (Nat.odd_iff.2 (by omega)), ?_⟩
    have h2 : Nat.Coprime a (a + b) := Nat.coprime_self_add_right.2 hc
    exact Nat.Coprime.coprime_dvd_right ⟨2, by omega⟩ h2
  · rintro ⟨x, y⟩ hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_divisorsAntidiagonal] at hp
    obtain ⟨⟨hxy, -⟩, -, h4, hc⟩ := hp
    obtain ⟨a, b, rfl, rfl, -⟩ := ambF_four_mul_struct hxy h4 hc
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨a, b⟩ -
    simp only [Prod.mk.injEq]
    omega

private lemma ambF_four_mul_eq_empty (n : ℕ) (hn : n % 4 = 3 ∨ n % 4 = 2 ∨ n % 8 = 4) :
    ((Nat.divisorsAntidiagonal (4 * n)).filter
      (fun p => p.1 < p.2 ∧ 4 ∣ p.1 + p.2 ∧ Nat.Coprime p.1 ((p.1 + p.2) / 4))) = ∅ := by
  ext ⟨x, y⟩
  simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal, Finset.notMem_empty, iff_false]
  rintro ⟨⟨hxy, -⟩, -, h4, hc⟩
  rcases hn with hn | hn
  · obtain ⟨a, b, -, -, hs, hab, -⟩ := ambF_four_mul_struct hxy h4 hc
    have hodd := mod_two_of_mul_mod_two_eq_one (a := a) (b := b) (by omega)
    have := (mul_mod_four_eq_one_iff hodd.1 hodd.2).2 (by omega)
    omega
  · obtain ⟨c, e, -, -, hs, hce, -⟩ := ambF_four_mul_struct_even (by omega) hxy h4 hc
    have := mul_mod_two_eq_zero_of_add hs
    omega

private lemma card_ambF_four_mul_of_eight_dvd (n : ℕ) (hn : 8 ∣ n) :
    ((Nat.divisorsAntidiagonal (4 * n)).filter
      (fun p => p.1 < p.2 ∧ 4 ∣ p.1 + p.2 ∧ Nat.Coprime p.1 ((p.1 + p.2) / 4))).card =
    ((Nat.divisorsAntidiagonal (n / 4)).filter
      (fun p => Nat.Coprime p.1 p.2 ∧ p.1 < p.2)).card := by
  refine Finset.card_nbij' (fun p => (p.1 / 4, p.2 / 4)) (fun p => (4 * p.1, 4 * p.2))
    ?_ ?_ ?_ ?_
  · rintro ⟨x, y⟩ hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_divisorsAntidiagonal] at hp ⊢
    obtain ⟨⟨hxy, hn0⟩, hlt, h4, hc⟩ := hp
    obtain ⟨c, e, rfl, rfl, -, hce, hc⟩ := ambF_four_mul_struct_even (by omega) hxy h4 hc
    have e1 : 4 * c / 4 = c := by omega
    have e2 : 4 * e / 4 = e := by omega
    rw [e1, e2]
    exact ⟨⟨by omega, by omega⟩, hc, by omega⟩
  · rintro ⟨a, b⟩ hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_divisorsAntidiagonal] at hp ⊢
    obtain ⟨⟨hab, hn0⟩, hc, hlt⟩ := hp
    have hn4 : n = 4 * (a * b) := by omega
    have e1 : (4 * a + 4 * b) / 4 = a + b := by omega
    rw [e1]
    refine ⟨⟨by rw [hn4]; ring, by omega⟩, by omega, by omega, ?_⟩
    rw [Nat.coprime_mul_iff_left]
    exact ⟨coprime_four_of_mod_two_eq_one (add_mod_two_of_coprime hc (by omega)),
      Nat.coprime_self_add_right.2 hc⟩
  · rintro ⟨x, y⟩ hp
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_divisorsAntidiagonal] at hp
    obtain ⟨⟨hxy, -⟩, -, h4, hc⟩ := hp
    obtain ⟨c, e, rfl, rfl, -⟩ := ambF_four_mul_struct_even (by omega) hxy h4 hc
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨a, b⟩ -
    simp only [Prod.mk.injEq]
    omega

/-! ### Number of prime factors -/

private lemma card_primeFactors_four_mul_of_odd (n : ℕ) (hn : n % 2 = 1) :
    (4 * n).primeFactors.card = n.primeFactors.card + 1 := by
  have hn0 : n ≠ 0 := by omega
  have h2 : 2 ∉ n.primeFactors := fun h => by
    have := Nat.dvd_of_mem_primeFactors h
    omega
  rw [Nat.primeFactors_mul (by norm_num) hn0, show (4 : ℕ) = 2 ^ 2 by norm_num,
    Nat.primeFactors_pow _ (by norm_num), Nat.Prime.primeFactors Nat.prime_two,
    Finset.card_union_of_disjoint (Finset.disjoint_singleton_left.mpr h2),
    Finset.card_singleton, add_comm]

private lemma card_primeFactors_four_mul_of_even (n : ℕ) (hn0 : n ≠ 0) (hn : n % 2 = 0) :
    (4 * n).primeFactors.card = n.primeFactors.card := by
  have h2 : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, Nat.dvd_of_mod_eq_zero hn, hn0⟩
  rw [Nat.primeFactors_mul (by norm_num) hn0, show (4 : ℕ) = 2 ^ 2 by norm_num,
    Nat.primeFactors_pow _ (by norm_num), Nat.Prime.primeFactors Nat.prime_two,
    Finset.singleton_union, Finset.insert_eq_of_mem h2]

/-! ### From ambiguous reduced forms to factorizations -/

private def ambE (d : ℕ) : Finset (ℕ × ℕ) :=
  (Nat.divisorsAntidiagonal (d / 4)).filter (fun p => Nat.Coprime p.1 p.2 ∧ p.1 ≤ p.2)

private def ambF (d : ℕ) : Finset (ℕ × ℕ) :=
  (Nat.divisorsAntidiagonal d).filter
    (fun p => p.1 < p.2 ∧ 4 ∣ p.1 + p.2 ∧ Nat.Coprime p.1 ((p.1 + p.2) / 4))

private def ambGE (p : ℕ × ℕ) : ℤ × ℤ × ℤ := ((p.1 : ℤ), 0, (p.2 : ℤ))

private def ambGF (p : ℕ × ℕ) : ℤ × ℤ × ℤ :=
  if 3 * p.1 ≤ p.2 then ((p.1 : ℤ), (p.1 : ℤ), (((p.1 + p.2) / 4 : ℕ) : ℤ))
  else ((((p.1 + p.2) / 4 : ℕ) : ℤ), (((p.2 - p.1) / 2 : ℕ) : ℤ),
    (((p.1 + p.2) / 4 : ℕ) : ℤ))

private def AmbPred (d : ℕ) (q : ℤ × ℤ × ℤ) : Prop :=
  IsGaussReduced q.1 q.2.1 q.2.2 ∧ discrim q.1 q.2.1 q.2.2 = -(d : ℤ) ∧
    Int.gcd (Int.gcd q.1 q.2.1 : ℤ) q.2.2 = 1 ∧
    (q.2.1 = 0 ∨ q.2.1 = q.1 ∨ q.1 = q.2.2)

private lemma ambPred_iff {d : ℕ} {a b c : ℤ} :
    AmbPred d (a, b, c) ↔ IsGaussReduced a b c ∧ discrim a b c = -(d : ℤ) ∧
      Int.gcd (Int.gcd a b : ℤ) c = 1 ∧ (b = 0 ∨ b = a ∨ a = c) :=
  Iff.rfl

private lemma gcd3_natCast (a b c : ℕ) :
    Int.gcd (Int.gcd (a : ℤ) (b : ℤ) : ℤ) (c : ℤ) = Nat.gcd (Nat.gcd a b) c := by
  rw [Int.gcd_natCast_natCast, Int.gcd_natCast_natCast]

private lemma coprime_of_add_eq {x t s : ℕ} (h : x + t = 2 * s) (hc : Nat.Coprime x s) :
    Nat.Coprime s t := by
  have h1 : Nat.gcd s t ∣ x := by
    have h2 : Nat.gcd s t ∣ x + t := h ▸ Dvd.dvd.mul_left (Nat.gcd_dvd_left s t) 2
    exact (Nat.dvd_add_left (Nat.gcd_dvd_right s t)).mp h2
  have h3 := Nat.dvd_gcd h1 (Nat.gcd_dvd_left s t)
  rw [hc.gcd_eq_one] at h3
  exact Nat.dvd_one.mp h3

private lemma coprime_of_add_eq' {x t s : ℕ} (h : x + t = 2 * s) (hc : Nat.Coprime s t) :
    Nat.Coprime x s := by
  have h1 : Nat.gcd x s ∣ t := by
    have h2 : Nat.gcd x s ∣ x + t := h ▸ Dvd.dvd.mul_left (Nat.gcd_dvd_right x s) 2
    exact (Nat.dvd_add_right (Nat.gcd_dvd_left x s)).mp h2
  have h3 := Nat.dvd_gcd (Nat.gcd_dvd_right x s) h1
  rw [hc.gcd_eq_one] at h3
  exact Nat.dvd_one.mp h3

private lemma discrim_side (x y s t : ℤ) (hy : y = 4 * s - x) (ht : t = 2 * s - x) :
    discrim s t s = -(x * y) := by
  subst hy ht
  unfold discrim
  ring

private lemma discrim_diag (x y s : ℤ) (hy : y = 4 * s - x) : discrim x x s = -(x * y) := by
  subst hy
  unfold discrim
  ring

private lemma ambPred_ambGE {d : ℕ} {p : ℕ × ℕ} (hd0 : 0 < d) (h4 : d % 4 = 0)
    (hp : p ∈ ambE d) : AmbPred d (ambGE p) := by
  obtain ⟨x, y⟩ := p
  simp only [ambE, Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hp
  obtain ⟨⟨hxy, -⟩, hcop, hle⟩ := hp
  have hx : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · simp [h] at hxy
      omega
    · exact h
  have hdZ : (d : ℤ) = 4 * (x * y) := by
    have : d = 4 * (x * y) := by omega
    exact_mod_cast this
  refine ambPred_iff.mpr ⟨⟨by exact_mod_cast hx, ?_, ?_, by exact_mod_cast hle,
    fun _ => le_rfl⟩, ?_, ?_, Or.inl rfl⟩
  · unfold discrim
    have : (0 : ℤ) < x * y := by
      have : 0 < y := by omega
      positivity
    nlinarith
  · simp only [abs_zero]
    positivity
  · unfold discrim
    rw [hdZ]
    ring
  · rw [Int.gcd_zero_right, Int.natAbs_natCast, Int.gcd_natCast_natCast]
    exact hcop

private lemma ambPred_ambGF {d : ℕ} {p : ℕ × ℕ} (hp : p ∈ ambF d) : AmbPred d (ambGF p) := by
  obtain ⟨x, y⟩ := p
  simp only [ambF, Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hp
  obtain ⟨⟨hxy, hd⟩, hlt, h4, hcop⟩ := hp
  have hx : 0 < x := by
    rcases Nat.eq_zero_or_pos x with h | h
    · simp [h] at hxy
      omega
    · exact h
  have hpos : (0 : ℤ) < x * y := by
    have : 0 < y := by omega
    positivity
  have hdZ : (d : ℤ) = x * y := by exact_mod_cast hxy.symm
  simp only [ambGF]
  set s := (x + y) / 4 with hs
  set t := (y - x) / 2 with ht
  split_ifs with h3
  · have hdisc := discrim_diag (x : ℤ) y s (by omega)
    refine ambPred_iff.mpr ⟨⟨by exact_mod_cast hx, by linarith, ?_, ?_,
      fun _ => by positivity⟩, by rw [hdisc, hdZ], ?_, Or.inr (Or.inl rfl)⟩
    · simp only [Nat.abs_cast, le_refl]
    · exact_mod_cast (by omega : x ≤ s)
    · rw [gcd3_natCast, Nat.gcd_self]
      exact hcop
  · have hdisc := discrim_side (x : ℤ) y s t (by omega) (by omega)
    refine ambPred_iff.mpr ⟨⟨by omega, by linarith, ?_, le_rfl, fun _ => by positivity⟩,
      by rw [hdisc, hdZ], ?_, Or.inr (Or.inr rfl)⟩
    · simp only [Nat.abs_cast]
      exact_mod_cast (by omega : t ≤ s)
    · rw [gcd3_natCast, Nat.gcd_eq_left (Nat.gcd_dvd_left s t)]
      exact coprime_of_add_eq (by omega) hcop

private lemma exists_ambE {d : ℕ} {a c : ℤ} (h : AmbPred d (a, 0, c)) :
    d % 4 = 0 ∧ ∃ p ∈ ambE d, ambGE p = (a, 0, c) := by
  obtain ⟨⟨ha, -, -, hac, -⟩, hdisc, hg, -⟩ := ambPred_iff.mp h
  lift a to ℕ using ha.le
  lift c to ℕ using ha.le.trans hac
  have hd : d = 4 * (a * c) := by
    unfold discrim at hdisc
    have : ((4 * (a * c) : ℕ) : ℤ) = d := by
      push_cast
      linarith
    exact_mod_cast this.symm
  have ha' : 0 < a := by exact_mod_cast ha
  have hc' : 0 < c := by exact_mod_cast ha.trans_le hac
  have hac0 : 0 < a * c := Nat.mul_pos ha' hc'
  rw [Int.gcd_zero_right, Int.natAbs_natCast, Int.gcd_natCast_natCast] at hg
  refine ⟨by omega, (a, c), ?_, rfl⟩
  simp only [ambE, Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
  exact ⟨⟨by omega, by omega⟩, hg, by exact_mod_cast hac⟩

private lemma exists_ambF_diag {d : ℕ} {a c : ℤ} (h : AmbPred d (a, a, c)) :
    ∃ p ∈ ambF d, ambGF p = (a, a, c) := by
  obtain ⟨⟨ha, -, -, hac, -⟩, hdisc, hg, -⟩ := ambPred_iff.mp h
  lift a to ℕ using ha.le
  lift c to ℕ using ha.le.trans hac
  have ha' : 0 < a := by exact_mod_cast ha
  have hac' : a ≤ c := by exact_mod_cast hac
  have hq : (a + (4 * c - a)) / 4 = c := by omega
  have hprod : a * (4 * c - a) = d := by
    unfold discrim at hdisc
    have : ((a * (4 * c - a) : ℕ) : ℤ) = d := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega)]
      push_cast
      linarith
    exact_mod_cast this
  rw [gcd3_natCast, Nat.gcd_self] at hg
  refine ⟨(a, 4 * c - a), ?_, ?_⟩
  · simp only [ambF, Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
    refine ⟨⟨hprod, ?_⟩, by omega, by omega, by rw [hq]; exact hg⟩
    rw [← hprod]
    exact Nat.mul_ne_zero (by omega) (by omega)
  · simp only [ambGF]
    simp only [show 3 * a ≤ 4 * c - a by omega, ↓reduceIte, hq]

private lemma exists_ambF_side {d : ℕ} {a b : ℤ} (h : AmbPred d (a, b, a)) (hb : b ≠ 0)
    (hba : b ≠ a) : ∃ p ∈ ambF d, ambGF p = (a, b, a) := by
  obtain ⟨⟨ha, -, hab, -, hbd⟩, hdisc, hg, -⟩ := ambPred_iff.mp h
  have hb0 : 0 ≤ b := hbd (Or.inr rfl)
  have hle : b ≤ a := (abs_le.mp hab).2
  lift a to ℕ using ha.le
  lift b to ℕ using hb0
  have hb' : b ≠ 0 := by exact_mod_cast hb
  have hba' : b < a := by
    have : b ≠ a := by exact_mod_cast hba
    have : b ≤ a := by exact_mod_cast hle
    omega
  have hq : (2 * a - b + (2 * a + b)) / 4 = a := by omega
  have hq' : (2 * a + b - (2 * a - b)) / 2 = b := by omega
  have hprod : (2 * a - b) * (2 * a + b) = d := by
    unfold discrim at hdisc
    have : (((2 * a - b) * (2 * a + b) : ℕ) : ℤ) = d := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega)]
      push_cast
      linarith
    exact_mod_cast this
  rw [gcd3_natCast, Nat.gcd_eq_left (Nat.gcd_dvd_left a b)] at hg
  refine ⟨(2 * a - b, 2 * a + b), ?_, ?_⟩
  · simp only [ambF, Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
    refine ⟨⟨hprod, ?_⟩, by omega, by omega,
      by rw [hq]; exact coprime_of_add_eq' (by omega) hg⟩
    rw [← hprod]
    exact Nat.mul_ne_zero (by omega) (by omega)
  · simp only [ambGF]
    simp only [show ¬3 * (2 * a - b) ≤ 2 * a + b by omega, ↓reduceIte, hq, hq']

private lemma ambGF_snd_ne {d : ℕ} {p : ℕ × ℕ} (hp : p ∈ ambF d) : (ambGF p).2.1 ≠ 0 := by
  obtain ⟨x, y⟩ := p
  simp only [ambF, Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hp
  obtain ⟨⟨hxy, hd⟩, hlt, h4, -⟩ := hp
  have hx : x ≠ 0 := by
    rintro rfl
    simp at hxy
    omega
  simp only [ambGF]
  split_ifs <;> simp only <;> omega

private lemma ambGE_injective : Function.Injective ambGE := by
  rintro ⟨a, c⟩ ⟨a', c'⟩ h
  simp only [ambGE, Prod.mk.injEq, Nat.cast_inj, true_and] at h
  rw [h.1, h.2]

private lemma ambGF_injOn (d : ℕ) : Set.InjOn ambGF ↑(ambF d) := by
  rintro ⟨x, y⟩ hp ⟨x', y'⟩ hp' h
  simp only [Finset.mem_coe, ambF, Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hp hp'
  obtain ⟨-, hlt, h4, -⟩ := hp
  obtain ⟨-, hlt', h4', -⟩ := hp'
  simp only [ambGF] at h
  split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> simp only [Prod.mk.injEq] <;> omega

private lemma ncard_ambiguous_eq (d : ℕ) (hd0 : 0 < d) (hd : d % 4 = 0 ∨ d % 4 = 3) :
    {q : ℤ × ℤ × ℤ | IsGaussReduced q.1 q.2.1 q.2.2 ∧ discrim q.1 q.2.1 q.2.2 = -(d : ℤ) ∧
      Int.gcd (Int.gcd q.1 q.2.1 : ℤ) q.2.2 = 1 ∧
      (q.2.1 = 0 ∨ q.2.1 = q.1 ∨ q.1 = q.2.2)}.ncard =
    (if d % 4 = 0 then
      ((Nat.divisorsAntidiagonal (d / 4)).filter
        (fun p => Nat.Coprime p.1 p.2 ∧ p.1 ≤ p.2)).card
     else 0) +
    ((Nat.divisorsAntidiagonal d).filter
      (fun p => p.1 < p.2 ∧ 4 ∣ p.1 + p.2 ∧ Nat.Coprime p.1 ((p.1 + p.2) / 4))).card := by
  have hA : {q : ℤ × ℤ × ℤ | IsGaussReduced q.1 q.2.1 q.2.2 ∧
      discrim q.1 q.2.1 q.2.2 = -(d : ℤ) ∧ Int.gcd (Int.gcd q.1 q.2.1 : ℤ) q.2.2 = 1 ∧
      (q.2.1 = 0 ∨ q.2.1 = q.1 ∨ q.1 = q.2.2)} =
      ↑(((if d % 4 = 0 then ambE d else ∅).image ambGE) ∪ (ambF d).image ambGF) := by
    ext q
    simp only [Set.mem_ofPred_eq, Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]
    constructor
    · obtain ⟨a, b, c⟩ := q
      intro h
      change AmbPred d (a, b, c) at h
      rcases eq_or_ne b 0 with rfl | hb
      · obtain ⟨h4, p, hp, hpq⟩ := exists_ambE h
        exact Or.inl ⟨p, by simpa [h4] using hp, hpq⟩
      · right
        rcases h.2.2.2 with h0 | hba | hac
        · exact absurd h0 hb
        · obtain rfl : b = a := hba
          exact exists_ambF_diag h
        · obtain rfl : a = c := hac
          by_cases hba : b = a
          · subst hba
            exact exists_ambF_diag h
          · exact exists_ambF_side h hb hba
    · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
      · split_ifs at hp with h4
        · exact ambPred_ambGE hd0 h4 hp
        · simp at hp
      · exact ambPred_ambGF hp
  have hdisj : Disjoint ((if d % 4 = 0 then ambE d else ∅).image ambGE)
      ((ambF d).image ambGF) := by
    rw [Finset.disjoint_left]
    rintro q hq1 hq2
    simp only [Finset.mem_image] at hq1 hq2
    obtain ⟨p, -, rfl⟩ := hq1
    obtain ⟨p', hp', heq⟩ := hq2
    exact ambGF_snd_ne hp' (congrArg (fun q => q.2.1) heq)
  rw [hA, Set.ncard_coe_finset, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ ambGE_injective,
    Finset.card_image_of_injOn (ambGF_injOn d)]
  rcases hd with h4 | h4 <;> simp [h4, ambE, ambF]

/-! ### Main theorem -/

/-- **Number of primitive reduced forms with $b = 0$, $b = a$ or $a = c$.** Let $d > 0$ be an
integer with $d \equiv 0$ or $3 \pmod 4$, and let $t$ be the number of distinct primes dividing
$d$. The integer triples $(a, b, c)$ with $b^2 - 4ac = -d$ and $\gcd(a, b, c) = 1$ for which the
form $a x^2 + b x y + c y^2$ is Gauss reduced ($a > 0$, $|b| \le a \le c$, and $b \ge 0$ whenever
$|b| = a$ or $a = c$) and $b = 0$, $b = a$ or $a = c$ number $2^{t-1}$ if
$d \not\equiv 12 \pmod{16}$ and $d \not\equiv 0 \pmod{32}$, $2^{t-2}$ if
$d \equiv 12 \pmod{16}$, and $2^t$ if $d \equiv 0 \pmod{32}$. Here $t \ge 1$, and $t \ge 2$ when
$d \equiv 12 \pmod{16}$, as $d$ is then even with an odd prime factor; so the exponents are
exact.

By the lemma of Oesterlé's §2 and his description of inverses in §4, these are the reduced forms
of the classes of order at most $2$ (the ambiguous classes) of primitive positive definite forms
of discriminant $-d$, which his formula (9) counts.

Source: Joseph Oesterlé, *Le problème de Gauss sur le nombre de classes*, L'Enseignement
Mathématique (2) 34 (1988), 43–67, Part I, §4, p. 50, formula (9), with the lemma and the
definition of reduced forms in Part I, §2, p. 46. Oesterlé refers the count to C. F. Gauss,
*Disquisitiones Arithmeticae* (1801), arts. 257–259 (French translation by A.-C.-M.
Poullet-Delisle, *Recherches arithmétiques*, Paris, 1807, pp. 287–294); the proof follows Gauss's
enumeration of the ambiguous forms $(A, 0, C)$ and $(2B, B, C)$, in his notation $(A, B, C)$ for
$A x^2 + 2 B x y + C y^2$, and of their reduced forms (arts. 257–258). -/
theorem ncard_ambiguous_reduced_forms (d : ℕ) (hd0 : 0 < d) (hd : d % 4 = 0 ∨ d % 4 = 3) :
    let A : Set (ℤ × ℤ × ℤ) := {q | IsGaussReduced q.1 q.2.1 q.2.2 ∧
      discrim q.1 q.2.1 q.2.2 = -(d : ℤ) ∧ Int.gcd (Int.gcd q.1 q.2.1 : ℤ) q.2.2 = 1 ∧
      (q.2.1 = 0 ∨ q.2.1 = q.1 ∨ q.1 = q.2.2)}
    (d % 16 ≠ 12 → d % 32 ≠ 0 → A.ncard = 2 ^ (d.primeFactors.card - 1)) ∧
    (d % 16 = 12 → A.ncard = 2 ^ (d.primeFactors.card - 2)) ∧
    (d % 32 = 0 → A.ncard = 2 ^ d.primeFactors.card) := by
  intro A
  have hA : A.ncard = _ := ncard_ambiguous_eq d hd0 hd
  rcases hd with h0 | h3
  · obtain ⟨n, rfl⟩ : ∃ n, d = 4 * n := ⟨d / 4, by omega⟩
    have hn0 : n ≠ 0 := by omega
    have hdiv : 4 * n / 4 = n := by omega
    simp only [h0, ↓reduceIte, hdiv] at hA
    have hpow : ∀ k : ℕ, 0 < k → 2 ^ (k - 1) + 2 ^ (k - 1) = 2 ^ k := by
      intro k hk
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ]
      ring
    have hω : ∀ m : ℕ, 1 < m → 0 < m.primeFactors.card := fun m hm =>
      Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hm)
    rcases (by omega : n % 4 = 1 ∨ n % 4 = 3 ∨ n % 4 = 2 ∨ n % 8 = 4 ∨ n % 8 = 0) with
      h1 | h3 | h2 | h4 | h8
    · rw [card_ambF_four_mul_of_mod_four_eq_one n h1] at hA
      rw [card_primeFactors_four_mul_of_odd n (by omega)]
      refine ⟨fun _ _ => ?_, fun h => by omega, fun h => by omega⟩
      rcases (by omega : n = 1 ∨ 1 < n) with rfl | hn1
      · rw [hA, card_coprime_antidiagonal_le_one, card_coprime_antidiagonal_lt_one]
        simp
      · rw [hA, card_coprime_antidiagonal_le n hn1, card_coprime_antidiagonal_lt n hn1,
          hpow _ (hω n hn1)]
        simp
    · rw [ambF_four_mul_eq_empty n (Or.inl h3), Finset.card_empty, add_zero,
        card_coprime_antidiagonal_le n (by omega)] at hA
      rw [card_primeFactors_four_mul_of_odd n (by omega)]
      refine ⟨fun h _ => by omega, fun _ => ?_, fun h => by omega⟩
      rw [hA]
      simp
    · rw [ambF_four_mul_eq_empty n (Or.inr (Or.inl h2)), Finset.card_empty, add_zero,
        card_coprime_antidiagonal_le n (by omega)] at hA
      rw [card_primeFactors_four_mul_of_even n hn0 (by omega)]
      exact ⟨fun _ _ => hA, fun h => by omega, fun h => by omega⟩
    · rw [ambF_four_mul_eq_empty n (Or.inr (Or.inr h4)), Finset.card_empty, add_zero,
        card_coprime_antidiagonal_le n (by omega)] at hA
      rw [card_primeFactors_four_mul_of_even n hn0 (by omega)]
      exact ⟨fun _ _ => hA, fun h => by omega, fun h => by omega⟩
    · have hn4 : 1 < n / 4 := by omega
      have hq : n / 4 * 4 = n := by omega
      have hωq : (n / 4).primeFactors.card = n.primeFactors.card := by
        have h := card_primeFactors_four_mul_of_even (n / 4) (by omega) (by omega)
        rw [mul_comm, hq] at h
        exact h.symm
      rw [card_ambF_four_mul_of_eight_dvd n (Nat.dvd_of_mod_eq_zero h8),
        card_coprime_antidiagonal_le n (by omega), card_coprime_antidiagonal_lt (n / 4) hn4,
        hωq, hpow _ (hω n (by omega))] at hA
      rw [card_primeFactors_four_mul_of_even n hn0 (by omega)]
      exact ⟨fun _ h => by omega, fun h => by omega, fun _ => hA⟩
  · have h0 : d % 4 ≠ 0 := by omega
    simp only [h0, ↓reduceIte, zero_add] at hA
    rw [ambF_of_mod_four_eq_three d h3,
      card_coprime_antidiagonal_lt d (by omega)] at hA
    exact ⟨fun _ _ => hA, fun h => by omega, fun h => by omega⟩

end BinaryQuadraticForm
