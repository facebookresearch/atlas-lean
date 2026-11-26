/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.Divisors
public import MathlibExt.NumberTheory.CoveringSystem
import Mathlib.Data.Finset.Image
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring

/-!
# Replacing the largest prime factor of a covering system's moduli

If the divisors of `L` that are at least `m` cover the integers, and `q` is a prime divisor
of `L` larger than a prime `p ≥ m` not dividing `L`, then the divisors of
`p ^ L.factorization q * (L / q ^ L.factorization q)` that are at least `m` also cover
the integers. The new residues keep the old residues modulo the part coprime to `q` and
re-encode the `q`-part digit by digit in base `p` (`rebase`).

## Main statements

* `MetaMathlibExt.exists_covering_divisors_replace_largest_prime`: the replacement lemma.

## References

* Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
  INTEGERS 26 (2026), Article A38; arXiv:2508.18062, Lemma 6.
-/

namespace MetaMathlibExt

/-- Combine the residue `R` with the residue `T` (mod `P`), given a Bezout coefficient
`a` with `P * a + U * b = 1` for the modulus `U` of `R`. -/
private def crtVal (R T : ℤ) (P : ℕ) (a : ℤ) : ℤ :=
  T + P * a * (R - T)

private theorem crtVal_modEq_left (R T : ℤ) (P : ℕ) (a : ℤ) :
    crtVal R T P a ≡ T [ZMOD (P : ℤ)] := by
  rw [Int.modEq_iff_dvd]
  exact ⟨-(a * (R - T)), by unfold crtVal; ring⟩

private theorem crtVal_modEq_right (R T : ℤ) (P U : ℕ) (a b : ℤ)
    (hBez : (P : ℤ) * a + (U : ℤ) * b = 1) :
    crtVal R T P a ≡ R [ZMOD (U : ℤ)] := by
  rw [Int.modEq_iff_dvd]
  refine ⟨(R - T) * b, ?_⟩
  have hub : (U : ℤ) * b = 1 - (P : ℤ) * a := by omega
  have hrr : R - crtVal R T P a = (R - T) * (1 - (P : ℤ) * a) := by
    unfold crtVal; ring
  rw [hrr, ← hub]; ring

private theorem exists_bezout (P U : ℕ) (h : P.Coprime U) :
    ∃ a b : ℤ, (P : ℤ) * a + (U : ℤ) * b = 1 := by
  refine ⟨P.gcdA U, P.gcdB U, ?_⟩
  have hg : P.gcd U = 1 := h
  have hbez := Nat.gcd_eq_gcd_ab P U
  rw [hg, Nat.cast_one] at hbez
  exact hbez.symm

/-- Re-encode the lowest `j` base-`q` digits of `b` as a base-`p` number. -/
private def rebase (q p j b : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | j + 1 => rebase q p j (b % q ^ j) + p ^ j * ((b / q ^ j) % q % p)

private theorem rebase_zero (q p b : ℕ) : rebase q p 0 b = 0 :=
  rfl

private theorem rebase_succ (q p j b : ℕ) :
    rebase q p (j + 1) b
      = rebase q p j (b % q ^ j) + p ^ j * ((b / q ^ j) % q % p) :=
  rfl

/-- Dividing a remainder by the cofactor gives the remainder of the quotient. -/
private theorem div_mod_mul (b m n : ℕ) (hm : 0 < m) :
    (b % (m * n)) / m = (b / m) % n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hmn_pos : 0 < m * n := Nat.mul_pos hm (Nat.pos_of_ne_zero hn)
    have hmod : b % (m * n) < m * n := by
      apply Nat.mod_lt
      exact hmn_pos
    have hlt : (b % (m * n)) / m < n :=
      Nat.div_lt_of_lt_mul hmod
    have hdiv : b / m = n * (b / (m * n)) + (b % (m * n)) / m := by
      conv_lhs => rw [← Nat.div_add_mod b (m * n)]
      rw [show m * n * (b / (m * n)) + b % (m * n)
          = (b % (m * n)) + m * (n * (b / (m * n))) from by ring]
      rw [Nat.add_mul_div_left _ _ hm, add_comm]
    conv_rhs => rw [hdiv]
    rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- The re-encoded number fits in `j` base-`p` digits. -/
private theorem rebase_lt (q p j b : ℕ) (hp : 1 ≤ p) : rebase q p j b < p ^ j := by
  induction j generalizing b with
  | zero =>
    rw [rebase_zero, pow_zero]
    omega
  | succ j ih =>
    have hdig : (b / q ^ j) % q % p < p := Nat.mod_lt _ hp
    have hrec := ih (b % q ^ j)
    have hP0 : 0 < p ^ j := pow_pos (by omega) j
    rw [rebase_succ, pow_succ]
    have hR : rebase q p j (b % q ^ j) ≤ p ^ j - 1 := by omega
    have hd : (b / q ^ j) % q % p ≤ p - 1 := by omega
    have hmul : p ^ j * ((b / q ^ j) % q % p) ≤ p ^ j * (p - 1) :=
      Nat.mul_le_mul (le_refl _) hd
    have hsum : rebase q p j (b % q ^ j) + p ^ j * ((b / q ^ j) % q % p)
        ≤ (p ^ j - 1) + p ^ j * (p - 1) := Nat.add_le_add hR hmul
    have hpred : p ^ j * (p - 1) = p ^ j * p - p ^ j := by
      rw [mul_tsub, mul_one]
    refine lt_of_le_of_lt hsum ?_
    rw [hpred]
    have hXP : p ^ j ≤ p ^ j * p := Nat.le_mul_of_pos_right _ (by omega)
    omega

/-- Re-encoding only sees the lowest `j` base-`q` digits. -/
private theorem rebase_stable (q p j b : ℕ) (hq : 1 ≤ q) :
    rebase q p j b = rebase q p j (b % q ^ j) := by
  cases j with
  | zero => rw [rebase_zero, rebase_zero]
  | succ j =>
    rw [rebase_succ, rebase_succ]
    have hmod : (b % q ^ (j + 1)) % q ^ j = b % q ^ j :=
      Nat.mod_mod_of_dvd b (pow_dvd_pow q (Nat.le_succ j))
    rw [hmod]
    have hdig : ((b % q ^ (j + 1)) / q ^ j) % q = (b / q ^ j) % q := by
      have hqj : q ^ (j + 1) = q ^ j * q := pow_succ q j
      have hqj0 : 0 < q ^ j := pow_pos (by omega) j
      rw [hqj, div_mod_mul b (q ^ j) q hqj0, Nat.mod_mod]
    rw [hdig]

/-- Reducing the re-encoded number recovers the re-encoding of the reduced number. -/
private theorem rebase_ancestry (q p e j b : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hle : j ≤ e) : rebase q p e b % p ^ j = rebase q p j (b % q ^ j) := by
  revert b hle
  induction e with
  | zero =>
    intro b hle
    have hj : j = 0 := Nat.le_zero.mp hle
    subst hj
    rw [Nat.mod_eq_of_lt (rebase_lt q p 0 b hp)]
    exact rebase_stable q p 0 b hq
  | succ e ih =>
    intro b hle
    rcases eq_or_lt_of_le hle with rfl | hlt
    · rw [Nat.mod_eq_of_lt (rebase_lt q p (e + 1) b hp)]
      exact rebase_stable q p (e + 1) b hq
    · have hle' : j ≤ e := Nat.lt_succ_iff.mp hlt
      rw [rebase_succ]
      obtain ⟨Z, hZ⟩ : p ^ j ∣ p ^ e * ((b / q ^ e) % q % p) :=
        (pow_dvd_pow p hle').mul_right _
      rw [hZ, Nat.add_mul_mod_self_left]
      have ih' := ih (b % q ^ e) hle'
      rw [ih']
      have hmod : (b % q ^ e) % q ^ j = b % q ^ j :=
        Nat.mod_mod_of_dvd b (pow_dvd_pow q hle')
      rw [hmod]

/-- Every number below `p ^ e` is a re-encoding of a number below `q ^ e`. -/
private theorem rebase_surj (q p e : ℕ) (hp : 1 ≤ p) (hpq : p ≤ q) (c : ℕ)
    (hc : c < p ^ e) : ∃ b < q ^ e, rebase q p e b = c := by
  revert c hc
  induction e with
  | zero =>
    intro c hc
    rw [pow_zero] at hc
    have hc0 : c = 0 := by omega
    exact ⟨0, by rw [pow_zero]; omega, by rw [rebase_zero]; exact hc0.symm⟩
  | succ e ih =>
    intro c hc
    have hpe0 : 0 < p ^ e := pow_pos (by omega) e
    have hdc : c / p ^ e < p := by
      apply Nat.div_lt_of_lt_mul
      have hcp := hc
      rwa [pow_succ] at hcp
    have hc0 : c % p ^ e < p ^ e := Nat.mod_lt _ hpe0
    obtain ⟨b₀, hb₀, ihb₀⟩ := ih (c % p ^ e) hc0
    have hq0 : 0 < q := by omega
    have hqe0 : 0 < q ^ e := pow_pos hq0 e
    have hdc_le : c / p ^ e < q := lt_of_lt_of_le hdc hpq
    refine ⟨b₀ + q ^ e * (c / p ^ e), ?_, ?_⟩
    · calc b₀ + q ^ e * (c / p ^ e) < q ^ e + q ^ e * (c / p ^ e) := by omega
        _ = q ^ e * (c / p ^ e + 1) := by ring
        _ ≤ q ^ e * q := Nat.mul_le_mul (le_refl _) (by omega)
        _ = q ^ (e + 1) := by rw [pow_succ]
    · rw [rebase_succ]
      have hmod : (b₀ + q ^ e * (c / p ^ e)) % q ^ e = b₀ := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb₀]
      have hdiv : (b₀ + q ^ e * (c / p ^ e)) / q ^ e = c / p ^ e := by
        have hz : b₀ / q ^ e = 0 := by
          have hdm := Nat.div_add_mod b₀ (q ^ e)
          rw [Nat.mod_eq_of_lt hb₀] at hdm
          have hATOM : q ^ e * (b₀ / q ^ e) = 0 := by omega
          rcases Nat.mul_eq_zero.mp hATOM with h0 | h0
          · omega
          · exact h0
        rw [Nat.add_mul_div_left _ _ hqe0, hz, Nat.zero_add]
      rw [hmod, hdiv, ihb₀]
      have hdp : (c / p ^ e) % q % p = c / p ^ e := by
        rw [Nat.mod_eq_of_lt (lt_of_lt_of_le hdc hpq), Nat.mod_eq_of_lt hdc]
      rw [hdp]
      have hdm := Nat.div_add_mod c (p ^ e)
      omega

/-- Congruence of integers is equality of their natural residues. -/
private theorem modEq_iff_natMod_eq (a b : ℤ) (n : ℕ) (hn : n ≠ 0) :
    a ≡ b [ZMOD (n : ℤ)] ↔ a.natMod n = b.natMod n := by
  constructor
  · intro h
    have heq : a % (n : ℤ) = b % (n : ℤ) := h
    unfold Int.natMod
    rw [heq]
  · intro h
    change a % (n : ℤ) = b % (n : ℤ)
    unfold Int.natMod at h
    have hn' : (n : ℤ) ≠ 0 := by omega
    have ha : ((a % (n : ℤ)).toNat : ℤ) = a % (n : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ hn')
    have hb : ((b % (n : ℤ)).toNat : ℤ) = b % (n : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg _ hn')
    rw [h] at ha
    exact ha.symm.trans hb

/-- Reducing the natural residue mod `M` further mod `u` gives the residue mod `u`. -/
private theorem natMod_mod (x : ℤ) (M u : ℕ) (hM : M ≠ 0) (hu : u ≠ 0)
    (hdiv : u ∣ M) : (x.natMod M) % u = x.natMod u := by
  have hM' : (M : ℤ) ≠ 0 := by omega
  have hu' : (u : ℤ) ≠ 0 := by omega
  have h1 : (((x.natMod M) % u : ℕ) : ℤ) = x % (u : ℤ) := by
    rw [Int.natCast_emod]
    unfold Int.natMod
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hM'),
      Int.emod_emod_of_dvd x (Int.natCast_dvd_natCast.mpr hdiv)]
  have h2 : ((x.natMod u : ℕ) : ℤ) = x % (u : ℤ) := by
    unfold Int.natMod
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ hu')
  rw [← h1] at h2
  exact Nat.cast_injective h2.symm

/-- The natural residue of a cast number is the natural remainder. -/
private theorem natMod_natCast (t p j : ℕ) : ((t : ℤ).natMod (p ^ j)) = t % p ^ j := by
  unfold Int.natMod
  rw [← Nat.cast_pow, ← Int.natCast_emod, Int.toNat_natCast]

/-- Every divisor of `L` is a `q`-power times a divisor of the `q`-free part of `L`. -/
private theorem eq_prime_pow_mul_of_dvd (d L q : ℕ) (hL : L ≠ 0) (hd : d ∣ L) :
    ∃ j u, j ≤ L.factorization q ∧ u ∣ L / q ^ L.factorization q ∧ d = q ^ j * u := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hL (zero_dvd_iff.mp hd)
  exact ⟨d.factorization q, d / q ^ d.factorization q,
    (Nat.factorization_le_iff_dvd hd0 hL).mpr hd q, Nat.ordCompl_dvd_ordCompl_of_dvd hd q,
    (Nat.ordProj_mul_ordCompl_eq_self d q).symm⟩

/-- The new residue for `d`: the old residue mod the `p`-free part, re-encoded mod `p`. -/
private def newRes (res : ℕ → ℤ) (p q : ℕ) (d : ℕ) : ℤ :=
  crtVal (res (q ^ d.factorization p * (d / p ^ d.factorization p)))
    ((rebase q p (d.factorization p)
      ((res (q ^ d.factorization p * (d / p ^ d.factorization p))).natMod
        (q ^ d.factorization p))) : ℤ)
    (p ^ d.factorization p)
    ((p ^ d.factorization p).gcdA (d / p ^ d.factorization p))

private theorem newRes_spec (res : ℕ → ℤ) (p q j u : ℕ) (hp : p.Prime)
    (hu0 : u ≠ 0) (hpu : ¬ p ∣ u) :
    newRes res p q (p ^ j * u) ≡ res (q ^ j * u) [ZMOD (u : ℤ)] ∧
    newRes res p q (p ^ j * u)
      ≡ (((rebase q p j ((res (q ^ j * u)).natMod (q ^ j)) : ℕ)) : ℤ)
      [ZMOD ((p ^ j : ℕ) : ℤ)] := by
  have hp0 : 0 < p := hp.pos
  have hP0 : 0 < p ^ j := pow_pos hp0 j
  have hne : p ^ j * u ≠ 0 := mul_ne_zero hP0.ne' hu0
  have hle : j ≤ (p ^ j * u).factorization p :=
    (hp.pow_dvd_iff_le_factorization hne).mp (dvd_mul_right (p ^ j) u)
  have hge : (p ^ j * u).factorization p ≤ j := by
    by_contra hcon
    have hlt : j < (p ^ j * u).factorization p := by omega
    have hle2 : j + 1 ≤ (p ^ j * u).factorization p := by omega
    have hdvd := (hp.pow_dvd_iff_le_factorization hne).mpr hle2
    rw [pow_succ] at hdvd
    have hpu' : p ∣ u := (mul_dvd_mul_iff_left hP0.ne').mp hdvd
    exact hpu hpu'
  have hfact : (p ^ j * u).factorization p = j := le_antisymm hge hle
  have hcop : u.Coprime (p ^ j) := by
    have h1 : p.Coprime u := (hp.coprime_iff_not_dvd).mpr hpu
    exact Nat.Coprime.pow_right _ h1.symm
  have hBez : ((p ^ j : ℕ) : ℤ) * ((p ^ j).gcdA u)
      + ((u : ℕ) : ℤ) * ((p ^ j).gcdB u) = 1 := by
    have hg : (p ^ j).gcd u = 1 := by
      rw [Nat.gcd_comm]
      exact hcop
    have hbez := Nat.gcd_eq_gcd_ab (p ^ j) u
    rw [hg, Nat.cast_one] at hbez
    exact hbez.symm
  have hunfold : newRes res p q (p ^ j * u)
      = crtVal (res (q ^ j * u))
        (((rebase q p j ((res (q ^ j * u)).natMod (q ^ j)) : ℕ)) : ℤ)
        (p ^ j) ((p ^ j).gcdA u) := by
    unfold newRes
    rw [hfact, Nat.mul_div_cancel_left _ hP0]
  rw [hunfold]
  exact ⟨crtVal_modEq_right _ _ _ _ _ _ hBez, crtVal_modEq_left _ _ _ _⟩

/-- Lift prescribed residues mod `M` and mod `Q` to a single integer. -/
private theorem exists_lift_modEq (x : ℤ) (b M Q : ℕ) (hcop : M.Coprime Q) :
    ∃ y : ℤ, y ≡ x [ZMOD (M : ℤ)] ∧ y ≡ (b : ℤ) [ZMOD (Q : ℤ)] := by
  obtain ⟨a, bb, hBez⟩ := exists_bezout M Q hcop
  exact ⟨crtVal (b : ℤ) x M a, crtVal_modEq_left _ _ _ _,
    crtVal_modEq_right _ _ _ _ _ _ hBez⟩

/-- **Replacing the largest prime factor of the modulus set.** Let $m, L \in \mathbb{N}$, let
$p \ge m$ be a prime with $p \nmid L$, let $q > p$ be the largest prime dividing $L$, and write
$\nu_q(L)$ for the exponent of $q$ in $L$. Suppose there are residues $r_d \in \mathbb{Z}$, one
for each divisor $d \ge m$ of $L$, such that every integer $x$ satisfies $x \equiv r_d \pmod d$
for some such $d$. Then the same holds with $L$ replaced by $p^{\nu_q(L)} L / q^{\nu_q(L)}$:
there are residues $s_d \in \mathbb{Z}$, one for each divisor $d \ge m$ of
$p^{\nu_q(L)} L / q^{\nu_q(L)}$, such that every integer $x$ satisfies $x \equiv s_d \pmod d$
for some such $d$.

Source: Jonah Klein, *On a Conjecture of Krukenberg and a Problem of Dalton and Trifonov*,
INTEGERS 26 (2026), Article A38, Lemma 6 (`integers-2026-A38-lem-6`). -/
public theorem exists_covering_divisors_replace_largest_prime {m p q L : ℕ}
    (hp : p.Prime) (hmp : m ≤ p) (hpL : ¬ p ∣ L) (hq : q.Prime) (hqL : q ∣ L)
    (hpq : p < q) (hqmax : ∀ r : ℕ, r.Prime → r ∣ L → r ≤ q)
    (h : ∃ res : ℕ → ℤ, Int.IsCoveringSystem
      ((L.divisors.filter fun d => m ≤ d).image fun d => (res d, d))) :
    ∃ res : ℕ → ℤ, Int.IsCoveringSystem
      (((p ^ L.factorization q * (L / q ^ L.factorization q)).divisors.filter
        fun d => m ≤ d).image fun d => (res d, d)) := by
  have _ : q ≤ q := hqmax q hq hqL
  obtain ⟨res, hcov⟩ := h
  by_cases hL0 : L = 0
  · subst hL0
    simp only [Nat.divisors_zero, Finset.filter_empty, Finset.image_empty] at hcov
    obtain ⟨c, hc, _⟩ := hcov 0
    exact (Finset.notMem_empty c hc).elim
  · set e := L.factorization q
    set M := L / q ^ e
    have hq2 : 2 ≤ q := hq.two_le
    have hp2 : 2 ≤ p := hp.two_le
    have hLM : L = q ^ e * M := (Nat.ordProj_mul_ordCompl_eq_self L q).symm
    have hM0 : M ≠ 0 := by
      intro hcon
      rw [hcon, mul_zero] at hLM
      exact hL0 hLM
    have hqM : ¬ q ∣ M := Nat.not_dvd_ordCompl hq hL0
    have hpM : ¬ p ∣ M := by
      intro hpdvd
      have hM_dvd : M ∣ L := by
        rw [hLM]
        exact dvd_mul_left M (q ^ e)
      exact hpL (hpdvd.trans hM_dvd)
    have hMcop : M.Coprime (q ^ e) := by
      have h1 : q.Coprime M := (hq.coprime_iff_not_dvd).mpr hqM
      exact Nat.Coprime.pow_right _ h1.symm
    have hL'0 : p ^ e * M ≠ 0 := mul_ne_zero (pow_pos hp.pos e).ne' hM0
    refine ⟨newRes res p q, ?_⟩
    intro x
    by_cases h0 : ∃ u, u ∣ M ∧ m ≤ u ∧ x ≡ res u [ZMOD (u : ℤ)]
    · obtain ⟨u, huM, hum, hxu⟩ := h0
      have hu0 : u ≠ 0 := by
        intro hcon
        rw [hcon] at huM
        exact hM0 (zero_dvd_iff.mp huM)
      have hpu : ¬ p ∣ u := fun hdiv => hpM (hdiv.trans huM)
      have hspec : newRes res p q u ≡ res u [ZMOD (u : ℤ)] := by
        simpa using (newRes_spec res p q 0 u hp hu0 hpu).1
      refine ⟨(newRes res p q u, u), Finset.mem_image_of_mem _ ?_,
        hxu.trans hspec.symm⟩
      rw [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨huM.trans (dvd_mul_left M (p ^ e)), hL'0⟩, hum⟩
    · have hrich : ∀ b : ℕ, b < q ^ e → ∃ j u, j ≤ e ∧ u ∣ M ∧ q ^ j * u ≥ m ∧
          x ≡ res (q ^ j * u) [ZMOD (u : ℤ)] ∧
          (b : ℤ) ≡ res (q ^ j * u) [ZMOD ((q ^ j : ℕ) : ℤ)] := by
        intro b hb
        obtain ⟨y, hyM, hyb⟩ := exists_lift_modEq x b M (q ^ e) hMcop
        obtain ⟨c, hc, hyc⟩ := hcov y
        rw [Finset.mem_image] at hc
        obtain ⟨d, hdmem, rfl⟩ := hc
        rw [Finset.mem_filter, Nat.mem_divisors] at hdmem
        obtain ⟨⟨hdvd, -⟩, hdm⟩ := hdmem
        obtain ⟨j, u, hje, huM, rfl⟩ :=
          eq_prime_pow_mul_of_dvd d L q hL0 hdvd
        refine ⟨j, u, hje, huM, hdm, ?_, ?_⟩
        · exact (hyM.symm.of_dvd (Int.natCast_dvd_natCast.mpr huM)).trans
            (hyc.of_dvd (Int.natCast_dvd_natCast.mpr (dvd_mul_left u (q ^ j))))
        · exact (hyb.symm.of_dvd
            (Int.natCast_dvd_natCast.mpr (pow_dvd_pow q hje))).trans
            (hyc.of_dvd (Int.natCast_dvd_natCast.mpr (dvd_mul_right (q ^ j) u)))
      have hpe0 : 0 < p ^ e := pow_pos hp.pos e
      have hplt : x.natMod (p ^ e) < p ^ e := Int.natMod_lt hpe0.ne'
      obtain ⟨b, hb, hlift⟩ :=
        rebase_surj q p e (by omega) (Nat.le_of_lt hpq) (x.natMod (p ^ e)) hplt
      obtain ⟨j, u, hje, huM, hdm, hxu, hbx⟩ := hrich b hb
      have hj1 : 1 ≤ j := by
        by_contra hcon
        have hj0 : j = 0 := by omega
        subst hj0
        exact h0 ⟨u, huM, by simpa using hdm, by simpa using hxu⟩
      have hu0 : u ≠ 0 := by
        intro hcon
        rw [hcon] at huM
        exact hM0 (zero_dvd_iff.mp huM)
      have hpu : ¬ p ∣ u := fun hdiv => hpM (hdiv.trans huM)
      have hspec := newRes_spec res p q j u hp hu0 hpu
      have hxU : x ≡ newRes res p q (p ^ j * u) [ZMOD (u : ℤ)] :=
        hxu.trans hspec.1.symm
      have hP0 : 0 < p ^ j := pow_pos hp.pos j
      have hQ0 : 0 < q ^ j := pow_pos hq.pos j
      have hρ : b % q ^ j = (res (q ^ j * u)).natMod (q ^ j) := by
        have h := (modEq_iff_natMod_eq (b : ℤ) (res (q ^ j * u)) (q ^ j)
          hQ0.ne').mp hbx
        rw [Nat.cast_pow] at h
        have hnat : ((b : ℤ).natMod (q ^ j)) = b % q ^ j :=
          natMod_natCast b q j
        rw [hnat] at h
        exact h
      have hanc := rebase_ancestry q p e j b (by omega) (by omega) hje
      rw [hlift, hρ] at hanc
      have htow := natMod_mod x (p ^ e) (p ^ j) hpe0.ne' hP0.ne'
        (pow_dvd_pow p hje)
      simp only [Nat.cast_pow] at htow
      have ht_lt : rebase q p j ((res (q ^ j * u)).natMod (q ^ j)) < p ^ j :=
        rebase_lt q p j _ (by omega)
      have hxP : x ≡ newRes res p q (p ^ j * u) [ZMOD ((p ^ j : ℕ) : ℤ)] := by
        have hxmod : x.natMod (p ^ j)
            = rebase q p j ((res (q ^ j * u)).natMod (q ^ j)) := by
          rw [← htow, hanc]
        have hxmod' : x
            ≡ (((rebase q p j ((res (q ^ j * u)).natMod (q ^ j)) : ℕ)) : ℤ)
            [ZMOD ((p ^ j : ℕ) : ℤ)] := by
          rw [modEq_iff_natMod_eq _ _ _ hP0.ne']
          simp only [Nat.cast_pow]
          rw [hxmod]
          have hnat2 : ((((rebase q p j ((res (q ^ j * u)).natMod (q ^ j)) :
            ℕ)) : ℤ).natMod (p ^ j))
              = (rebase q p j ((res (q ^ j * u)).natMod (q ^ j))) % p ^ j :=
            natMod_natCast _ p j
          rw [hnat2, Nat.mod_eq_of_lt ht_lt]
        exact hxmod'.trans hspec.2.symm
      have hcop' : u.Coprime (p ^ j) := by
        have h1 : p.Coprime u := (hp.coprime_iff_not_dvd).mpr hpu
        exact Nat.Coprime.pow_right _ h1.symm
      have hcomb : x ≡ newRes res p q (p ^ j * u) [ZMOD ((u * p ^ j : ℕ) : ℤ)] := by
        rw [Nat.cast_mul]
        exact (Int.modEq_and_modEq_iff_modEq_mul (by simpa using hcop')).mp ⟨hxU, hxP⟩
      rw [mul_comm u (p ^ j)] at hcomb
      refine ⟨(newRes res p q (p ^ j * u), p ^ j * u),
        Finset.mem_image_of_mem _ ?_, hcomb⟩
      rw [Finset.mem_filter, Nat.mem_divisors]
      refine ⟨⟨mul_dvd_mul (pow_dvd_pow p hje) huM, hL'0⟩, ?_⟩
      calc m ≤ p := hmp
        _ ≤ p ^ j := Nat.le_self_pow (by omega) p
        _ ≤ p ^ j * u := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hu0)

end MetaMathlibExt
