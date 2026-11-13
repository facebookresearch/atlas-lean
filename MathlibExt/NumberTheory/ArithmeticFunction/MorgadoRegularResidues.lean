/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Totient
public import MathlibExt.NumberTheory.UnitaryDivisor
import Mathlib.FieldTheory.Finite.Basic

open scoped BigOperators

@[expose] public section

namespace MetaMathlibExt

/-- Solvability of `M ^ 2 * X ≡ M [MOD n]` in terms of `Nat.gcd`. -/
private lemma exists_sq_mul_modEq_iff (M n : ℕ) (hn : 0 < n) :
    (∃ X : ℕ, M ^ 2 * X ≡ M [MOD n]) ↔ (M ^ 2).gcd n ∣ M := by
  constructor
  · rintro ⟨X, hx⟩
    have hdvd := hx.dvd
    have h1 : (((M ^ 2).gcd n : ℕ) : ℤ) ∣ ((n : ℕ) : ℤ) :=
      Int.ofNat_dvd.mpr (Nat.gcd_dvd_right _ _)
    have h2 : (((M ^ 2).gcd n : ℕ) : ℤ) ∣ (((M ^ 2 : ℕ)) : ℤ) :=
      Int.ofNat_dvd.mpr (Nat.gcd_dvd_left _ _)
    have e : ((M : ℕ) : ℤ)
        = ((M : ℕ) : ℤ) - (((M ^ 2 * X : ℕ)) : ℤ)
          + (((M ^ 2 : ℕ)) : ℤ) * ((X : ℕ) : ℤ) := by
      push_cast
      ring
    have h3 : (((M ^ 2).gcd n : ℕ) : ℤ) ∣ ((M : ℕ) : ℤ) := by
      rw [e]
      exact dvd_add (dvd_trans h1 hdvd) (h2.mul_right _)
    exact Int.ofNat_dvd.mp h3
  · intro h
    have hgpos : 0 < (M ^ 2).gcd n := Nat.gcd_pos_of_pos_right _ hn
    have hcop : (M ^ 2 / (M ^ 2).gcd n).Coprime (n / (M ^ 2).gcd n) :=
      Nat.coprime_div_gcd_div_gcd hgpos
    have hbpos : 0 < n / (M ^ 2).gcd n :=
      Nat.div_pos (Nat.le_of_dvd hn (Nat.gcd_dvd_right _ _)) hgpos
    have hpos : 0 < (n / (M ^ 2).gcd n).totient := Nat.totient_pos.mpr hbpos
    have hφ : (n / (M ^ 2).gcd n).totient - 1 + 1
        = (n / (M ^ 2).gcd n).totient := by omega
    have hY : (M ^ 2 / (M ^ 2).gcd n)
          * ((M ^ 2 / (M ^ 2).gcd n) ^ ((n / (M ^ 2).gcd n).totient - 1))
        ≡ 1 [MOD (n / (M ^ 2).gcd n)] := by
      have h1 : (M ^ 2 / (M ^ 2).gcd n) ^ ((n / (M ^ 2).gcd n).totient)
          ≡ 1 [MOD (n / (M ^ 2).gcd n)] :=
        Nat.ModEq.pow_totient hcop
      have e : (M ^ 2 / (M ^ 2).gcd n)
            * ((M ^ 2 / (M ^ 2).gcd n) ^ ((n / (M ^ 2).gcd n).totient - 1))
          = (M ^ 2 / (M ^ 2).gcd n) ^ ((n / (M ^ 2).gcd n).totient) := by
        rw [← pow_succ', hφ]
      rw [e]
      exact h1
    have hbase := hY.mul_right (M / (M ^ 2).gcd n)
    rw [one_mul] at hbase
    have ha0 : M ^ 2 = (M ^ 2).gcd n * (M ^ 2 / (M ^ 2).gcd n) :=
      ((Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm.trans (mul_comm _ _))
    have hb0 : n = (M ^ 2).gcd n * (n / (M ^ 2).gcd n) :=
      ((Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)).symm.trans (mul_comm _ _))
    have hc0 : M = (M ^ 2).gcd n * (M / (M ^ 2).gcd n) :=
      ((Nat.div_mul_cancel h).symm.trans (mul_comm _ _))
    refine ⟨((M ^ 2 / (M ^ 2).gcd n) ^ ((n / (M ^ 2).gcd n).totient - 1))
      * (M / (M ^ 2).gcd n), ?_⟩
    generalize hg : (M ^ 2).gcd n = g at ha0 hb0 hc0 hbase ⊢
    generalize ha : M ^ 2 / g = a at ha0 hbase ⊢
    generalize hb : n / g = b at hb0 hbase ⊢
    generalize hc : M / g = c at hc0 hbase ⊢
    have hscaled : g * ((a * (a ^ (b.totient - 1))) * c)
        ≡ g * c [MOD g * b] := by
      rw [Nat.modEq_iff_dvd] at hbase ⊢
      obtain ⟨k, hk⟩ := hbase
      refine ⟨k, by push_cast at hk ⊢; linear_combination g * hk⟩
    have eM2 : (g * a) * ((a ^ (b.totient - 1)) * c)
        = g * (((a * (a ^ (b.totient - 1)))) * c) := by
      rw [mul_assoc g a _, ← mul_assoc a _ c]
    rw [ha0, hb0, hc0, eM2]
    exact hscaled

/-- `Nat.gcd (M ^ 2) n ∣ M` holds iff `Nat.gcd M n` is a unitary divisor. -/
private lemma gcd_sq_dvd_iff_unitary (M n : ℕ) (hn : 0 < n) :
    (M ^ 2).gcd n ∣ M ↔ (M.gcd n).Coprime (n / M.gcd n) := by
  have hgpos : 0 < M.gcd n := Nat.gcd_pos_of_pos_right M hn
  have hM : M = M.gcd n * (M / M.gcd n) :=
    ((Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm.trans (mul_comm _ _))
  have hn' : n = M.gcd n * (n / M.gcd n) :=
    ((Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)).symm.trans (mul_comm _ _))
  have hcop : (M / M.gcd n).Coprime (n / M.gcd n) :=
    Nat.coprime_div_gcd_div_gcd hgpos
  have hcop2 : ((M / M.gcd n) ^ 2).Coprime (n / M.gcd n) := hcop.pow_left 2
  have hcancel : (M.gcd n * (M / M.gcd n) ^ 2).gcd (n / M.gcd n)
      = (M.gcd n).gcd (n / M.gcd n) :=
    Nat.Coprime.gcd_mul_right_cancel _ hcop2
  have e1 : M ^ 2 = M.gcd n * (M.gcd n * (M / M.gcd n) ^ 2) := by
    conv_lhs => rw [hM]
    ring
  have hsq : (M ^ 2).gcd n = M.gcd n * (M.gcd n).gcd (n / M.gcd n) := by
    generalize hg : M.gcd n = g at e1 hn' hcancel ⊢
    generalize hng : n / g = v at hn' hcancel ⊢
    rw [e1, hn', Nat.gcd_mul_left, hcancel]
  rw [hsq]
  generalize hg : M.gcd n = g at hM hgpos hcop ⊢
  rw [hM, Nat.mul_dvd_mul_iff_left hgpos]
  constructor
  · intro h
    have h1 : g.gcd (n / g) ∣ (M / g).gcd (n / g) :=
      Nat.dvd_gcd h (Nat.gcd_dvd_right _ _)
    rw [hcop.gcd_eq_one] at h1
    exact Nat.dvd_one.mp h1
  · intro h
    rw [h.gcd_eq_one]
    exact Nat.one_dvd _

/-- Regularity of `m : ZMod n` in terms of a `ℕ` congruence for `m.val`. -/
private lemma regular_iff_exists_modEq (n : ℕ) [NeZero n] (m : ZMod n) :
    (∃ x : ZMod n, m ^ 2 * x = m)
      ↔ ∃ X : ℕ, m.val ^ 2 * X ≡ m.val [MOD n] := by
  have hm : ((m.val : ℕ) : ZMod n) = m := by simp
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x.val, ?_⟩
    have e : ((m.val ^ 2 * x.val : ℕ) : ZMod n) = ((m.val : ℕ) : ZMod n) := by
      have hx' : ((x.val : ℕ) : ZMod n) = x := by simp
      simp only [Nat.cast_mul, Nat.cast_pow, hm, hx']
      exact hx
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp e
  · rintro ⟨X, hX⟩
    refine ⟨((X : ℕ) : ZMod n), ?_⟩
    have e := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hX
    rw [Nat.cast_mul, Nat.cast_pow, hm] at e
    exact e

/-- A residue is regular iff its gcd with `n` is a unitary divisor of `n`. -/
private lemma regular_iff_unitary_gcd (n : ℕ) [NeZero n] (hn : 0 < n) (m : ZMod n) :
    (∃ x : ZMod n, m ^ 2 * x = m)
      ↔ (m.val.gcd n).Coprime (n / m.val.gcd n) := by
  rw [regular_iff_exists_modEq, exists_sq_mul_modEq_iff _ _ hn,
    gcd_sq_dvd_iff_unitary _ _ hn]

/-- The gcd fiber over a unitary divisor, as an equiv with coprime residues. -/
private def fiberEquiv (n : ℕ) (hn : 0 < n) (b : ℕ)
    (hb : b ∈ n.unitaryDivisors) :
    {m : ZMod n // m.val.gcd n = b}
      ≃ {k : ZMod (n / b) // k.val.Coprime (n / b)} := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hbdvd : b ∣ n := Nat.dvd_of_mem_unitaryDivisors hb
  have hbpos : 0 < b := Nat.pos_of_dvd_of_pos hbdvd hn
  have hvpos : 0 < n / b := Nat.div_pos (Nat.le_of_dvd hn hbdvd) hbpos
  haveI : NeZero (n / b) := ⟨ne_of_gt hvpos⟩
  have hn_eq : b * (n / b) = n := Nat.mul_div_cancel' hbdvd
  have hcast_n : ∀ a : ZMod n, ((a.val : ℕ) : ZMod n) = a := fun a => by simp
  have hcast_v : ∀ k : ZMod (n / b), ((k.val : ℕ) : ZMod (n / b)) = k :=
    fun k => by simp
  refine ⟨fun av => ?_, fun kv => ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := av
    refine ⟨((a.val / b : ℕ) : ZMod (n / b)), ?_⟩
    have hlt : a.val / b < n / b := by
      rw [Nat.div_lt_iff_lt_mul hbpos]
      calc a.val < n := ZMod.val_lt a
        _ = b * (n / b) := hn_eq.symm
        _ = n / b * b := mul_comm _ _
    rw [ZMod.val_natCast_of_lt hlt]
    have h0 : 0 < a.val.gcd n := ha.symm ▸ hbpos
    have hcop := Nat.coprime_div_gcd_div_gcd h0
    rwa [ha] at hcop
  · obtain ⟨k, hk⟩ := kv
    refine ⟨((b * k.val : ℕ) : ZMod n), ?_⟩
    have hlt : b * k.val < n := by
      have hvk := ZMod.val_lt k
      have hmul := Nat.mul_lt_mul_of_pos_left hvk hbpos
      rwa [hn_eq] at hmul
    have e1 : (b * k.val).gcd (b * (n / b)) = (b * k.val).gcd n :=
      congrArg _ hn_eq
    rw [ZMod.val_natCast_of_lt hlt, ← e1, Nat.gcd_mul_left,
      hk.gcd_eq_one, mul_one]
  · intro xv
    obtain ⟨a, ha⟩ := xv
    apply Subtype.ext
    change ((b * ((((a.val / b : ℕ)) : ZMod (n / b)).val) : ℕ) : ZMod n) = a
    have hlt : a.val / b < n / b := by
      rw [Nat.div_lt_iff_lt_mul hbpos]
      calc a.val < n := ZMod.val_lt a
        _ = b * (n / b) := hn_eq.symm
        _ = n / b * b := mul_comm _ _
    have hdvd : b ∣ a.val := ha ▸ Nat.gcd_dvd_left _ _
    have hmul : b * (a.val / b) = a.val := Nat.mul_div_cancel' hdvd
    rw [ZMod.val_natCast_of_lt hlt, hmul]
    exact hcast_n a
  · intro xv
    obtain ⟨k, hk⟩ := xv
    apply Subtype.ext
    change (((((b * k.val : ℕ) : ZMod n).val / b : ℕ)) : ZMod (n / b)) = k
    have hlt : b * k.val < n := by
      have hvk := ZMod.val_lt k
      have hmul := Nat.mul_lt_mul_of_pos_left hvk hbpos
      rwa [hn_eq] at hmul
    rw [ZMod.val_natCast_of_lt hlt, Nat.mul_div_cancel_left _ hbpos]
    exact hcast_v k

/-- **Morgado's formula as a sum over unitary divisors.** For every positive integer $n$, the
number of residue classes $m \in \mathbb{Z}/n\mathbb{Z}$ for which the equation $m^2 x = m$ has a
solution $x \in \mathbb{Z}/n\mathbb{Z}$ equals the sum of $\varphi(d)$ over the unitary divisors
$d$ of $n$ (the positive divisors $d$ of $n$ with $\gcd(d, n/d) = 1$), where $\varphi$ is Euler's
totient function. -/
theorem ncard_regular_eq_sum_totient_unitaryDivisors (n : ℕ) (hn : 0 < n) :
    Set.ncard {m : ZMod n | ∃ x : ZMod n, m ^ 2 * x = m} =
      ∑ d ∈ n.unitaryDivisors, Nat.totient d := by
  have : NeZero n := ⟨hn.ne'⟩
  classical
  have hcard : Set.ncard {m : ZMod n | ∃ x : ZMod n, m ^ 2 * x = m}
      = (Finset.univ.filter
        (fun m : ZMod n => ∃ x : ZMod n, m ^ 2 * x = m)).card := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  rw [hcard]
  have hmaps : Set.MapsTo (fun m : ZMod n => m.val.gcd n)
      ↑(Finset.univ.filter (fun m : ZMod n => ∃ x : ZMod n, m ^ 2 * x = m))
      ↑n.unitaryDivisors := by
    intro m hm
    have hreg := (Finset.mem_filter.mp (Finset.mem_coe.mp hm)).2
    have hchar := (regular_iff_unitary_gcd n hn m).mp hreg
    exact Finset.mem_coe.mpr
      (Nat.mem_unitaryDivisors.mpr ⟨Nat.gcd_dvd_right _ _, hn.ne', hchar⟩)
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hmem : ∀ d ∈ n.unitaryDivisors, n / d ∈ n.unitaryDivisors := by
    intro d hd
    have hdvd : d ∣ n := Nat.dvd_of_mem_unitaryDivisors hd
    have hcop : Nat.Coprime d (n / d) := Nat.coprime_div_of_mem_unitaryDivisors hd
    have hnd : n / d ∣ n := ⟨d, (Nat.div_mul_cancel hdvd).symm⟩
    have hdd : n / (n / d) = d := Nat.div_div_self hdvd hn.ne'
    refine Nat.mem_unitaryDivisors.mpr ⟨hnd, hn.ne', ?_⟩
    rw [hdd]
    exact hcop.symm
  have hfib : ∀ b ∈ n.unitaryDivisors,
      (Finset.filter (fun a : ZMod n => a.val.gcd n = b)
        (Finset.univ.filter
          (fun m : ZMod n => ∃ x : ZMod n, m ^ 2 * x = m))).card
      = (n / b).totient := by
    intro b hb
    have hbu : Nat.Coprime b (n / b) := Nat.coprime_div_of_mem_unitaryDivisors hb
    have hbdvd : b ∣ n := Nat.dvd_of_mem_unitaryDivisors hb
    have hbpos : 0 < b := Nat.pos_of_dvd_of_pos hbdvd hn
    have : NeZero (n / b) :=
      ⟨ne_of_gt (Nat.div_pos (Nat.le_of_dvd hn hbdvd) hbpos)⟩
    have hsub : Finset.filter (fun a : ZMod n => a.val.gcd n = b)
        (Finset.univ.filter
          (fun m : ZMod n => ∃ x : ZMod n, m ^ 2 * x = m))
        = Finset.univ.filter (fun a : ZMod n => a.val.gcd n = b) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        exact h2
      · intro h2
        have hreg : ∃ x : ZMod n, a ^ 2 * x = a := by
          apply (regular_iff_unitary_gcd n hn a).mpr
          rw [h2]
          exact hbu
        exact ⟨hreg, h2⟩
    rw [hsub, ← Fintype.card_subtype,
      Fintype.card_congr (fiberEquiv n hn b hb),
      Fintype.card_congr (ZMod.unitsEquivCoprime (n := n / b)).symm]
    exact ZMod.card_units_eq_totient (n / b)
  refine (Finset.sum_congr rfl hfib).trans ?_
  refine Finset.sum_bij' (fun d _ => n / d) (fun d _ => n / d) hmem hmem
    ?_ ?_ (fun b hb => rfl)
  · intro d hd
    exact Nat.div_div_self (Nat.dvd_of_mem_unitaryDivisors hd) hn.ne'
  · intro d hd
    exact Nat.div_div_self (Nat.dvd_of_mem_unitaryDivisors hd) hn.ne'

/-- **Morgado's formula for the number of regular residues.** Let $n$ be a positive integer. Call
a residue class $m \in \mathbb{Z}/n\mathbb{Z}$ regular if the equation $m^2 x = m$ has a solution
$x \in \mathbb{Z}/n\mathbb{Z}$, and let $\varrho(n)$ be the number of regular residue classes. Let
$U(n)$ be the set of positive divisors $d$ of $n$ with $\gcd(d, n/d) = 1$. Then
$$\varrho(n) = \sum_{d \in U(n)} \varphi(d),$$
where $\varphi$ is Euler's totient function.

The sequence $\varrho(1), \varrho(2), \ldots$ is OEIS A055653.

Source: Klaus Dohmen and Mandy Lange-Geisler, "On the Number of Regular
Integers Modulo n and Its Significance for Cryptography", Journal of Integer
Sequences 29 (2026), Article 26.2.4, Definition [Morgado 1972] lines 108-112
and Theorem [Morgado 1972] (equation `eq:2`) lines 127-132:
https://cs.uwaterloo.ca/journals/JIS/VOL29/Dohmen/dohmen4.tex
The formula is attributed to J. Morgado (1972).
It follows from `ncard_regular_eq_sum_totient_unitaryDivisors`; the filter spells out
`n.unitaryDivisors` and keeps the source's shape.
Proves `Wanted` entry `morgado_card_regular_modulo`.
-/
theorem morgado_card_regular_modulo (n : ℕ) (hn : 0 < n) :
    Set.ncard {m : ZMod n | ∃ x : ZMod n, m ^ 2 * x = m} =
      ∑ d ∈ n.divisors.filter (fun d => Nat.Coprime d (n / d)), Nat.totient d :=
  ncard_regular_eq_sum_totient_unitaryDivisors n hn

end MetaMathlibExt
