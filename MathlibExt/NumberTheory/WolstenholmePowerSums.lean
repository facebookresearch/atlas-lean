/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators

private lemma sq_pp_eq_zero (p : ℕ) : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
  have h : (((p ^ 2 : ℕ)) : ZMod (p ^ 2)) = 0 := ZMod.natCast_self _
  push_cast at h
  exact h

private lemma binom_two_term (R : Type) [CommRing R] (c pp : R) (hpp : pp ^ 2 = 0)
    (k : ℕ) :
    ((-c) + pp) ^ (k + 1) = (-c) ^ (k + 1) + (k + 1 : R) * pp * (-c) ^ k := by
  rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ]
  have h0 : ∑ m ∈ Finset.range k, (-c) ^ m * pp ^ (k + 1 - m) * ↑((k + 1).choose m) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    have hle : 2 ≤ k + 1 - m := by
      have hmem := Finset.mem_range.mp hm
      omega
    have hppz : pp ^ (k + 1 - m) = 0 := pow_eq_zero_of_le hle hpp
    simp [hppz]
  rw [h0, zero_add]
  have e1 : k + 1 - (k + 1) = 0 := by omega
  have e2 : k + 1 - k = 1 := by omega
  rw [e1, e2]
  simp only [Nat.choose_self, Nat.choose_succ_self_right, Nat.cast_succ, pow_zero,
    mul_one, pow_one]
  ring

private lemma coprime_of_mem_Icc (p t : ℕ) (hp : p.Prime)
    (ht1 : 1 ≤ t) (ht2 : t ≤ p - 1) : t.Coprime (p ^ 2) := by
  have hlt : t < p := by omega
  have hne : t ≠ 0 := by omega
  have h := Nat.coprime_of_lt_prime hne hlt hp
  exact Nat.Coprime.pow_right 2 h.symm

private lemma isUnit_cast_of_mem_Icc (p t : ℕ) (hp : p.Prime)
    (ht1 : 1 ≤ t) (ht2 : t ≤ p - 1) :
    IsUnit ((t : ZMod (p ^ 2)) : ZMod (p ^ 2)) := by
  rw [ZMod.isUnit_iff_coprime]
  exact coprime_of_mem_Icc p t hp ht1 ht2

private lemma isUnit_two (p : ℕ) (hp : p.Prime) (hodd : Odd p) :
    IsUnit ((2 : ZMod (p ^ 2)) : ZMod (p ^ 2)) := by
  have h2c : ((2 : ℕ) : ZMod (p ^ 2)) = 2 := by norm_cast
  rw [← h2c, ZMod.isUnit_iff_coprime]
  have hp2 : p ≠ 2 := by
    rcases hodd with ⟨k, hk⟩
    omega
  have hcp : Nat.Coprime 2 p := by
    rw [Nat.coprime_primes (by norm_num : Nat.Prime 2) hp]
    exact Ne.symm hp2
  exact Nat.Coprime.pow_right 2 hcp

private lemma pair_add (p ν t : ℕ) (hp : p.Prime) (hν : 1 ≤ ν) (hνodd : Odd ν)
    (ht1 : 1 ≤ t) (ht2 : t ≤ p - 1) :
    (((t : ZMod (p ^ 2)) ^ ν)⁻¹) + ((((p - t : ℕ) : ZMod (p ^ 2)) ^ ν)⁻¹)
      = -((ν : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))
        * (((t : ZMod (p ^ 2)) ^ (ν + 1))⁻¹)) := by
  have hle : t ≤ p := by
    have hpos := hp.pos
    omega
  have hpp : (p : ZMod (p ^ 2)) ^ 2 = 0 := sq_pp_eq_zero p
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ν ≠ 0)
  have hk1 : ν = k + 1 := hk.trans (Nat.succ_eq_add_one k)
  have ⟨m, hm⟩ := hνodd
  have hkEven : Even k := ⟨m, by omega⟩
  set c := ((t : ZMod (p ^ 2))) with hc
  set pp := ((p : ZMod (p ^ 2))) with hppd
  set d := ((((p - t : ℕ) : ZMod (p ^ 2)))) with hd
  set A := c ^ ν with hA
  set B := d ^ ν with hB
  set C2 := c ^ (ν + 1) with hC2
  set ai := A⁻¹ with hai
  set bi := B⁻¹ with hbi
  set ci := C2⁻¹ with hci
  have hdc : d = pp - c := by
    have hpt : p - t + t = p := Nat.sub_add_cancel hle
    have hcast : d + c = pp := by
      rw [hd, hppd, hc, ← Nat.cast_add, hpt]
    rw [eq_sub_iff_add_eq]
    exact hcast
  have huC : IsUnit c := by
    rw [hc]
    exact isUnit_cast_of_mem_Icc p t hp ht1 ht2
  have hpt1 : 1 ≤ p - t := by omega
  have hpt2 : p - t ≤ p - 1 := by omega
  have huD : IsUnit d := by
    rw [hd]
    exact isUnit_cast_of_mem_Icc p (p - t) hp hpt1 hpt2
  have huA : IsUnit A := by
    rw [hA]
    exact huC.pow ν
  have huB : IsUnit B := by
    rw [hB]
    exact huD.pow ν
  have huC2 : IsUnit C2 := by
    rw [hC2]
    exact huC.pow (ν + 1)
  have hAB : IsUnit (A * B) := huA.mul huB
  have e1 : ai * A = 1 := by
    rw [hai]
    exact ZMod.inv_mul_of_unit A huA
  have e2 : bi * B = 1 := by
    rw [hbi]
    exact ZMod.inv_mul_of_unit B huB
  have e3 : ci * C2 = 1 := by
    rw [hci]
    exact ZMod.inv_mul_of_unit C2 huC2
  have hdp : d = (-c) + pp := by
    rw [hdc]
    ring
  have hbin := binom_two_term (ZMod (p ^ 2)) c pp hpp k
  have hoddK : Odd (k + 1) := hk1 ▸ hνodd
  have hs1 : (-c) ^ (k + 1) = -(c ^ (k + 1)) := hoddK.neg_pow c
  have hs2 : (-c) ^ k = c ^ k := hkEven.neg_pow c
  have hcastν : ((ν : ZMod (p ^ 2))) = ((k : ZMod (p ^ 2)) + 1) := by
    rw [hk1]
    norm_cast
  have hBexp2 : B = (-c) ^ (k + 1) + ((k : ZMod (p ^ 2)) + 1) * pp * ((-c) ^ k) := by
    have hBexp : B = d ^ (k + 1) := by rw [hB, hk1]
    rw [hBexp, hdp]
    exact hbin
  have hAexp : A = c ^ (k + 1) := by rw [hA, hk1]
  have hBe : A + B = (ν : ZMod (p ^ 2)) * pp * c ^ k := by
    have hcastν' : ((k : ZMod (p ^ 2)) + 1) = ((ν : ZMod (p ^ 2))) := hcastν.symm
    rw [hAexp, hBexp2, hs1, hs2, hcastν', ← add_assoc, add_neg_cancel, zero_add]
  have hA2 : A ^ 2 = c ^ (ν * 2) := by
    rw [hA, ← pow_mul]
  have hC2e : C2 * c ^ k = c ^ (ν * 2) := by
    rw [hC2, ← pow_add]
    have hen : ν + 1 + k = ν * 2 := by omega
    rw [hen]
  have hAC : ci * A ^ 2 = c ^ k := by
    have htmp : ci * A ^ 2 = (ci * C2) * c ^ k := by
      rw [hA2, ← hC2e, mul_assoc]
    rw [htmp, e3, one_mul]
  have hL : (ai + bi) * (A * B) = A + B := by
    linear_combination B * e1 + A * e2
  have hR : (-((ν : ZMod (p ^ 2)) * pp * ci)) * (A * B) = A + B := by
    linear_combination (ν : ZMod (p ^ 2)) * pp * hAC
      + (-1 - (ν : ZMod (p ^ 2)) * pp * ci * A) * hBe
      + (-((ν : ZMod (p ^ 2)) ^ 2 * (ci * A * c ^ k))) * hpp
  have hfin : ai + bi = -((ν : ZMod (p ^ 2)) * pp * ci) := by
    apply hAB.mul_left_injective
    show (ai + bi) * (A * B) = (-((ν : ZMod (p ^ 2)) * pp * ci)) * (A * B)
    rw [hL, hR]
  exact hfin

private lemma field_inv_sum_zero (p k : ℕ) (hp : p.Prime) (hk2 : 2 ≤ k)
    (hk3 : k ≤ p - 3) :
    ∑ t ∈ Finset.Icc 1 (p - 1), ((((t : ZMod p) ^ k))⁻¹) = 0 := by
  haveI := Fact.mk hp
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hklt : k < Fintype.card (ZMod p) - 1 := by omega
  have hfield : ∑ x : ZMod p, x ^ k = 0 :=
    FiniteField.sum_pow_lt_card_sub_one (ZMod p) k hklt
  have hkne : k ≠ 0 := by omega
  have h1 : (∑ t ∈ Finset.Icc 1 (p - 1), ((((t : ZMod p) ^ k))⁻¹))
      = ∑ x ∈ Finset.univ \ {0}, ((x ^ k)⁻¹) := by
    refine Finset.sum_bij (fun t _ => ((t : ZMod p))) ?_ ?_ ?_ ?_
    · intro t ht
      have ht' := Finset.mem_Icc.mp ht
      show ((t : ZMod p)) ∈ Finset.univ \ {0}
      rw [Finset.mem_sdiff]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [Finset.mem_singleton]
      intro h0
      have hva : ((t : ZMod p)).val = t := ZMod.val_natCast_of_lt (by omega : t < p)
      rw [h0, ZMod.val_zero] at hva
      omega
    · intro a ha b hb hab
      have ha' := Finset.mem_Icc.mp ha
      have hb' := Finset.mem_Icc.mp hb
      have hab' : ((a : ZMod p)) = ((b : ZMod p)) := hab
      have hva : ((a : ZMod p)).val = a := ZMod.val_natCast_of_lt (by omega : a < p)
      have hvb : ((b : ZMod p)).val = b := ZMod.val_natCast_of_lt (by omega : b < p)
      rw [hab'] at hva
      rw [hvb] at hva
      exact hva.symm
    · intro x hx
      have hx' := Finset.mem_sdiff.mp hx
      have hxne : x ≠ 0 := fun h => hx'.2 (Finset.mem_singleton.mpr h)
      refine ⟨x.val, Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
      · have hne : x.val ≠ 0 := fun h => hxne ((ZMod.val_eq_zero _).mp h)
        omega
      · have hlt := ZMod.val_lt x
        omega
      · show ((x.val : ZMod p)) = x
        have e1 : ((((x.val : ℕ))) : ZMod p) = x.cast := ZMod.natCast_val x
        rw [e1]
        exact ZMod.cast_id p x
    · intro t ht
      rfl
  have h2 : (∑ x ∈ Finset.univ \ {0}, ((x ^ k)⁻¹))
      = ∑ x : ZMod p, ((x ^ k)⁻¹) := by
    have h0mem : (0 : ZMod p) ∈ Finset.univ := Finset.mem_univ 0
    have h0val : ((((0 : ZMod p) ^ k))⁻¹) = 0 := by
      rw [zero_pow hkne, inv_zero]
    have hadd := Finset.add_sum_erase Finset.univ (fun x : ZMod p => ((x ^ k)⁻¹)) h0mem
    rw [h0val, zero_add] at hadd
    rwa [Finset.sdiff_singleton_eq_erase]
  have h3 : (∑ x : ZMod p, ((x ^ k)⁻¹)) = ∑ x : ZMod p, x ^ k := by
    have e : ∀ x : ZMod p, (((x ^ k))⁻¹) = ((Equiv.inv (ZMod p)) x) ^ k := by
      intro x
      rw [Equiv.inv_apply]
      exact (inv_pow x k).symm
    simp_rw [e]
    exact Equiv.sum_comp (Equiv.inv (ZMod p)) (fun x : ZMod p => x ^ k)
  rw [h1, h2, h3]
  exact hfield

private lemma sum_reindex (p ν : ℕ) :
    ∑ t ∈ Finset.Icc 1 (p - 1), ((((p - t : ℕ) : ZMod (p ^ 2)) ^ ν)⁻¹)
      = ∑ s ∈ Finset.Icc 1 (p - 1), ((((s : ZMod (p ^ 2)) ^ ν)⁻¹)) := by
  refine Finset.sum_bij (fun t _ => p - t) ?_ ?_ ?_ ?_
  · intro t ht
    have ht' := Finset.mem_Icc.mp ht
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro a ha b hb hab
    have ha' := Finset.mem_Icc.mp ha
    have hb' := Finset.mem_Icc.mp hb
    have hab' : p - a = p - b := hab
    omega
  · intro s hs
    have hs' := Finset.mem_Icc.mp hs
    refine ⟨p - s, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    show p - (p - s) = s
    omega
  · intro t ht
    rfl

/--
**Wolstenholme's congruence for odd powers.** Let $\nu \ge 1$ be odd and let $p$ be a prime with
$p \ge \nu + 4$. Then in $\mathbb{Z}/p^2\mathbb{Z}$
$$
\sum_{t=1}^{p-1} (t^{\nu})^{-1} = 0,
$$
where each $t^{\nu}$ is invertible modulo $p^2$ because $1 \le t < p$.

For $\nu = 1$ this is Wolstenholme's congruence of 1862; the general statement is Theorem 131 of
Hardy and Wright and was first studied by Leudesdorf.

Source: Christian Ballot, "On a Congruence of Kimball and Webb Involving Lucas
Sequences," Journal of Integer Sequences 17 (2014), Article 14.1.3,
Theorem (label thm:L), lines 94–99,
https://cs.uwaterloo.ca/journals/JIS/VOL17/Ballot/ballot7.tex
-/
theorem wolstenholme_harmonic_power_sum
    (ν p : ℕ) (hν : 1 ≤ ν) (hνodd : Odd ν)
    (hp : p.Prime) (hpν : ν + 4 ≤ p) :
    ∑ t ∈ Finset.Icc 1 (p - 1), (((t : ZMod (p ^ 2)) ^ ν)⁻¹) = 0 := by
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI := Fact.mk hp
  have hodd : Odd p := hp.odd_of_ne_two (by omega : p ≠ 2)
  have hpp : (p : ZMod (p ^ 2)) ^ 2 = 0 := sq_pp_eq_zero p
  have hpair : ∀ t ∈ Finset.Icc 1 (p - 1),
      (((t : ZMod (p ^ 2)) ^ ν)⁻¹) + ((((p - t : ℕ) : ZMod (p ^ 2)) ^ ν)⁻¹)
        = -((ν : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))
          * (((t : ZMod (p ^ 2)) ^ (ν + 1))⁻¹)) := by
    intro t ht
    have ht' := Finset.mem_Icc.mp ht
    exact pair_add p ν t hp hν hνodd ht'.1 ht'.2
  have h2S : 2 * (∑ t ∈ Finset.Icc 1 (p - 1), ((((t : ZMod (p ^ 2)) ^ ν)⁻¹)))
      = (-((ν : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))))
        * (∑ t ∈ Finset.Icc 1 (p - 1), ((((t : ZMod (p ^ 2)) ^ (ν + 1)))⁻¹)) := by
    have hsum : (∑ t ∈ Finset.Icc 1 (p - 1),
          (-((ν : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)))
            * ((((t : ZMod (p ^ 2)) ^ (ν + 1)))⁻¹)))
        = (∑ t ∈ Finset.Icc 1 (p - 1), ((((t : ZMod (p ^ 2)) ^ ν)⁻¹)))
          + (∑ t ∈ Finset.Icc 1 (p - 1), ((((p - t : ℕ) : ZMod (p ^ 2)) ^ ν)⁻¹)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun t ht => by
        have hp2 := (hpair t ht).symm
        rwa [← neg_mul] at hp2)
    rw [← Finset.mul_sum] at hsum
    rw [hsum, sum_reindex]
    ring
  have hUdiv : ∃ w : ZMod (p ^ 2),
      (∑ t ∈ Finset.Icc 1 (p - 1), ((((t : ZMod (p ^ 2)) ^ (ν + 1)))⁻¹))
        = (p : ZMod (p ^ 2)) * w := by
    have hdiv : p ∣ p ^ 2 := ⟨p, pow_two p⟩
    have hphi : ((ZMod.castHom hdiv (ZMod p))
        (∑ t ∈ Finset.Icc 1 (p - 1), ((((t : ZMod (p ^ 2)) ^ (ν + 1)))⁻¹))) = 0 := by
      rw [map_sum]
      have hterm : ∀ t ∈ Finset.Icc 1 (p - 1),
          ((ZMod.castHom hdiv (ZMod p)) ((((t : ZMod (p ^ 2)) ^ (ν + 1)))⁻¹))
            = ((((t : ZMod p) ^ (ν + 1)))⁻¹) := by
        intro t ht
        have ht' := Finset.mem_Icc.mp ht
        have hu : IsUnit ((((t : ZMod (p ^ 2)) ^ (ν + 1)) : ZMod (p ^ 2))) :=
          (isUnit_cast_of_mem_Icc p t hp ht'.1 ht'.2).pow (ν + 1)
        have h1 : (ZMod.castHom hdiv (ZMod p)) (((t : ZMod (p ^ 2)) ^ (ν + 1)))
            * (ZMod.castHom hdiv (ZMod p)) (((((t : ZMod (p ^ 2)) ^ (ν + 1)))⁻¹)) = 1 := by
          rw [← map_mul, ZMod.mul_inv_of_unit _ hu, map_one]
        have h2 : (ZMod.castHom hdiv (ZMod p)) (((t : ZMod (p ^ 2)) ^ (ν + 1)))
            = (((t : ZMod p) ^ (ν + 1)) : ZMod p) := by
          rw [map_pow]
          congr 1
          simp
        rw [h2] at h1
        exact eq_inv_of_mul_eq_one_right h1
      have hEq : (∑ t ∈ Finset.Icc 1 (p - 1),
          ((ZMod.castHom hdiv (ZMod p)) ((((t : ZMod (p ^ 2)) ^ (ν + 1)))⁻¹)))
          = (∑ t ∈ Finset.Icc 1 (p - 1), ((((t : ZMod p) ^ (ν + 1)))⁻¹)) :=
        Finset.sum_congr rfl hterm
      rw [hEq]
      exact field_inv_sum_zero p (ν + 1) hp (by omega) (by omega)
    have hcast : (((((∑ t ∈ Finset.Icc 1 (p - 1),
        ((((t : ZMod (p ^ 2)) ^ (ν + 1)))⁻¹))).val : ℕ)) : ZMod p) = 0 := by
      have e1 : (((((∑ t ∈ Finset.Icc 1 (p - 1),
        ((((t : ZMod (p ^ 2)) ^ (ν + 1)))⁻¹))).val : ℕ)) : ZMod p)
          = (∑ t ∈ Finset.Icc 1 (p - 1), ((((t : ZMod (p ^ 2)) ^ (ν + 1)))⁻¹)).cast :=
        ZMod.natCast_val _
      have e2 : (∑ t ∈ Finset.Icc 1 (p - 1), ((((t : ZMod (p ^ 2)) ^ (ν + 1)))⁻¹)).cast
          = ((ZMod.castHom hdiv (ZMod p))
            (∑ t ∈ Finset.Icc 1 (p - 1), ((((t : ZMod (p ^ 2)) ^ (ν + 1)))⁻¹))) :=
        (ZMod.castHom_apply _).symm
      rw [e1, e2]
      exact hphi
    have hdvd : p ∣ (∑ t ∈ Finset.Icc 1 (p - 1),
        ((((t : ZMod (p ^ 2)) ^ (ν + 1)))⁻¹)).val :=
      (CharP.cast_eq_zero_iff (ZMod p) p _).mp hcast
    obtain ⟨w0, hw0⟩ := hdvd
    refine ⟨((w0 : ZMod (p ^ 2))), ?_⟩
    have h1 : (((((∑ t ∈ Finset.Icc 1 (p - 1),
        ((((t : ZMod (p ^ 2)) ^ (ν + 1)))⁻¹))).val : ℕ)) : ZMod (p ^ 2))
        = (∑ t ∈ Finset.Icc 1 (p - 1), ((((t : ZMod (p ^ 2)) ^ (ν + 1)))⁻¹)) := by
      have e := ZMod.natCast_val (R := ZMod (p ^ 2))
        (∑ t ∈ Finset.Icc 1 (p - 1), ((((t : ZMod (p ^ 2)) ^ (ν + 1)))⁻¹))
      rwa [ZMod.cast_id] at e
    have h2 : ((((p * w0 : ℕ))) : ZMod (p ^ 2))
        = (p : ZMod (p ^ 2)) * ((w0 : ZMod (p ^ 2))) := by
      rw [Nat.cast_mul]
    rw [hw0] at h1
    rw [h2] at h1
    exact h1.symm
  obtain ⟨w, hw⟩ := hUdiv
  have h2S0 : 2 * (∑ t ∈ Finset.Icc 1 (p - 1), ((((t : ZMod (p ^ 2)) ^ ν)⁻¹))) = 0 := by
    rw [h2S, hw]
    have hpp2 : (p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) = 0 := by
      rw [← pow_two]
      exact hpp
    have hrw : (-((ν : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)))) * ((p : ZMod (p ^ 2)) * w)
        = (-((ν : ZMod (p ^ 2)) * w)) * ((p : ZMod (p ^ 2)) * (p : ZMod (p ^ 2))) := by
      ring
    rw [hrw, hpp2, mul_zero]
  have h2unit : IsUnit ((2 : ZMod (p ^ 2)) : ZMod (p ^ 2)) := isUnit_two p hp hodd
  have hfin : (∑ t ∈ Finset.Icc 1 (p - 1), ((((t : ZMod (p ^ 2)) ^ ν)⁻¹))) = 0 := by
    have h := congrArg (fun x : ZMod (p ^ 2) => (2 : ZMod (p ^ 2))⁻¹ * x) h2S0
    simp only [mul_zero] at h
    rwa [← mul_assoc, ZMod.inv_mul_of_unit _ h2unit, one_mul] at h
  exact hfin

end MetaMathlibExt
