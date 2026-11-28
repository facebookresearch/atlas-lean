/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
Copyright (c) the flt-regular authors, as recorded in that repository.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Alex J. Best, Christopher Birkbeck, Riccardo Brasca, Eric Rodriguez Boidi,
Ruben Van de Velde, Andrew Yang
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_flt_regular.lean`
and
`P2M/Sol/S_flt_regular.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.

`FltRegular/NumberTheory/*`, `FltRegular/MayAssume/*`, `FltRegular/CaseI/*`,
`FltRegular/CaseII/*` and `FltRegular/FltRegular.lean`
(https://github.com/leanprover-community/flt-regular), the formalization of
Fermat's Last Theorem for regular primes that `P2M/Sol/S_flt_regular.lean`
ports with proofs:
The source's NOTICE (item 2) and ATTRIBUTION.md (§3) record this credit and
name the upstream files; that project's per-file headers are not reproduced there.

Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.NumberTheory.FLT.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
import Mathlib.RingTheory.Prime
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.KummerExtension
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.ClassGroup.ExtendedHom
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.NormTrace
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.Tactic.NormNum.Prime
import MathlibExt.NumberTheory.Cyclotomic.CoefficientDivisibility
import MathlibExt.NumberTheory.Cyclotomic.TwoFactorIdealBound
import MathlibExt.NumberTheory.PrimitiveFamily
import MathlibExt.RingTheory.DedekindDomain.PrimeAvoidingGenerator
import MathlibExt.RingTheory.DedekindDomain.UnramifiedIdealDescent
import MathlibExt.RingTheory.DedekindDomain.UnramifiedMinpoly

/-!
# Kummer's theorem on Fermat's Last Theorem for regular primes

A prime `p` is regular when `p` does not divide the class number of the
`p`-th cyclotomic field. This file proves that Fermat's Last Theorem holds
for every odd regular prime exponent.

The proof follows Kummer's classical argument in the ring of integers of
the `p`-th cyclotomic field: the first case, where `p` divides none of
`x`, `y`, `z`, and the second case, where `p` divides one of them, are
handled separately, using Kummer's lemma on units and infinite descent.
All auxiliary definitions and lemmas are private.
-/

namespace FltRegularPort.Internal

section Port_FLT_Deep_RegularPrimes_lean

open Nat Polynomial NumberField

open scoped NumberField

variable (n p : ℕ) [hp : Fact p.Prime]

def IsRegularNumber : Prop :=
  n.Coprime <| Fintype.card <| ClassGroup (𝓞 <| CyclotomicField n ℚ)

def IsRegularPrime : Prop :=
  IsRegularNumber p

theorem isPrincipal_of_isPrincipal_pow_of_coprime
    {A : Type*} [CommRing A] [IsDedekindDomain A] [Fintype (ClassGroup A)]
    {p : ℕ}
    (H : p.Coprime <| Fintype.card <| ClassGroup A) {I : Ideal A}
    (hI : (I ^ p).IsPrincipal) : I.IsPrincipal := by
  by_cases Izero : I = 0
  · rw [Izero]
    exact bot_isPrincipal
  rw [← ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_of_ne_zero _)] at hI ⊢
  swap
  · exact Izero
  swap
  · exact pow_ne_zero p Izero
  · rw [← orderOf_eq_one_iff, ← Nat.dvd_one, ← H, Nat.dvd_gcd_iff]
    refine ⟨?_, orderOf_dvd_card⟩
    rwa [orderOf_dvd_iff_pow_eq_one, ← map_pow, SubmonoidClass.mk_pow]

end Port_FLT_Deep_RegularPrimes_lean

section Port_FLT_Deep_Regular_FinpFarm_lean

open Int Finset

namespace FltRegular

variable {p : ℕ} (hpri : p.Prime)

namespace CaseI

theorem two_lt (hp5 : 5 ≤ p) : 2 < p := by omega

def f0k₁ (b : ℤ) (p : ℕ) : ℕ → ℤ := fun x =>
  if x = 1 then b else if x = p.pred then -b else 0

def f0k₂ (a b : ℤ) : ℕ → ℤ := fun x => if x = 0 then a - b else if x = 1 then b - a else 0

def f1k₂ (a : ℤ) : ℕ → ℤ := fun x => if x = 0 then a else if x = 2 then -a else 0

theorem aux_cong0k₁ {k : Fin p} (hcong : k ≡ -1 [ZMOD p]) :
    k = ⟨p.pred, Nat.pred_lt hpri.ne_zero⟩ := by
  have h2 := hpri.two_le
  have hk := k.is_lt
  have hd : (p : ℤ) ∣ (k : ℤ) + 1 := by
    have := hcong.dvd
    simpa using (dvd_neg.mpr this)
  have hle := Int.le_of_dvd (by omega) hd
  apply Fin.ext
  show (k : ℕ) = p.pred
  simp only [Nat.pred_eq_sub_one]
  omega

theorem aux_cong0k₂ {k : Fin p} (hcong : k ≡ 1 [ZMOD p]) : k = ⟨1, hpri.one_lt⟩ := by
  have h2 := hpri.two_le
  have hk := k.is_lt
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hcong.dvd (by omega)
  apply Fin.ext
  show (k : ℕ) = 1
  omega

theorem aux_cong1k₁ {k : Fin p} (hcong : k ≡ 0 [ZMOD p]) : k = ⟨0, hpri.pos⟩ := by
  have h2 := hpri.two_le
  have hk := k.is_lt
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hcong.dvd (by omega)
  apply Fin.ext
  show (k : ℕ) = 0
  omega

theorem aux_cong1k₂ {k : Fin p} (hpri : p.Prime) (hp5 : 5 ≤ p)
    (hcong : k ≡ 1 + 1 [ZMOD p]) : k = ⟨2, two_lt hp5⟩ := by
  have h2 := hpri.two_le
  have hk := k.is_lt
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hcong.dvd (by omega)
  apply Fin.ext
  show (k : ℕ) = 2
  omega

theorem auxf0k₁ (hp5 : 5 ≤ p) (b : ℤ) : ∃ i : Fin p, f0k₁ b p (i : ℕ) = 0 := by
  refine ⟨⟨3, by omega⟩, ?_⟩
  simp only [f0k₁, Nat.pred_eq_sub_one]
  rw [if_neg (by omega), if_neg (by omega)]

theorem auxf0k₂ (hp5 : 5 ≤ p) (a b : ℤ) : ∃ i : Fin p, f0k₂ a b (i : ℕ) = 0 := by
  refine ⟨⟨2, by omega⟩, ?_⟩
  simp only [f0k₂]
  rw [if_neg (by omega), if_neg (by omega)]

include hpri in

theorem auxf1k₂ (a : ℤ) : ∃ i : Fin p, f1k₂ a i = 0 := by
  refine ⟨⟨1, hpri.one_lt⟩, ?_⟩
  simp only [f1k₂]
  rw [if_neg (by omega), if_neg (by omega)]

theorem auxk₁k₂ {k₁ k₂ : Fin p} (hpri : p.Prime) (hcong : k₂ ≡ k₁ - 1 [ZMOD p]) :
    (k₁ : ℕ) ≠ (k₂ : ℕ) := by
  have h2 := hpri.two_le
  have hk1 := k₁.is_lt
  have hk2 := k₂.is_lt
  intro habs
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hcong.dvd (by omega)
  omega

end CaseI

namespace MayAssume

theorem p_dvd_c_of_ab_of_anegc {p : ℕ} {a b c : ℤ} (hpri : p.Prime)
    (hp : p ≠ 3) (h : a ^ p + b ^ p = c ^ p) (hab : a ≡ b [ZMOD p])
    (hbc : b ≡ -c [ZMOD p]) : ↑p ∣ c := by
  letI : Fact p.Prime := ⟨hpri⟩
  replace h := congrArg (fun n : ℤ => (n : ZMod p)) h
  simp only [Int.cast_add, Int.cast_pow, ZMod.pow_card] at h
  rw [← ZMod.intCast_eq_intCast_iff] at hab hbc
  push_cast at hbc
  rw [hab, hbc] at h
  have h3 : (3 : ZMod p) * (c : ZMod p) = 0 := by linear_combination -h
  have hp3 : (3 : ZMod p) ≠ 0 := by
    intro h3'
    have hdvd : p ∣ 3 := by
      have : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h3'
      exact (ZMod.natCast_eq_zero_iff 3 p).mp this
    exact hp ((Nat.prime_dvd_prime_iff_eq hpri Nat.prime_three).mp hdvd)
  have hc : (c : ZMod p) = 0 := by
    rcases mul_eq_zero.mp h3 with h' | h'
    · exact absurd h' hp3
    · exact h'
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp hc

theorem a_not_cong_b {p : ℕ} {a b c : ℤ} (hpri : p.Prime) (hp5 : 5 ≤ p)
    (hprod : a * b * c ≠ 0)
    (h : a ^ p + b ^ p = c ^ p) (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (caseI : ¬↑p ∣ a * b * c) :
    ∃ x y z : ℤ, x ^ p + y ^ p = z ^ p ∧
      ({x, y, z} : Finset ℤ).gcd id = 1 ∧ ¬x ≡ y [ZMOD p] ∧ x * y * z ≠ 0 ∧
        ¬↑p ∣ x * y * z := by
  by_cases H : a ≡ b [ZMOD p]
  swap
  · exact ⟨a, b, c, h, hgcd, H, hprod, caseI⟩
  have hodd : Odd p := hpri.odd_of_ne_two (by omega)
  refine ⟨a, -c, -b, ?_, ?_, fun habs => ?_, fun habs => ?_, fun habs => ?_⟩
  · rw [hodd.neg_pow, hodd.neg_pow]
    linear_combination h
  · have h1 : ({a, -c, -b} : Finset ℤ).gcd id ∣ 1 := by
      rw [← hgcd]
      apply Finset.dvd_gcd
      intro x hx
      have ha : ({a, -c, -b} : Finset ℤ).gcd id ∣ a :=
        Finset.gcd_dvd (show a ∈ ({a, -c, -b} : Finset ℤ) by simp)
      have hcc : ({a, -c, -b} : Finset ℤ).gcd id ∣ -c :=
        Finset.gcd_dvd (show -c ∈ ({a, -c, -b} : Finset ℤ) by simp)
      have hbb : ({a, -c, -b} : Finset ℤ).gcd id ∣ -b :=
        Finset.gcd_dvd (show -b ∈ ({a, -c, -b} : Finset ℤ) by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [id_eq]
      rcases hx with rfl | rfl | rfl
      · exact ha
      · exact (dvd_neg).mp hbb
      · exact (dvd_neg).mp hcc
    rw [← Finset.normalize_gcd]
    exact normalize_eq_one.mpr (isUnit_of_dvd_one h1)
  · exact caseI ((p_dvd_c_of_ab_of_anegc hpri (by omega) h H
      (H.symm.trans habs)).mul_left (a * b))
  · exact hprod (by rw [show a * b * c = a * -c * -b by ring, habs])
  · exact caseI (by rwa [show a * -c * -b = a * b * c by ring] at habs)

end MayAssume

end FltRegular

end Port_FLT_Deep_Regular_FinpFarm_lean

section Port_FLT_Deep_Regular_CyclotomicFarm_lean

open Finset Nat Finset.Nat Polynomial Int Finset.Int NumberField NumberField.IsCMField Ideal NumberField.Ideal

open scoped NumberField

namespace FltRegular

variable {p : ℕ}

theorem exists_int_sub_pow_prime_dvd {A : Type*} [CommRing A] [IsCyclotomicExtension {p} ℤ A]
    [hp : Fact p.Prime] (a : A) : ∃ m : ℤ, a ^ p - m ∈ span ({(p : A)} : Set A) := by
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_
    (IsCyclotomicExtension.adjoin_roots (S := {p}) (A := ℤ) a)
  · intro x hx
    use 1
    simp_all
  · intro r
    use r ^ p
    simp
  · rintro x y _ _ ⟨b, hb⟩ ⟨c, hc⟩
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out x y
    rw [mul_assoc, mul_assoc] at hr
    rw [hr]
    use c + b
    push_cast
    rw [sub_add_eq_sub_sub, sub_eq_add_neg, sub_eq_add_neg, add_comm (x ^ p + _), add_assoc,
      add_assoc]
    apply Ideal.add_mem _ _
    · convert Ideal.add_mem _ hb hc using 1
      ring
    · rw [mem_span_singleton]
      exact dvd_mul_right _ _
  · rintro x y _ _ ⟨b, hb⟩ ⟨c, hc⟩
    rw [mul_pow]
    use b * c
    have := Ideal.mul_mem_left _ (x ^ p) hc
    rw [mul_sub] at this
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub] at this hb ⊢
    convert this using 2
    rw [Int.cast_mul, _root_.map_mul, _root_.map_mul]
    congr 1
    exact (sub_eq_zero.mp hb).symm

private theorem isPrimitiveRoot_of_mem_nthRootsFinset' {A : Type*} [CommRing A] [IsDomain A]
    [hp : Fact p.Prime] {η : A} (hη : η ∈ nthRootsFinset p (1 : A)) (hne1 : η ≠ 1) :
    IsPrimitiveRoot η p := by
  have hpow : η ^ p = 1 := (Polynomial.mem_nthRootsFinset hp.out.pos 1).1 hη
  have hord : orderOf η = p := by
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp.out _
      (orderOf_dvd_of_pow_eq_one hpow)) with h1 | hp'
    · exact absurd (orderOf_eq_one_iff.mp h1) hne1
    · exact hp'
  exact hord ▸ IsPrimitiveRoot.orderOf η

section FltIdeals

local notation "K" => CyclotomicField p ℚ
local notation "R" => 𝓞 K

noncomputable def fltIdeals (x y : ℤ) {η : R} (_ : η ∈ nthRootsFinset p (1 : R)) : Ideal R :=
  span ({↑x + η * ↑y} : Set R)

theorem mem_fltIdeals (x y : ℤ) {η : R} (hη : η ∈ nthRootsFinset p (1 : R)) :
    ↑x + η * ↑y ∈ fltIdeals x y hη :=
  subset_span rfl

variable [Fact p.Prime] in

theorem aux_lem_flt {x y z : ℤ} (H : x ^ p + y ^ p = z ^ p) (caseI : ¬↑p ∣ x * y * z) :
    ¬(p : ℤ) ∣ (x + y : ℤ) := by
  intro habs
  replace habs : ↑p ∣ (x + y : ℤ) := by simpa using habs
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_add] at habs
  replace H := congr_arg (fun x : ℤ => (x : ZMod p)) H.symm
  simp only [Int.cast_add, Int.cast_pow, ZMod.pow_card, habs,
    ZMod.intCast_zmod_eq_zero_iff_dvd] at H
  exact caseI (Dvd.dvd.mul_left H _)

variable [Fact p.Prime] in

theorem one_sub_zeta_prime {η : R} (hη : η ∈ nthRootsFinset p (1 : R)) (hne1 : η ≠ 1) :
    Prime (1 - η) := by
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨by exact_mod_cast (Fact.out : p.Prime).ne_zero⟩
  have h : IsPrimitiveRoot ((η : R) : K) p :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mpr
      (isPrimitiveRoot_of_mem_nthRootsFinset' hη hne1)
  have key : h.toInteger = η := by ext; rfl
  haveI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  have hprime : Prime (h.toInteger - 1) := h.zeta_sub_one_prime'
  rw [key] at hprime
  simpa only [neg_sub] using Prime.neg hprime

variable [Fact p.Prime] in

theorem diff_of_roots (_ph : 5 ≤ p) {η₁ η₂ : R} (hη₁ : η₁ ∈ nthRootsFinset p (1 : R))
    (hη₂ : η₂ ∈ nthRootsFinset p (1 : R)) (hdiff : η₁ ≠ η₂) (hwlog : η₁ ≠ 1) :
    ∃ u : Rˣ, η₁ - η₂ = u * (1 - η₁) := by
  have h : IsPrimitiveRoot η₁ p := isPrimitiveRoot_of_mem_nthRootsFinset' hη₁ hwlog
  obtain ⟨u, hu⟩ := h.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime
    (Fact.out : p.Prime) hη₁ hη₂ hdiff
  refine ⟨-u, ?_⟩
  rw [← hu]
  simp only [Units.val_neg, Units.val_mul, Units.val_one]
  ring

variable [Fact p.Prime] in

theorem diff_of_roots2 (ph : 5 ≤ p) {η₁ η₂ : R} (hη₁ : η₁ ∈ nthRootsFinset p (1 : R))
    (hη₂ : η₂ ∈ nthRootsFinset p (1 : R)) (hdiff : η₁ ≠ η₂) (hwlog : η₁ ≠ 1) :
    ∃ u : Rˣ, η₂ - η₁ = u * (1 - η₁) := by
  obtain ⟨u, hu⟩ := diff_of_roots ph hη₁ hη₂ hdiff hwlog
  exact ⟨-u, by simp [← hu]⟩

variable [Fact p.Prime] in

theorem fltIdeals_coprime2_lemma (ph : 5 ≤ p) {x y : ℤ} {η₁ η₂ : R}
    (hη₁ : η₁ ∈ nthRootsFinset p (1 : R)) (hη₂ : η₂ ∈ nthRootsFinset p (1 : R))
    (hdiff : η₁ ≠ η₂) (hp : IsCoprime x y) (hp2 : ¬(p : ℤ) ∣ (x + y : ℤ))
    (hwlog : η₁ ≠ 1) :
    (fltIdeals x y hη₁) ⊔ (fltIdeals x y hη₂) = ⊤ := by
  apply by_contradiction
  intro h
  let I := fltIdeals x y hη₁ ⊔ fltIdeals x y hη₂
  obtain ⟨P, hP1, hP2⟩ := Ideal.exists_le_maximal I h
  have hiP : fltIdeals x y hη₁ ≤ P := le_trans le_sup_left hP2
  have hel1 : ∃ v : Rˣ, (v : R) * y * (1 - η₁) ∈ I := by
    obtain ⟨v, hv⟩ := diff_of_roots ph hη₁ hη₂ hdiff hwlog
    refine ⟨v, ?_⟩
    have := Ideal.sub_mem _
      (mem_sup_left (mem_fltIdeals x y hη₁)) (mem_sup_right (mem_fltIdeals x y hη₂))
    rwa [add_sub_add_left_eq_sub, ← sub_mul, hv, mul_right_comm] at this
  have hel2 : ∃ v : Rˣ, (v : R) * x * (1 - η₁) ∈ I := by
    obtain ⟨v, hv⟩ := diff_of_roots2 ph hη₁ hη₂ hdiff hwlog
    refine ⟨v, ?_⟩
    have := Ideal.add_mem _ (mul_mem_left _ η₂ (mem_sup_left (mem_fltIdeals x y hη₁)))
        (mul_mem_left _ (-η₁) (mem_sup_right (mem_fltIdeals x y hη₂)))
    have h1 : η₂ * (↑x + η₁ * ↑y) + -η₁ * (↑x + η₂ * ↑y) = (η₂ - η₁) * x := by ring
    rwa [h1, hv, mul_right_comm] at this
  have hel11 : (y : R) * (1 - η₁) ∈ P := by
    obtain ⟨v, hv⟩ := hel1
    rw [mul_assoc] at hv
    exact (unit_mul_mem_iff_mem P v.isUnit).1 (hP2 hv)
  have hel22 : (x : R) * (1 - η₁) ∈ P := by
    obtain ⟨v, hv⟩ := hel2
    rw [mul_assoc] at hv
    exact (unit_mul_mem_iff_mem P v.isUnit).1 (hP2 hv)
  have hPrime := hP1.isPrime
  have hprime2 := IsPrime.mem_or_mem hPrime hel11
  have hprime3 := IsPrime.mem_or_mem hPrime hel22
  have HC : 1 - η₁ ∈ P → False := by
    intro h
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    haveI : NeZero ((p : ℕ) : ℚ) := ⟨by exact_mod_cast (Fact.out : p.Prime).ne_zero⟩
    have eta_sub_one_ne_zero := sub_ne_zero.mpr (Ne.symm hwlog)
    have hηprime : IsPrime (Ideal.span ({1 - η₁} : Set R)) := by
      rw [span_singleton_prime eta_sub_one_ne_zero]
      apply one_sub_zeta_prime hη₁ hwlog
    have H5 : IsPrime (Ideal.span ({(p : ℤ)} : Set ℤ)) := by
      have h2 : (p : ℤ) ≠ 0 := by simp [NeZero.ne p]
      have h1 : Prime (p : ℤ) := by
        rw [← Nat.prime_iff_prime_int]
        exact Fact.out
      rw [span_singleton_prime h2]
      apply h1
    have hηP : Ideal.span ({1 - η₁} : Set R) = P := by
      have hle : Ideal.span ({1 - η₁} : Set R) ≤ P := by
        rw [span_le]
        simp [h]
      apply (@Ring.DimensionLeOne.prime_le_prime_iff_eq _ _ _ _ _ hηprime hPrime _).1 hle
      intro hbot
      rw [span_eq_bot] at hbot
      simp only [Set.mem_singleton_iff, forall_eq, sub_eq_zero] at hbot
      exact hwlog hbot.symm
    have hcapZ : P.comap (Int.castRingHom R) = Ideal.span ({(p : ℤ)} : Set ℤ) := by
      have H1 : Ideal.span ({(p : ℤ)} : Set ℤ) ≤ P.comap (Int.castRingHom R) := by
        rw [← hηP]
        apply le_comap_of_map_le _
        rw [map_span]
        simp only [eq_intCast, Set.image_singleton, Int.cast_natCast]
        rw [span_singleton_le_span_singleton, ← neg_sub, neg_dvd]
        have hprimroot : IsPrimitiveRoot ((η₁ : R) : K) p :=
          IsPrimitiveRoot.coe_submonoidClass_iff.mpr
            (isPrimitiveRoot_of_mem_nthRootsFinset' hη₁ hwlog)
        have hdvd := @IsPrimitiveRoot.toInteger_sub_one_dvd_prime' p K _ _ _ _
          (CyclotomicField.isCyclotomicExtension p ℚ) hprimroot
        have key : hprimroot.toInteger = η₁ := by ext; rfl
        rwa [key] at hdvd
      have H2 : IsPrime (P.comap (Int.castRingHom R)) := IsPrime.comap _
      have H4 : Ideal.span ({(p : ℤ)} : Set ℤ) ≠ ⊥ := by simp [NeZero.ne p]
      apply ((@Ring.DimensionLeOne.prime_le_prime_iff_eq _ _ _ _ _ H5 H2 H4).1 H1).symm
    have hxyinP : (x + y : R) ∈ P := by
      have H1 : (x : R) + η₁ * y ∈ P := by
        apply hiP
        apply Submodule.mem_span_singleton_self
      have H2 : η₁ * y = y - y * (1 - η₁) := by ring
      rw [H2] at H1
      have H3 : ↑x + (↑y - ↑y * (1 - η₁)) = ↑x + ↑y + -↑y * (1 - η₁) := by ring
      rw [H3] at H1
      have H4 : -↑y * (1 - η₁) ∈ P := by
        rw [← hηP, Ideal.mem_span_singleton']
        exact ⟨-(y : R), rfl⟩
      apply (Ideal.add_mem_iff_left P H4).1 H1
    have hxyinP2 : x + y ∈ Ideal.span ({(p : ℤ)} : Set ℤ) := by
      rw [← hcapZ]
      simp [hxyinP]
    rw [mem_span_singleton] at hxyinP2
    apply absurd hxyinP2 hp2
  rcases hprime2 with hprime2 | hprime2
  · rcases hprime3 with hprime3 | hprime3
    · obtain ⟨a, b, hab⟩ := hp
      have hone := P.add_mem (Ideal.mul_mem_left P a hprime3) (Ideal.mul_mem_left P b hprime2)
      norm_cast at hone
      rw [hab] at hone
      norm_cast at hone
      rw [← eq_top_iff_one] at hone
      have hcontra := IsPrime.ne_top hPrime
      rw [hone] at hcontra
      simp only [Ne, not_true] at hcontra
    apply HC hprime3
  · apply HC hprime2

variable [Fact p.Prime] in

theorem fltIdeals_coprime2 (ph : 5 ≤ p) {x y : ℤ} {η₁ η₂ : R}
    (hη₁ : η₁ ∈ nthRootsFinset p (1 : R)) (hη₂ : η₂ ∈ nthRootsFinset p (1 : R))
    (hdiff : η₁ ≠ η₂) (hp : IsCoprime x y) (hp2 : ¬(p : ℤ) ∣ (x + y : ℤ))
    (hwlog : η₁ ≠ 1) :
    IsCoprime (fltIdeals x y hη₁) (fltIdeals x y hη₂) := by
  rw [Ideal.isCoprime_iff_add]
  simpa using fltIdeals_coprime2_lemma ph hη₁ hη₂ hdiff hp hp2 hwlog

variable [Fact p.Prime] in

theorem fltIdeals_coprime (p5 : 5 ≤ p) {x y z : ℤ} (H : x ^ p + y ^ p = z ^ p)
    {η₁ η₂ : R} (hxy : IsCoprime x y) (hη₁ : η₁ ∈ nthRootsFinset p (1 : R))
    (hη₂ : η₂ ∈ nthRootsFinset p (1 : R)) (hdiff : η₁ ≠ η₂)
    (caseI : ¬↑p ∣ x * y * z) :
    IsCoprime (fltIdeals x y hη₁) (fltIdeals x y hη₂) := by
  by_cases h : η₁ ≠ 1
  · exact fltIdeals_coprime2 p5 hη₁ hη₂ hdiff hxy (aux_lem_flt H caseI) h
  · have h2 : η₂ ≠ 1 := by
      simp only [ne_eq, not_not] at h
      rw [h] at hdiff
      exact hdiff.symm
    exact (fltIdeals_coprime2 p5 hη₂ hη₁ hdiff.symm hxy (aux_lem_flt H caseI) h2).symm

end FltIdeals

section MoreLemmas

variable [hpri : Fact p.Prime] {K : Type*} [Field K] [CharZero K]
  [IsCyclotomicExtension {p} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

theorem exists_zeta_sub_one_dvd_sub_Int (a : 𝓞 K) :
    ∃ b : ℤ, (hζ.toInteger - 1 : 𝓞 K) ∣ a - b := by
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  simp_rw [← Ideal.Quotient.eq_zero_iff_dvd, ← Ideal.Quotient.mk_eq_mk, Submodule.Quotient.mk_sub,
    sub_eq_zero, ← SModEq.def]
  obtain ⟨n, hn⟩ := hζ.subOneIntegralPowerBasis.exists_smodEq a
  refine ⟨n, ?_⟩
  rw [hζ.subOneIntegralPowerBasis_gen] at hn
  exact hn

theorem exists_dvd_pow_sub_Int_pow (hp : p ≠ 2) (a : 𝓞 K) :
    ∃ b : ℤ, ↑p ∣ a ^ p - (b : 𝓞 K) ^ p := by
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  haveI := IsCyclotomicExtension.numberField {p} ℚ K
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ K
    (Set.mem_singleton p) hpri.1.ne_zero
  have hassoc : Associated ((hζ.toInteger - 1) ^ (p - 1)) ((p : ℕ) : 𝓞 K) := by
    haveI h0 : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
      simpa using (inferInstance : IsCyclotomicExtension {p} ℚ K)
    have hζ' : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
    have hmap := IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow p 0 hζ'
    rw [Ideal.map_span, Set.image_singleton] at hmap
    have hrank : Module.finrank ℚ K = p - 1 := by
      rw [IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat (NeZero.pos p)),
        totient_prime hpri.out]
    rw [hrank, Ideal.span_singleton_pow] at hmap
    have hkey : hζ'.toInteger = hζ.toInteger := by ext; rfl
    rw [hkey] at hmap
    have := Ideal.span_singleton_eq_span_singleton.mp hmap.symm
    simpa using this
  obtain ⟨b, k, e⟩ := exists_zeta_sub_one_dvd_sub_Int hζ a
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hpri.out a (-b)
  obtain ⟨u, hu⟩ := hassoc.symm
  rw [(Nat.Prime.odd_of_ne_two hpri.out hp).neg_pow, ← sub_eq_add_neg, e,
    mul_pow, ← sub_eq_add_neg] at hr
  use b, ↑u * ((hζ.toInteger - 1 : 𝓞 K) * k ^ p) - r * a * (-b)
  rw [← sub_eq_iff_eq_add.mpr hr, mul_sub, ← mul_assoc, ← mul_assoc, hu, ← pow_succ,
    Nat.sub_add_cancel (n := p) (m := 1) hpri.out.one_lt.le]
  ring

end MoreLemmas

section UnitLemmas

variable [NeZero p] {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

set_option quotPrecheck false in

local notation3 "ηu" => (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit

set_option quotPrecheck false in

local notation "Iη" => (Ideal.span ({(ηu - 1 : 𝓞 K)} : Set (𝓞 K)) : Ideal (𝓞 K))

private theorem eq_one_mod_one_sub {A : Type*} [CommRing A] {t : A} :
    algebraMap A (A ⧸ Ideal.span ({t - 1} : Set A)) t = 1 := by
  rw [← map_one <| algebraMap A <| A ⧸ Ideal.span ({t - 1} : Set A), ← sub_eq_zero, ← map_sub,
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

set_option backward.isDefEq.respectTransparency false in
omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
private theorem aux_sum_mod {t} {l : 𝓞 K} {f : Fin t → ℤ} {μ : K} (hμ : IsPrimitiveRoot μ p)
    (h : ∑ x : Fin t, f x • (⟨μ, hμ.isIntegral (NeZero.pos p)⟩ : 𝓞 K) ^ (x : ℕ) = l) :
    algebraMap (𝓞 K) (𝓞 K ⧸ Iη) l = ∑ x : Fin t, (f x : 𝓞 K ⧸ Iη) := by
  apply_fun algebraMap (𝓞 K) (𝓞 K ⧸ Iη) at h
  simp only [map_sum, map_zsmul] at h
  convert h.symm using 1
  congr
  funext x
  have : (⟨μ, hμ.isIntegral (NeZero.pos p)⟩ : 𝓞 K) ^ p = 1 := by
    ext
    push_cast
    exact hμ.pow_eq_one
  obtain ⟨k, -, hk⟩ := hζ.toInteger_isPrimitiveRoot.eq_pow_of_pow_eq_one this
  have : algebraMap (𝓞 K) (𝓞 K ⧸ Iη) (⟨μ, hμ.isIntegral (NeZero.pos p)⟩ : 𝓞 K) = 1 := by
    rw [← hk, map_pow]
    change (algebraMap (𝓞 K) (𝓞 K ⧸ Iη) (ηu : 𝓞 K)) ^ k = 1
    rw [eq_one_mod_one_sub, one_pow]
  simp only [map_pow (algebraMap (𝓞 K) (𝓞 K ⧸ Iη)), this, one_pow, zsmul_one]

set_option backward.isDefEq.respectTransparency false in
private theorem roots_of_unity_in_cyclo_aux {x : K} {l : ℕ} (hl : l ≠ 0) (hx : IsIntegral ℤ x)
    (hhl : (Polynomial.cyclotomic l (𝓞 K)).IsRoot ⟨x, hx⟩) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) : l ∣ 2 * p := by
  by_contra h
  have hpl' : IsPrimitiveRoot (⟨x, hx⟩ : 𝓞 K) l := by
    have nezero : NeZero (l : 𝓞 K) := by
      refine ⟨fun hzero ↦ ?_⟩
      simp only [Nat.cast_eq_zero, hl] at hzero
    rw [isRoot_cyclotomic_iff.symm]
    apply hhl
  have hpl : IsPrimitiveRoot x l := by
    have : (algebraMap (𝓞 K) K) ⟨x, hx⟩ = x := by rfl
    have h4 := IsPrimitiveRoot.map_of_injective hpl' (f := algebraMap (𝓞 K) K)
    rw [← this]
    apply h4
    apply IsFractionRing.injective
  have hirr : Irreducible (Polynomial.cyclotomic p ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (NeZero.pos p)
  have KEY := IsPrimitiveRoot.lcm_totient_le_finrank hpl hζ <|
    Polynomial.cyclotomic.irreducible_rat <| Nat.lcm_pos (Nat.zero_lt_of_ne_zero hl) (NeZero.pos p)
  have hrank := IsCyclotomicExtension.finrank K hirr
  rw [hrank] at KEY
  have pdivlcm : p ∣ Nat.lcm l p := Nat.dvd_lcm_right l p
  rcases pdivlcm with ⟨pdivlcm_w, pdivlcm_h⟩
  have ineq1 := Nat.totient_super_multiplicative p pdivlcm_w
  rw [← pdivlcm_h] at ineq1
  have KEY3 := (mul_le_iff_le_one_right (Nat.totient_pos.2 (NeZero.pos p))).mp (le_trans ineq1 KEY)
  have pdiv_ne_zero : 0 < pdivlcm_w := by
    by_contra h
    simp only [not_lt, le_zero_iff] at h
    rw [h] at pdivlcm_h
    simp only [MulZeroClass.mul_zero, Nat.lcm_eq_zero_iff] at pdivlcm_h
    rcases pdivlcm_h with h' | h'
    · exact hl h'
    · exact (NeZero.ne p) h'
  have K5 := (Nat.dvd_prime Nat.prime_two).1 (Nat.dvd_two_of_totient_le_one pdiv_ne_zero KEY3)
  rcases K5 with K5 | K5
  · rw [K5, mul_one] at pdivlcm_h
    have hlp2 : l ∣ p := pdivlcm_h ▸ Nat.dvd_lcm_left l p
    exact absurd (hlp2.trans (dvd_mul_left p 2)) h
  · rw [K5, mul_comm] at pdivlcm_h
    exact absurd (pdivlcm_h ▸ Nat.dvd_lcm_left l p) h

include hζ in

theorem roots_of_unity_in_cyclo (hpo : Odd p) (x : K)
    (h : ∃ (n : ℕ) (_ : 0 < n), x ^ n = 1) :
    ∃ (m k : ℕ), x = (-1) ^ k * ζ ^ m := by
  obtain ⟨n, hn0, hn⟩ := h
  have hx : IsIntegral ℤ x := by
    refine ⟨X ^ n - 1, ⟨?_, ?_⟩⟩
    · exact monic_X_pow_sub_C 1 hn0.ne'
    · simp only [hn, eval₂_one, eval₂_X_pow, eval₂_sub, sub_self]
  have hxu : (⟨x, hx⟩ : 𝓞 K) ^ n = 1 := by
    ext
    simp [hn]
  obtain ⟨l, hl, hhl⟩ := (_root_.isRoot_of_unity_iff hn0 _).1 hxu
  replace hl : l ≠ 0 := fun H ↦ by simp [H] at hl
  have hlp := roots_of_unity_in_cyclo_aux hl hx hhl hζ
  have isPrimRoot : IsPrimitiveRoot (hζ.toInteger) p := hζ.toInteger_isPrimitiveRoot
  have hxl : (⟨x, hx⟩ : 𝓞 K) ^ l = 1 := by
    apply Polynomial.isRoot_of_unity_of_root_cyclotomic _ hhl
    simp only [Nat.mem_divisors, dvd_refl, Ne, true_and]
    exact pos_iff_ne_zero.1 (Nat.pos_of_ne_zero hl)
  have hxp' : (⟨x, hx⟩ : 𝓞 K) ^ (2 * p) = 1 := by
    obtain ⟨w, hw⟩ := hlp
    rw [hw, pow_mul, hxl, one_pow]
  have hxp'' : (⟨x, hx⟩ : 𝓞 K) ^ p = 1 ∨ (⟨x, hx⟩ : 𝓞 K) ^ p = -1 := by
    rw [mul_comm, pow_mul] at hxp'
    exact eq_or_eq_neg_of_sq_eq_sq _ _ (by simpa only [one_pow] using hxp')
  rcases hxp'' with hxp'' | hxp''
  · obtain ⟨i, -, Hi⟩ := isPrimRoot.eq_pow_of_pow_eq_one hxp''
    refine ⟨i, 2, ?_⟩
    have hKi : ζ ^ i = x := by
      have h2 := congr_arg (algebraMap (𝓞 K) K) Hi
      rw [map_pow] at h2
      exact h2
    norm_num [← hKi]
  · have hone : (-1 : 𝓞 K) ^ p = (-1 : 𝓞 K) := Odd.neg_one_pow hpo
    have hxp3 : (-1 * ⟨x, hx⟩ : 𝓞 K) ^ p = 1 := by
      have h2 : (-1 * ⟨x, hx⟩ : 𝓞 K) = -⟨x, hx⟩ := neg_one_mul _
      rw [h2]
      exact (Odd.neg_pow hpo (⟨x, hx⟩ : 𝓞 K)).trans ((congrArg Neg.neg hxp'').trans (neg_neg (1 : 𝓞 K)))
    obtain ⟨i, -, Hi⟩ := isPrimRoot.eq_pow_of_pow_eq_one hxp3
    refine ⟨i, 1, ?_⟩
    have hKi : ζ ^ i = -x := by
      have h2 : hζ.toInteger.1 ^ i = -x := by
        have h4 := congrArg (algebraMap (𝓞 K) K) Hi
        rw [map_pow] at h4
        have h5 : (algebraMap (𝓞 K) K) (-1 * ⟨x, hx⟩) = -x :=
          (map_mul (algebraMap (𝓞 K) K) (-1) ⟨x, hx⟩).trans
            (by rw [map_neg, map_one]; exact neg_one_mul _)
        rw [h5] at h4
        exact h4
      rwa [IsPrimitiveRoot.coe_toInteger] at h2
    rw [hKi]
    ring

variable [Fact p.Prime] [NumberField.IsCMField K]

set_option backward.isDefEq.respectTransparency false in
private theorem unit_inv_conj_not_neg_zeta_runity_aux (u : (𝓞 K)ˣ) (_hp : 2 < p) :
    algebraMap (𝓞 K) (𝓞 K ⧸ Iη) (unitsMulComplexConjInv K u).1 = 1 := by
  have := Units.coe_map_inv (N := 𝓞 K ⧸ Iη) (algebraMap (𝓞 K) (𝓞 K ⧸ Iη))
    (unitsComplexConj K u)
  rw [unitsMulComplexConjInv_apply, Units.val_mul, _root_.map_mul, ← MonoidHom.coe_coe, ← this,
    Units.mul_inv_eq_one, Units.coe_map, MonoidHom.coe_coe]
  have hu := hζ.integralPowerBasis.basis.sum_repr u
  let a := hζ.integralPowerBasis.basis.repr
  let φn := hζ.integralPowerBasis.dim
  simp_rw [PowerBasis.basis_eq_pow, IsPrimitiveRoot.integralPowerBasis_gen] at hu
  have hu' := congr_arg (ringOfIntegersComplexConj K) hu
  replace hu' : ∑ x : Fin φn, (a u) x • (ringOfIntegersComplexConj K)
      (⟨ζ, hζ.isIntegral (NeZero.pos p)⟩ ^ (x : ℕ)) = unitsComplexConj K u := by
    refine Eq.trans ?_ hu'
    rw [map_sum]
    congr 1
    ext x
    congr 1
    rw [map_zsmul]
  have : ∀ x : Fin φn, ringOfIntegersComplexConj K (⟨ζ, hζ.isIntegral (NeZero.pos p)⟩ ^ (x : ℕ)) =
      ⟨ζ⁻¹, hζ.inv.isIntegral (NeZero.pos p)⟩ ^ (x : ℕ) := by
    intro x
    ext
    simp only [map_pow, coe_ringOfIntegersComplexConj, RingOfIntegers.map_mk, inv_pow]
    suffices ηu ∈ NumberField.Units.torsion K by
      have H := RingOfIntegers.ext_iff.1 <|
        Units.ext_iff.1 <| unitsComplexConj_torsion K ⟨ηu, ‹_›⟩
      have hcoe : ↑↑ηu = ζ := rfl
      simp only [Units.coe_mapEquiv, RingEquiv.coe_toMulEquiv, RingOfIntegers.mapRingEquiv_apply,
        hcoe, InvMemClass.coe_inv, map_units_inv] at H
      simp [show (complexConj K) ζ = ζ⁻¹ from H]
    refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2
      ⟨p, (Fact.out : p.Prime).pos, ?_⟩)
    ext
    exact hζ.pow_eq_one
  conv_lhs at hu' =>
    congr
    congr
    ext a
    rw [this a]
  exact (aux_sum_mod hζ hζ hu).trans (aux_sum_mod hζ hζ.inv hu').symm

set_option backward.isDefEq.respectTransparency false in
private theorem unit_inv_conj_not_neg_zeta_runity (u : (𝓞 K)ˣ) (n : ℕ) (hp : 2 < p) :
    u * (unitsComplexConj K u)⁻¹ ≠ -ηu ^ n := by
  by_contra H
  have hμ : algebraMap (𝓞 K) (𝓞 K ⧸ Iη) ((ηu : 𝓞 K) ^ n) = 1 := by
    have hpow : ((ηu : 𝓞 K) ^ n) ^ p = 1 := by
      change (hζ.toInteger ^ n) ^ p = 1
      rw [← pow_mul, mul_comm, pow_mul, hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
    obtain ⟨k, -, hk⟩ := hζ.toInteger_isPrimitiveRoot.eq_pow_of_pow_eq_one hpow
    rw [← hk, map_pow]
    change (algebraMap (𝓞 K) (𝓞 K ⧸ Iη) (ηu : 𝓞 K)) ^ k = 1
    rw [eq_one_mod_one_sub, one_pow]
  have hμ' : algebraMap (𝓞 K) (𝓞 K ⧸ Iη) ((ηu : 𝓞 K) ^ n) = -1 := by
    rw [← neg_eq_iff_eq_neg, ← map_neg, ← Units.val_pow_eq_pow_val, ← Units.val_neg, ← H]
    apply unit_inv_conj_not_neg_zeta_runity_aux hζ u hp
  have h2 : (2 : 𝓞 K) ∉ Iη := by
    intro hmem
    rw [Ideal.mem_span_singleton] at hmem
    haveI h0 : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
      simpa using (inferInstance : IsCyclotomicExtension {p} ℚ K)
    have hζ' : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
    refine hζ'.toInteger_sub_one_not_dvd_two (by omega) ?_
    have hkey : hζ'.toInteger = hζ.toInteger := by ext; rfl
    rw [hkey]
    exact hmem
  apply h2
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat, ← one_add_one_eq_two, ← neg_eq_iff_add_eq_zero]
  exact hμ'.symm.trans hμ

theorem unit_inv_conj_is_root_of_unity (u : (𝓞 K)ˣ) (hp : 2 < p) :
    ∃ m : ℕ, u * (unitsComplexConj K u)⁻¹ =
      ((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit ^ m) ^ 2 := by
  have hpo : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp.ne'
  haveI : NormedAlgebra ℚ ℂ := normedAlgebraRat
  have hfin :=
    @NumberField.Embeddings.pow_eq_one_of_norm_eq_one K _ _ ℂ _ _ _
      (u * (unitsComplexConj K u)⁻¹ : K) ?_ ?_
  · have H := roots_of_unity_in_cyclo hζ hpo (u * (unitsComplexConj K u)⁻¹ : K) hfin
    obtain ⟨n, k, hz⟩ := H
    simp_rw [← pow_mul]
    rcases Nat.even_or_odd k with hk | hk
    · simp only [hk.neg_one_pow, one_mul] at hz
      have hz' : u * (unitsComplexConj K u)⁻¹ = ηu ^ n := by
        ext
        exact hz
      rw [hz']
      refine ⟨n * ((p + 1) / 2), ?_⟩
      have hord : (ηu : (𝓞 K)ˣ) ^ p = 1 := by
        ext
        push_cast
        exact hζ.pow_eq_one
      have h2 : (p + 1) / 2 * 2 = p + 1 := Nat.div_mul_cancel hpo.add_one.two_dvd
      rw [mul_assoc, h2, mul_add, mul_one, pow_add, mul_comm n p, pow_mul, hord, one_pow,
        one_mul]
    · simp only [hk.neg_one_pow, neg_mul, one_mul] at hz
      have hz' : u * (unitsComplexConj K u)⁻¹ = -ηu ^ n := by
        ext
        exact hz
      exact absurd hz' (unit_inv_conj_not_neg_zeta_runity hζ u n hp)
  · apply RingHom.IsIntegralElem.mul
    · exact NumberField.RingOfIntegers.isIntegral_coe _
    · exact NumberField.RingOfIntegers.isIntegral_coe _
  · simp

theorem exists_int_sum_eq_zero
    (x y i : ℤ) {u : (𝓞 K)ˣ} {α : 𝓞 K}
    (h : (x : 𝓞 K) + y * ((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit ^ i :
      (𝓞 K)ˣ) = u * α ^ p) (hp : 2 < p) :
    ∃ k : ℤ, (x : 𝓞 K) + y * ((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit ^ i :
        (𝓞 K)ˣ) -
      ((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit ^ (2 * k) : (𝓞 K)ˣ) *
        (x + y * ((hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit ^ (-i) :
          (𝓞 K)ˣ)) ∈
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  set ζu : (𝓞 K)ˣ := (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit with hζu

  have hconj_pow : (α ^ p - ringOfIntegersComplexConj K (α ^ p)) ∈
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
    obtain ⟨a, ha⟩ := exists_int_sub_pow_prime_dvd (p := p) α
    rw [mem_span_singleton] at ha ⊢
    obtain ⟨γ, hγ⟩ := ha
    rw [sub_eq_iff_eq_add] at hγ
    rw [hγ, _root_.map_add, _root_.map_mul, map_natCast, map_intCast,
      add_sub_add_right_eq_sub, ← mul_sub]
    exact dvd_mul_right _ _

  have haux : ringOfIntegersComplexConj K ((x : 𝓞 K) + y * (ζu ^ i : (𝓞 K)ˣ)) =
      (x : 𝓞 K) + y * (ζu ^ (-i) : (𝓞 K)ˣ) := by
    ext1
    simp only [_root_.map_add, map_intCast, _root_.map_mul, coe_ringOfIntegersComplexConj,
      zpow_neg, map_units_inv, add_right_inj, _root_.mul_eq_mul_left_iff, Int.cast_eq_zero]
    simp_rw [NumberField.Units.coe_zpow]
    left
    simp only [map_zpow₀]
    rw [← inv_zpow]
    congr
    suffices ζu ∈ NumberField.Units.torsion K by
      have H := RingOfIntegers.ext_iff.1 <|
          Units.ext_iff.1 <| unitsComplexConj_torsion K ⟨ζu, ‹_›⟩
      have hcoe : ↑↑ζu = ζ := rfl
      simp only [Units.coe_mapEquiv, RingEquiv.coe_toMulEquiv, RingOfIntegers.mapRingEquiv_apply,
        hcoe, InvMemClass.coe_inv, map_units_inv] at H
      have h' : (algebraMap (𝓞 K) K) ↑ζu = ζ := rfl
      rw [h']
      exact H
    refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2
      ⟨p, (Fact.out : p.Prime).pos, ?_⟩)
    ext
    exact hζ.pow_eq_one

  obtain ⟨m, H⟩ := unit_inv_conj_is_root_of_unity hζ u hp
  refine ⟨m, ?_⟩
  have hz : ((ζu ^ m) ^ 2 : (𝓞 K)ˣ) = (ζu ^ (2 * (m : ℤ)) : (𝓞 K)ˣ) := by
    rw [← zpow_natCast (ζu ^ m) 2, ← zpow_natCast ζu m, ← zpow_mul]
    norm_num [mul_comm]
  rw [← hz, ← haux, h, ← H, Units.val_mul, mul_assoc, ← mul_sub]
  convert Ideal.mul_mem_left _ ↑u hconj_pow using 3
  ext
  simp

end UnitLemmas

end FltRegular

end Port_FLT_Deep_Regular_CyclotomicFarm_lean

section Port_FLT_Deep_Regular_CoeffFarm_lean

open Finset Nat Finset.Nat Int Finset.Int

open scoped NumberField

namespace FltRegular
namespace CaseI

variable {p : ℕ} (hpri : p.Prime)

local notation "K" => CyclotomicField p ℚ
local notation "R" => 𝓞 K

include hpri in

theorem aux0k₁ {a b c : ℤ} {ζ : R} (hp5 : 5 ≤ p) (hζ : IsPrimitiveRoot ζ p)
    (caseI : ¬↑p ∣ a * b * c) {k₁ k₂ : Fin p} (hcong : k₂ ≡ k₁ - 1 [ZMOD p])
    (hdiv : ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ)) :
    0 ≠ (k₁ : ℕ) := by
  symm
  intro habs
  rw [show (k₁ : ℤ) = 0 by simpa using habs, zero_sub] at hcong
  rw [habs, _root_.pow_zero, mul_one, add_sub_cancel_left, aux_cong0k₁ hpri hcong] at hdiv
  nth_rw 1 [show ζ = ζ ^ ((⟨1, hpri.one_lt⟩ : Fin p) : ℕ) by simp] at hdiv
  have key : ↑(p : ℤ) ∣ ∑ j ∈ range p, f0k₁ b p j • ζ ^ j := by
    convert hdiv using 1
    all_goals try rfl
    have h : 1 ≠ p.pred := fun h => by
      have := Nat.pred_eq_succ_iff.1 h.symm
      omega
    simp_rw [f0k₁, ite_smul, sum_ite, filter_filter, ← Ne.eq_def, ne_and_eq_iff_right h,
      Finset.range_filter_eq]
    simp [hpri.one_lt, Nat.sub_lt hpri.pos, sub_eq_add_neg]
  rw [sum_range] at key
  refine caseI (Dvd.dvd.mul_right (Dvd.dvd.mul_left ?_ _) _)
  haveI : NeZero p := ⟨hpri.ne_zero⟩
  haveI : Fact p.Prime := ⟨hpri⟩
  haveI : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
  simpa [f0k₁] using hζ.int_dvd_coeff_of_dvd_sum (auxf0k₁ hp5 b) key ⟨1, hpri.one_lt⟩

include hpri in

theorem aux0k₂ {a b : ℤ} {ζ : R} (hp5 : 5 ≤ p) (hζ : IsPrimitiveRoot ζ p)
    (hab : ¬a ≡ b [ZMOD p]) {k₁ k₂ : Fin p} (hcong : k₂ ≡ k₁ - 1 [ZMOD p])
    (hdiv : ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ)) :
    (0 : ℕ) ≠ ↑k₂ := by
  symm
  intro habs
  replace hcong := hcong.symm
  rw [show (k₂ : ℤ) = 0 by simpa using habs, ← ZMod.intCast_eq_intCast_iff, Int.cast_sub,
    Int.cast_zero, sub_eq_zero, ZMod.intCast_eq_intCast_iff] at hcong
  rw [habs, _root_.pow_zero, mul_one, aux_cong0k₂ hpri hcong, Fin.val_mk, pow_one,
    add_sub_assoc, ← sub_mul, add_sub_right_comm,
    show ζ = ζ ^ ((⟨1, hpri.one_lt⟩ : Fin p) : ℕ) by simp] at hdiv
  have key : ↑(p : ℤ) ∣ ∑ j ∈ range p, f0k₂ a b j • ζ ^ j := by
    convert hdiv using 1
    all_goals try rfl
    simp_rw [f0k₂, ite_smul, sum_ite, filter_filter, ← Ne.eq_def,
      ne_and_eq_iff_right zero_ne_one, Finset.range_filter_eq]
    simp only [hpri.pos, hpri.one_lt, if_true, zsmul_eq_mul, Int.cast_sub, sum_singleton,
      _root_.pow_zero, mul_one, pow_one, Ne, zero_smul, sum_const_zero, add_zero]
  rw [sum_range] at key
  refine hab ?_
  symm
  rw [← ZMod.intCast_eq_intCast_iff, ZMod.intCast_eq_intCast_iff_dvd_sub]
  haveI : NeZero p := ⟨hpri.ne_zero⟩
  haveI : Fact p.Prime := ⟨hpri⟩
  haveI : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
  simpa [f0k₂] using hζ.int_dvd_coeff_of_dvd_sum (auxf0k₂ hp5 a b) key ⟨0, hpri.pos⟩

include hpri in

theorem aux1k₁ {a b : ℤ} {ζ : R} (hp5 : 5 ≤ p) (hζ : IsPrimitiveRoot ζ p)
    (hab : ¬a ≡ b [ZMOD p]) {k₁ k₂ : Fin p} (hcong : k₂ ≡ k₁ - 1 [ZMOD p])
    (hdiv : ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ)) :
    (1 : ℕ) ≠ k₁ := by
  intro habs
  have h := aux0k₂ hpri hp5 hζ hab hcong hdiv
  rw [show (k₁ : ℤ) = 1 by simpa using habs.symm, sub_self] at hcong
  have := aux_cong1k₁ hpri hcong
  simp only [← Fin.val_eq_val] at this
  exact h.symm this

include hpri in

theorem aux1k₂ {a b c : ℤ} {ζ : R} (hp5 : 5 ≤ p) (hζ : IsPrimitiveRoot ζ p)
    (caseI : ¬↑p ∣ a * b * c) {k₁ k₂ : Fin p} (hcong : k₂ ≡ k₁ - 1 [ZMOD p])
    (hdiv : ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ)) :
    (1 : ℕ) ≠ k₂ := by
  symm
  intro habs
  replace hcong := hcong.symm
  rw [show (k₂ : ℤ) = 1 by simpa using habs, ← ZMod.intCast_eq_intCast_iff, Int.cast_sub,
    sub_eq_iff_eq_add, ← Int.cast_add, ZMod.intCast_eq_intCast_iff] at hcong
  rw [habs, pow_one, aux_cong1k₂ hpri hp5 hcong] at hdiv
  ring_nf at hdiv
  have key : ↑(p : ℤ) ∣ ∑ j ∈ range p, f1k₂ a j • ζ ^ j := by
    suffices h : ∑ j ∈ range p, f1k₂ a j • ζ ^ j = ↑a - ↑a * ζ ^ 2 by
      rwa [h]
    simp_rw [f1k₂, ite_smul, sum_ite, filter_filter, ← Ne.eq_def, ne_and_eq_iff_right
      (show 0 ≠ 2 by norm_num), Finset.range_filter_eq]
    simp only [hpri.pos, ite_true, zsmul_eq_mul, sum_singleton, _root_.pow_zero, mul_one,
      two_lt hp5, neg_smul, sum_neg_distrib, ne_eq, zero_smul, sum_const_zero, add_zero]
    ring
  rw [sum_range] at key
  refine caseI (Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _)
  haveI : NeZero p := ⟨hpri.ne_zero⟩
  haveI : Fact p.Prime := ⟨hpri⟩
  haveI : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
  simpa [f1k₂] using hζ.int_dvd_coeff_of_dvd_sum (auxf1k₂ hpri a) key ⟨0, hpri.pos⟩

end FltRegular.CaseI

end Port_FLT_Deep_Regular_CoeffFarm_lean

section Port_FLT_Deep_Regular_CaseIChain_lean

open Finset Nat Finset.Nat IsCyclotomicExtension Ideal Polynomial Int Finset.Int FltRegularPort.Internal.FltRegular.CaseI

open scoped NumberField

namespace FltRegular

variable {p : ℕ}

namespace CaseI

def SlightlyEasier : Prop :=
  ∀ ⦃a b c : ℤ⦄ {p : ℕ} [Fact p.Prime], IsRegularPrime p → 5 ≤ p →
    ({a, b, c} : Finset ℤ).gcd id = 1 → ¬a ≡ b [ZMOD p] → ¬↑p ∣ a * b * c →
    a ^ p + b ^ p ≠ c ^ p

def Statement : Prop :=
  ∀ ⦃a b c : ℤ⦄ {p : ℕ} [Fact p.Prime], IsRegularPrime p →
    ({a, b, c} : Finset ℤ).gcd id = 1 → ¬↑p ∣ a * b * c →
    a ^ p + b ^ p ≠ c ^ p

theorem may_assume : SlightlyEasier → Statement := by
  intro Heasy a b c p hpri hreg hgcd hI H
  have hodd : p ≠ 2 := by
    rintro rfl
    refine hI <| Dvd.dvd.mul_left ?_ _
    simp only [Nat.cast_ofNat, ← even_iff_two_dvd] at hI ⊢
    rw [Int.not_even_iff_odd] at hI
    rw [← Int.even_pow' two_ne_zero, ← H]
    exact (Odd.of_mul_left (Odd.of_mul_left hI)).pow.add_odd
      (Odd.of_mul_right (Odd.of_mul_left hI)).pow
  have hprod : a * b * c ≠ 0 := by
    intro h
    simp [h] at hI
  have hp5 : 5 ≤ p := by
    by_contra! habs
    have : 2 < p := Nat.lt_of_le_of_ne hpri.out.two_le hodd.symm
    interval_cases p
    · exact fermatLastTheoremFor_iff_int.1 fermatLastTheoremThree a b c
        (fun ha ↦ hprod <| by simp [ha]) (fun hb ↦ hprod <| by simp [hb])
        (fun hc ↦ hprod <| by simp [hc]) H
    · exact Nat.not_prime_mul one_lt_two.ne' one_lt_two.ne' hpri.out
  obtain ⟨_, _, _, H1, H2, H3, _, H5⟩ := MayAssume.a_not_cong_b hpri.out hp5 hprod H hgcd hI
  exact Heasy hreg hp5 H2 H3 H5 H1

end CaseI

theorem ab_coprime {a b c : ℤ} (H : a ^ p + b ^ p = c ^ p) (hpzero : p ≠ 0)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) : IsCoprime a b := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra! h
  obtain ⟨q, hqpri, hq⟩ := exists_prime_and_dvd h
  replace hqpri : Prime (q : ℤ) := Int.prime_iff_natAbs_prime.2 (by simp [hqpri])
  obtain ⟨n, hn⟩ := hq
  have haq : ↑q ∣ a := by
    obtain ⟨m, hm⟩ := Int.gcd_dvd_left (a := a) (b := b)
    exact ⟨n * m, by rw [hm, hn]; simp [mul_assoc]⟩
  have hbq : ↑q ∣ b := by
    obtain ⟨m, hm⟩ := Int.gcd_dvd_right (a := a) (b := b)
    exact ⟨n * m, by rw [hm, hn]; simp [mul_assoc]⟩
  have hcq : ↑q ∣ c :=
    hqpri.dvd_of_dvd_pow (H ▸ dvd_add (dvd_pow haq hpzero) (dvd_pow hbq hpzero))
  have Hq : ↑q ∣ ({a, b, c} : Finset ℤ).gcd id := by
    refine dvd_gcd fun x hx ↦ ?_
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with (H | H | H) <;> simpa [H]
  rw [hgcd] at Hq
  exact hqpri.not_unit (isUnit_of_dvd_one Hq)

def f (a b : ℤ) (k₁ k₂ : ℕ) : ℕ → ℤ := fun x =>
  if x = 0 then a else if x = 1 then b else if x = k₁ then -a else if x = k₂ then -b else 0

theorem auxf' (hp5 : 5 ≤ p) (a b : ℤ) (k₁ k₂ : Fin p) :
    ∃ i ∈ range p, f a b k₁ k₂ (i : ℕ) = 0 := by
  have h0 : 0 < p := by linarith
  have h1 : 1 < p := by linarith
  let s := ({0, 1, k₁.1, k₂.1} : Finset ℕ)
  have : s.card ≤ 4 := by
    repeat refine le_trans (card_insert_le _ _) (succ_le_succ ?_)
    exact rfl.ge
  replace this : s.card < 5 := lt_of_le_of_lt this (by norm_num)
  have hs : s ⊆ range p := insert_subset_iff.2 ⟨mem_range.2 h0, insert_subset_iff.2
    ⟨mem_range.2 h1, insert_subset_iff.2 ⟨mem_range.2 (Fin.is_lt _),
    singleton_subset_iff.2 (mem_range.2 (Fin.is_lt _))⟩⟩⟩
  have hcard := card_sdiff_of_subset hs
  replace hcard : (range p \ s).Nonempty := by
    rw [← Finset.card_pos, hcard, card_range]
    exact Nat.sub_pos_of_lt (lt_of_lt_of_le this hp5)
  obtain ⟨i, hi⟩ := hcard
  refine ⟨i, sdiff_subset hi, ?_⟩
  have hi0 : i ≠ 0 := fun h => by simp [h, s] at hi
  have hi1 : i ≠ 1 := fun h => by simp [h, s] at hi
  have hik₁ : i ≠ k₁ := fun h => by simp [h, s] at hi
  have hik₂ : i ≠ k₂ := fun h => by simp [h, s] at hi
  simp [f, hi0, hi1, hik₁, hik₂]

theorem auxf (hp5 : 5 ≤ p) (a b : ℤ) (k₁ k₂ : Fin p) :
    ∃ i : Fin p, f a b k₁ k₂ (i : ℕ) = 0 := by
  obtain ⟨i, hrange, hi⟩ := auxf' hp5 a b k₁ k₂
  exact ⟨⟨i, mem_range.1 hrange⟩, hi⟩

local notation "K" => CyclotomicField p ℚ
local notation "R" => 𝓞 K

theorem is_principal_aux {K' : Type*} [Field K'] [CharZero K'] [IsCyclotomicExtension {p} ℚ K']
    [Fintype (ClassGroup (𝓞 K'))]
    {a b : ℤ} {ζ : 𝓞 K'} (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K'))
    {I : Ideal (𝓞 K')} (hI : span ({↑a + ζ * ↑b} : Set (𝓞 K')) = I ^ p) :
    ∃ (u : (𝓞 K')ˣ) (α : 𝓞 K'), ↑u * α ^ p = ↑a + ζ * ↑b := by
  haveI : NumberField K' := IsCyclotomicExtension.numberField {p} ℚ K'
  obtain ⟨α, hα⟩ : I.IsPrincipal := by
    apply isPrincipal_of_isPrincipal_pow_of_coprime hreg
    exact ⟨⟨↑a + ζ * ↑b, by rw [submodule_span_eq, hI]⟩⟩
  replace hα := congr_arg (fun (J : Submodule _ _) => J ^ p) hα
  simp only [← hI, submodule_span_eq, span_singleton_pow, span_singleton_eq_span_singleton] at hα
  obtain ⟨u, hu⟩ := hα
  refine ⟨u⁻¹, α, ?_⟩
  rw [← hu, mul_comm ((_ + ζ * _)), Units.inv_mul_cancel_left]

variable [hpri : Fact p.Prime]

set_option backward.isDefEq.respectTransparency false in

theorem exists_ideal {a b c : ℤ} (h5p : 5 ≤ p) (H : a ^ p + b ^ p = c ^ p)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (caseI : ¬↑p ∣ a * b * c) {ζ : R} (hζ : ζ ∈ nthRootsFinset p (1 : R)) :
    ∃ I, span ({a + ζ * b} : Set R) = I ^ p := by
  classical
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨by exact_mod_cast hpri.out.ne_zero⟩
  have H₁ := congr_arg (@Int.cast R _) H
  simp only [Int.cast_add, Int.cast_pow] at H₁
  have hζ' := (zeta_spec p ℚ K).toInteger_isPrimitiveRoot
  rw [hζ'.pow_add_pow_eq_prod_add_mul _ _ <|
    odd_iff.2 <| hpri.1.eq_two_or_odd.resolve_left fun h ↦ by simp [h] at h5p] at H₁
  replace H₁ := congr_arg (fun x => span ({ x } : Set R)) H₁
  simp only [← prod_span_singleton, ← span_singleton_pow] at H₁
  refine exists_eq_pow_of_mul_eq_pow_of_coprime (fun η₁ hη₁ η₂ hη₂ hη => ?_) H₁ ζ
    hζ
  exact fltIdeals_coprime h5p H (ab_coprime H hpri.out.ne_zero hgcd) hη₁ hη₂ hη caseI

set_option backward.isDefEq.respectTransparency false in

theorem is_principal {a b c : ℤ} {ζ : R} (hreg : IsRegularPrime p) (hp5 : 5 ≤ p)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) (caseI : ¬↑p ∣ a * b * c)
    (H : a ^ p + b ^ p = c ^ p) (hζ : IsPrimitiveRoot ζ p) :
    ∃ (u : Rˣ) (α : R), ↑u * α ^ p = ↑a + ζ * ↑b := by
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨by exact_mod_cast hpri.out.ne_zero⟩
  replace hζ := hζ.mem_nthRootsFinset hpri.out.pos
  obtain ⟨I, hI⟩ := exists_ideal hp5 H hgcd caseI hζ
  exact is_principal_aux hreg hI

theorem ex_fin_div {a b c : ℤ} {ζ : R} (hp5 : 5 ≤ p) (hreg : IsRegularPrime p)
    (hζ : IsPrimitiveRoot ζ p) (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (caseI : ¬↑p ∣ a * b * c) (H : a ^ p + b ^ p = c ^ p) :
    ∃ k₁ k₂ : Fin p,
      k₂ ≡ k₁ - 1 [ZMOD p] ∧
        ↑p ∣ ↑a + ↑b * ζ - ↑a * ζ ^ (k₁ : ℕ) - ↑b * ζ ^ (k₂ : ℕ) := by
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨by exact_mod_cast hpri.out.ne_zero⟩
  haveI : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, by omega⟩
  let ζ' := (ζ : K)
  have hζ' : IsPrimitiveRoot ζ' p := IsPrimitiveRoot.coe_submonoidClass_iff.2 hζ
  let zetaUnit := (hζ'.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit
  have h : ζ = (zetaUnit : R) := by rfl
  have hP : p ≠ 2 := by
    intro hP
    rw [hP] at hp5
    contradiction
  obtain ⟨u, α, hu⟩ := is_principal hreg hp5 hgcd caseI H hζ
  rw [h, mul_comm _ (↑b : R), ← pow_one zetaUnit] at hu
  obtain ⟨k, hk⟩ := exists_int_sum_eq_zero hζ' a b 1 hu.symm (by omega)
  simp only [zpow_one, zpow_neg, mem_span_singleton] at hk
  have hpcoe : (p : ℤ) ≠ 0 := by simp [hpri.out.ne_zero]
  have hζ_map : (algebraMap R K) ζ = ζ' := rfl
  refine ⟨⟨(2 * k % p).natAbs, ?_⟩, ⟨((2 * k - 1) % p).natAbs, ?_⟩, ?_, ?_⟩
  repeat'
    rw [← natAbs_natCast p]
    refine natAbs_lt_natAbs_of_nonneg_of_lt (emod_nonneg _ hpcoe) ?_
    rw [natAbs_natCast]
    exact emod_lt_of_pos _ (by simp [hpri.out.pos])
  · simp only [natAbs_of_nonneg (emod_nonneg _ hpcoe), ← ZMod.intCast_eq_intCast_iff,
      ZMod.intCast_mod, Int.cast_sub, Int.cast_mul, Int.cast_one]
  simp only [add_sub_assoc, sub_sub] at hk ⊢
  convert hk using 3
  all_goals try exact congrArg _ h
  rw [mul_add, mul_comm (↑a : R), ← mul_assoc _ (↑b : R), mul_comm _ (↑b : R),
    mul_assoc (↑b : R)]
  congr 2
  · ext
    simp only [map_pow, NumberField.Units.coe_zpow, hζ_map]
    change ζ' ^ ↑(2 * k % ↑p).natAbs = ζ' ^ (2 * k)
    refine eq_of_div_eq_one ?_
    rw [← zpow_natCast, ← zpow_sub₀ (hζ'.ne_zero hpri.out.ne_zero), hζ'.zpow_eq_one_iff_dvd]
    simp only [natAbs_of_nonneg (emod_nonneg _ hpcoe), ← ZMod.intCast_zmod_eq_zero_iff_dvd,
      Int.cast_sub, ZMod.intCast_mod, Int.cast_mul, sub_self]
  · ext
    simp only [map_pow, _root_.map_mul, NumberField.Units.coe_zpow, map_units_inv, hζ_map]
    change ζ' ^ ↑((2 * k - 1) % ↑p).natAbs = ζ' ^ (2 * k) * ζ'⁻¹
    refine eq_of_div_eq_one ?_
    rw [← zpow_natCast, ← zpow_sub_one₀ (hζ'.ne_zero hpri.out.ne_zero), ←
      zpow_sub₀ (hζ'.ne_zero hpri.out.ne_zero), hζ'.zpow_eq_one_iff_dvd]
    simp only [natAbs_of_nonneg (emod_nonneg _ hpcoe), ← ZMod.intCast_zmod_eq_zero_iff_dvd,
      Int.cast_sub, ZMod.intCast_mod, Int.cast_mul, Int.cast_one, sub_self]

set_option backward.isDefEq.respectTransparency false in

theorem caseI_easier {a b c : ℤ} (hreg : IsRegularPrime p) (hp5 : 5 ≤ p)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) (hab : ¬a ≡ b [ZMOD p])
    (caseI : ¬↑p ∣ a * b * c) :
    a ^ p + b ^ p ≠ c ^ p := by
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  haveI : NeZero ((p : ℕ) : ℚ) := ⟨by exact_mod_cast hpri.out.ne_zero⟩
  haveI : IsCyclotomicExtension {p} ℚ K := CyclotomicField.isCyclotomicExtension p ℚ
  set ζ : R := (zeta_spec p ℚ K).toInteger with hζ_def
  have hζ : IsPrimitiveRoot ζ p := (zeta_spec p ℚ K).toInteger_isPrimitiveRoot
  intro H
  obtain ⟨k₁, k₂, hcong, hdiv⟩ := ex_fin_div hp5 hreg hζ hgcd caseI H
  have key : ↑(p : ℤ) ∣ ∑ j ∈ range p, f a b k₁ k₂ j • ζ ^ j := by
    convert hdiv using 1
    all_goals try rfl
    have h01 : 0 ≠ 1 := zero_ne_one
    have h0k₁ := aux0k₁ hpri.out hp5 hζ caseI hcong hdiv
    have h0k₂ := aux0k₂ hpri.out hp5 hζ hab hcong hdiv
    have h1k₁ := aux1k₁ hpri.out hp5 hζ hab hcong hdiv
    have h1k₂ := aux1k₂ hpri.out hp5 hζ caseI hcong hdiv
    have hk₁k₂ : (k₁ : ℕ) ≠ (k₂ : ℕ) := auxk₁k₂ hpri.out hcong
    simp_rw [f, ite_smul, sum_ite, filter_filter, ← Ne.eq_def, ne_and_eq_iff_right h01, and_assoc,
      ne_and_eq_iff_right h1k₁, ne_and_eq_iff_right h0k₁, ne_and_eq_iff_right hk₁k₂,
      ne_and_eq_iff_right h1k₂, ne_and_eq_iff_right h0k₂, Finset.range_filter_eq]
    simp only [hpri.out.pos, hpri.out.one_lt, if_true, zsmul_eq_mul, sum_singleton,
      _root_.pow_zero, mul_one, pow_one, Fin.is_lt, neg_smul, sum_neg_distrib, Ne, zero_smul,
      sum_const_zero, add_zero]
    ring
  rw [sum_range] at key
  refine caseI (Dvd.dvd.mul_right (Dvd.dvd.mul_right ?_ _) _)
  exact hζ.int_dvd_coeff_of_dvd_sum (auxf hp5 a b k₁ k₂) key ⟨0, hpri.out.pos⟩

end FltRegular

end Port_FLT_Deep_Regular_CaseIChain_lean

section Port_FLT_Deep_Regular_CyclotomicRing_lean

noncomputable section

open Polynomial NumberField

open scoped NumberField

namespace FltRegular

variable (p : ℕ) [hpri : Fact p.Prime]

def CyclotomicIntegers : Type := AdjoinRoot (cyclotomic p ℤ)

scoped instance : CommRing (CyclotomicIntegers p) := by delta CyclotomicIntegers; infer_instance

set_option backward.isDefEq.respectTransparency false in
open Polynomial in
lemma IsPrimitiveRoot.cyclotomic_eq_minpoly
    (x : 𝓞 (CyclotomicField p ℚ)) (hx : IsPrimitiveRoot x.1 p) :
    minpoly ℤ x = cyclotomic p ℤ := by
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (RingHom.injective_int (algebraMap ℤ ℚ))
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions ℚ (CyclotomicField p ℚ)
    (IsIntegralClosure.isIntegral _ (CyclotomicField p ℚ) _),
    ← cyclotomic_eq_minpoly_rat (n := p) (hpos := hpri.out.pos), map_cyclotomic]
  exact hx

namespace CyclotomicIntegers

set_option backward.isDefEq.respectTransparency false in

@[simps! -isSimp]
def equiv :
    CyclotomicIntegers p ≃+* 𝓞 (CyclotomicField p ℚ) := by
  have H := IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)
  have hH : minpoly ℤ H.integralPowerBasis.gen = cyclotomic p ℤ :=
    H.integralPowerBasis_gen ▸ IsPrimitiveRoot.cyclotomic_eq_minpoly p H.toInteger H
  exact (AdjoinRoot.equiv' (cyclotomic p ℤ) H.integralPowerBasis
    (hH ▸ ((AdjoinRoot.aeval_eq _).trans AdjoinRoot.mk_self))
    (hH ▸ minpoly.aeval _ _)).toRingEquiv

scoped instance : IsDomain (CyclotomicIntegers p) :=
  AdjoinRoot.isDomain_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (cyclotomic.irreducible hpri.out.pos))

def zeta : CyclotomicIntegers p := AdjoinRoot.root _

set_option backward.isDefEq.respectTransparency false in
lemma equiv_zeta : equiv p (zeta p) = (IsCyclotomicExtension.zeta_spec
    p ℚ (CyclotomicField p ℚ)).toInteger := by
  simp [equiv_apply, zeta]

set_option backward.isDefEq.respectTransparency false in
lemma prime_one_sub_zeta :
    Prime (1 - zeta p) := by
  have H := IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)
  have h : Prime (zeta p - 1) := by
    apply (MulEquiv.prime_iff (equiv p).toMulEquiv).1
    show Prime (equiv p (zeta p - 1))
    simp only [(equiv p).map_sub, (equiv p).map_one, equiv_zeta]
    exact H.zeta_sub_one_prime'
  simpa only [neg_sub] using Prime.neg h

lemma one_sub_zeta_mem_nonZeroDivisors :
    1 - zeta p ∈ nonZeroDivisors (CyclotomicIntegers p) := by
  rw [mem_nonZeroDivisors_iff_ne_zero]
  exact (prime_one_sub_zeta p).1

lemma not_isUnit_one_sub_zeta :
    ¬ IsUnit (1 - zeta p) := (prime_one_sub_zeta p).irreducible.1

lemma one_sub_zeta_dvd_int_iff (n : ℤ) : 1 - zeta p ∣ n ↔ ↑p ∣ n := by
  have : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero p ℚ
  have H := IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)
  have key : H.toInteger - 1 ∣ (n : 𝓞 (CyclotomicField p ℚ)) ↔ (p : ℤ) ∣ n := by
    by_cases hodd : p = 2
    · subst hodd
      have h2 : Prime (Algebra.norm ℤ (H.toInteger - 1)) := by
        rw [H.norm_toInteger_sub_one_of_eq_two]
        exact Int.prime_iff_natAbs_prime.mpr (by simpa using Nat.prime_two)
      rw [← Ideal.norm_dvd_iff h2, H.norm_toInteger_sub_one_of_eq_two, neg_dvd]
      norm_num
    · rw [← Ideal.norm_dvd_iff (H.prime_norm_toInteger_sub_one_of_prime_ne_two' hodd),
        H.norm_toInteger_sub_one_of_prime_ne_two' hodd]
  rw [← map_dvd_iff (equiv p), map_sub, map_one, equiv_zeta, map_intCast, ← neg_dvd, neg_sub]
  exact key

lemma one_sub_zeta_dvd : 1 - zeta p ∣ p :=
  (one_sub_zeta_dvd_int_iff _ _).2 dvd_rfl

lemma isCoprime_one_sub_zeta (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) : IsCoprime (1 - zeta p) n :=
  (((Nat.prime_iff_prime_int.mp hpri.out).coprime_iff_not_dvd.mpr hn).map
    (algebraMap ℤ <| CyclotomicIntegers p)).of_isCoprime_of_dvd_left (one_sub_zeta_dvd p)

lemma exists_dvd_int (n : CyclotomicIntegers p) (hn : n ≠ 0) :
    ∃ m : ℤ, m ≠ 0 ∧ n ∣ m := by
  refine ⟨Algebra.norm ℤ ((equiv p) n), by simpa, ?_⟩
  rw [← map_dvd_iff (equiv p), map_intCast]
  have : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero p ℚ
  have : IsGalois ℚ (CyclotomicField p ℚ) := IsCyclotomicExtension.isGalois {p} _ _
  convert NumberField.RingOfIntegers.dvd_norm ℚ (equiv p n) using 1
  ext1
  exact DFunLike.congr_arg (algebraMap ℚ _) (Algebra.coe_norm_int (equiv p n))

def powerBasis : PowerBasis ℤ (CyclotomicIntegers p) :=
  AdjoinRoot.powerBasis' (cyclotomic.monic _ _)

lemma powerBasis_dim : (powerBasis p).dim = p - 1 := by
  simp [powerBasis, Nat.totient_prime hpri.out, natDegree_cyclotomic]

scoped instance : Module.Free ℤ (CyclotomicIntegers p) := ⟨_, (powerBasis p).basis⟩

lemma nontrivial {p} (hp : p ≠ 0) : Nontrivial (CyclotomicIntegers p) := by
  apply Ideal.Quotient.nontrivial_iff.mpr
  simp only [ne_eq, Ideal.span_singleton_eq_top]
  intro h
  have := natDegree_eq_zero_of_isUnit h
  rw [natDegree_cyclotomic] at this
  exact this.not_gt (Nat.totient_pos.2 <| Nat.zero_lt_of_ne_zero hp)

lemma charZero {p} (hp : p ≠ 0) : CharZero (CyclotomicIntegers p) :=
  have := nontrivial hp
  ⟨(FaithfulSMul.algebraMap_injective _ _).comp (algebraMap ℕ ℤ).injective_nat⟩

scoped instance : CharZero (CyclotomicIntegers p) := charZero hpri.out.ne_zero

end CyclotomicIntegers
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers

end FltRegular
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular

end
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular

end Port_FLT_Deep_Regular_CyclotomicRing_lean
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular

section Port_FLT_Deep_Regular_SystemOfUnits_lean

namespace FltRegular

open FiniteDimensional
open NumberField

variable (p : ℕ) {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {k : Type*} [Field k] [NumberField k] (hp : Nat.Prime p)

open Module Finset
open CyclotomicIntegers (zeta)

variable
  (G : Type*) {H : Type*} [AddCommGroup G] (s : ℕ)
  (hf : finrank ℤ G = s * (p - 1))

local notation "A" => (CyclotomicIntegers p)

section

variable [Module (CyclotomicIntegers p) G]

structure systemOfUnits (s : ℕ) where

  units : Fin s → G

  linearIndependent : LinearIndependent A units

namespace systemOfUnits

lemma existence0 : Nonempty (systemOfUnits p G 0) :=
  ⟨⟨fun _ ↦ 0, linearIndependent_empty_type⟩⟩

include hp

lemma finrank_spanA {R : ℕ} (f : Fin R → G) (hf : LinearIndependent A f) :
    finrank ℤ (Submodule.span A (Set.range f)) = (p - 1) * R := by
  classical
  have := Fact.mk hp
  have := finrank_span_set_eq_card (R := A) (s := Set.range f)
    ((linearIndepOn_id_range_iff hf.injective).mpr hf)
  simp only [Set.toFinset_range, Finset.card_image_of_injective _ hf.injective, card_fin] at this
  rw [← CyclotomicIntegers.powerBasis_dim, ← PowerBasis.finrank]
  conv_rhs => rw [← this]
  have := Module.Free.of_basis (Basis.span hf)
  have := Module.Finite.of_basis (Basis.span hf)
  rw [finrank_mul_finrank]

include hf

set_option backward.isDefEq.respectTransparency false in
lemma ex_not_mem [Module.Free ℤ G] {R : ℕ} (S : systemOfUnits p G R) (hR : R < s) :
    ∃ g, ∀ (k : ℤ), k ≠ 0 → ¬(k • g ∈ Submodule.span A (Set.range S.units)) := by
  have := Fact.mk hp
  have : Module.Finite ℤ G := Module.finite_of_finrank_pos
    (by simp [hf, R.zero_le.trans_lt hR, hp.one_lt])
  refine Submodule.exists_of_finrank_lt
    ((Submodule.span A (Set.range S.units)).restrictScalars ℤ) ?_
  change finrank ℤ (Submodule.span A _) < _
  rw [finrank_spanA p hp G S.units S.linearIndependent, hf, mul_comm]
  exact Nat.mul_lt_mul_of_lt_of_le hR rfl.le hp.pred_pos

end systemOfUnits
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular

end
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular

namespace systemOfUnits

include hp hf

variable [Module.Free ℤ G]

lemma existence' [Module A G] {R : ℕ} (S : systemOfUnits p G R) (hR : R < s) :
    Nonempty (systemOfUnits p G (R + 1)) := by
  obtain ⟨g, hg⟩ := ex_not_mem p hp G s hf S hR
  refine ⟨⟨Fin.cons g S.units, ?_⟩⟩
  refine LinearIndependent.finCons' g S.units S.linearIndependent (fun a y hy hay ↦ ?_)
  by_contra ha
  have := Fact.mk hp
  obtain ⟨n, h0, f, Hf⟩ := CyclotomicIntegers.exists_dvd_int p a ha
  have hy' := congr_arg (f • ·) hay
  simp only [smul_zero, smul_add, smul_smul] at hy'
  rw [mul_comm f, ← Hf, ← eq_neg_iff_add_eq_zero, Int.cast_smul_eq_zsmul] at hy'
  apply hg _ h0
  rw [hy']
  exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hy)

lemma existence'' [Module A G] {R : ℕ} (hR : R ≤ s) :
    Nonempty (systemOfUnits p G R) := by
  induction R with
  | zero => exact existence0 p G
  | succ n ih =>
      obtain ⟨S⟩ := ih (le_trans (Nat.le_succ n) hR)
      exact existence' p hp G s hf S (lt_of_lt_of_le (Nat.lt_add_one n) hR)

lemma existence [Module A G] : Nonempty (systemOfUnits p G s) := existence'' p hp G s hf rfl.le

end systemOfUnits
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular

end FltRegular
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular

end Port_FLT_Deep_Regular_SystemOfUnits_lean
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular

section Port_FLT_Deep_Regular_Hilbert92_lean

namespace FltRegular

open scoped NumberField nonZeroDivisors
open FiniteDimensional NumberField

variable {s r : ℕ} (p : ℕ) {K : Type*} [Field K]
variable {k : Type*} [Field k] (hp : Nat.Prime p)

open Module Finset
open CyclotomicIntegers (zeta)

section thm91
variable (G : Type*) [AddCommGroup G]

local notation3 "A" => CyclotomicIntegers p

abbrev systemOfUnits.IsMaximal {p : ℕ} {G : Type*} [AddCommGroup G]
    [Module (CyclotomicIntegers p) G] (sys : systemOfUnits (G := G) p s) :=
  Fintype (G ⧸ Submodule.span (CyclotomicIntegers p) (Set.range sys.units))

set_option backward.isDefEq.respectTransparency false in

@[reducible]
noncomputable
def systemOfUnits.isMaximal [Module.Finite ℤ G] (hf : finrank ℤ G = s * (p - 1))
  [Module A G] (sys : systemOfUnits (G := G) p s) : sys.IsMaximal := by
  apply Nonempty.some
  apply (@nonempty_fintype _ ?_)
  apply Module.finite_of_fg_torsion
  rw [← finrank_eq_zero_iff_isTorsion, Submodule.finrank_quotient,
    finrank_spanA p hp _ _ sys.linearIndependent, hf, mul_comm, Nat.sub_self]

noncomputable
def systemOfUnits.index [Module A G] (sys : systemOfUnits p G s) [sys.IsMaximal] :=
  Fintype.card (G ⧸ Submodule.span A (Set.range sys.units))

def systemOfUnits.IsFundamental [Module A G] (h : systemOfUnits p G s) :=
  ∃ _ : h.IsMaximal, ∀ (S : systemOfUnits p G s) (_ : S.IsMaximal), h.index ≤ S.index

lemma systemOfUnits.IsFundamental.maximal' [Module A G] (S : systemOfUnits p G r)
    (hs : S.IsFundamental) (a : systemOfUnits p G r) [a.IsMaximal] :
    (Submodule.span A (Set.range S.units)).toAddSubgroup.index ≤
      (Submodule.span A (Set.range a.units)).toAddSubgroup.index := by
  letI := hs.choose
  convert hs.choose_spec a ‹_› <;> symm <;> exact Nat.card_eq_fintype_card.symm
namespace systemOfUnits
namespace IsFundamental

variable {H : Type*} [CommGroup H] [Fintype H] (hCard : Fintype.card H = p)
  (σ : H) (hσ : Subgroup.zpowers σ = ⊤) (s : ℕ) [DistribMulAction H G]
  (hf : finrank ℤ G = s * (p - 1))

include hp hf

variable [Module.Finite ℤ G]

lemma existence [Module.Free ℤ G] [Module A G] :
    ∃ S : systemOfUnits p G s, S.IsFundamental := by
  obtain ⟨S⟩ := systemOfUnits.existence p hp G s hf
  letI := S.isMaximal p hp G hf
  have : { a | ∃ (S : systemOfUnits p G s) (_ : S.IsMaximal), a = S.index p G }.Nonempty :=
    ⟨S.index, S, S.isMaximal p hp G hf, rfl⟩
  obtain ⟨S', hS', ha⟩ := Nat.sInf_mem this
  use S', hS'
  intro a' ha'
  rw [← ha]
  apply csInf_le (OrderBot.bddBelow _)
  use a', ha'

lemma lemma2 [Module A G] (S : systemOfUnits p G s) (hs : S.IsFundamental)
    (i : Fin s) (a : Fin s →₀ A) (ha : a i = 1) :
    ∀ g : G, (1 - zeta p) • g ≠ Finsupp.linearCombination A S.units a := by
  cases s with
  | zero => exact isEmptyElim i
  | succ s =>
    intro g hg
    have := Fact.mk hp
    let S' : systemOfUnits p G (s + 1) := ⟨Function.update S.units i g,
      LinearIndependent.update S.linearIndependent i g ⟨_,
        CyclotomicIntegers.one_sub_zeta_mem_nonZeroDivisors p, a, ha ▸ one_mem A⁰, hg⟩⟩
    let a' := a.comapDomain (Fin.succAbove i) Fin.succAbove_right_injective.injOn
    have hS' : S'.units ∘ Fin.succAbove i = S.units ∘ Fin.succAbove i := by
      ext; simp only [Function.comp_apply, ne_eq, Fin.succAbove_ne, not_false_eq_true,
        Function.update_of_ne, S']
    have ha' : Finsupp.linearCombination A (S'.units ∘ Fin.succAbove i) a' + S.units i =
        (1 - zeta p) • g := by
      rw [hS', Finsupp.linearCombination_comp, LinearMap.comp_apply, Finsupp.lmapDomain_apply,
        ← one_smul A (S.units i), hg, ← ha, ← Finsupp.linearCombination_single, ← map_add]
      congr 1
      ext j
      rw [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
      have : i = j ↔ j ∉ Set.range (Fin.succAbove i) := by simp [@eq_comm _ i]
      split_ifs with hij
      · rw [Finsupp.mapDomain_notin_range, zero_add, hij]
        rwa [← this]
      · obtain ⟨j, rfl⟩ := not_imp_comm.mp this.mpr hij
        rw [Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective, add_zero,
          Finsupp.comapDomain_apply]
    have := S'.isMaximal p hp G hf
    suffices Submodule.span A (Set.range S.units) < Submodule.span A (Set.range S'.units) by
      have : (Submodule.span A (Set.range S.units)).toAddSubgroup.FiniteIndex :=
        ⟨AddSubgroup.index_ne_zero_of_finite (hH := (S.isMaximal _ hp _ hf).finite)⟩
      exact (hs.maximal' _ _ _ S').not_gt <| AddSubgroup.index_strictAnti ‹_›
    rw [SetLike.lt_iff_le_and_exists]
    constructor
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      by_cases hij : i = j
      · rw [add_comm, ← eq_sub_iff_add_eq] at ha'
        rw [← hij, ha']
        apply sub_mem
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Function.update_self _ _ _⟩)
        · rw [← Finsupp.range_linearCombination, Finsupp.linearCombination_comp,
            LinearMap.comp_apply]
          exact ⟨_, rfl⟩
      · exact Submodule.subset_span ⟨j, Function.update_of_ne (Ne.symm hij) _ _⟩
    · refine ⟨g, Submodule.subset_span ⟨i, Function.update_self _ _ _⟩, ?_⟩
      rw [← Finsupp.range_linearCombination]
      rintro ⟨l, rfl⟩
      let _ := (Algebra.id A).toModule
      let _ : SMulZeroClass A A := SMulWithZero.toSMulZeroClass
      let _ : Module A (Fin s →₀ A) := Finsupp.module (Fin s) A
      rw [← LinearMap.map_smul, ← sub_eq_zero,
        ← (Finsupp.linearCombination A S.units).map_sub] at hg
      have := DFunLike.congr_fun (linearIndependent_iff.mp S.linearIndependent _ hg) i
      simp only [Finsupp.coe_sub, Finsupp.coe_smul, ha, Pi.sub_apply, Finsupp.coe_zero,
        Pi.zero_apply, sub_eq_zero] at this
      exact CyclotomicIntegers.not_isUnit_one_sub_zeta p
        (IsUnit.of_mul_eq_one _ this)

lemma corollary [Module A G] (S : systemOfUnits p G s) (hs : S.IsFundamental) (a : Fin s → ℤ)
    (ha : ∃ i, ¬ (p : ℤ) ∣ a i) :
    ∀ g : G, (1 - zeta p) • g ≠ ∑ i, a i • S.units i := by
  intro g hg
  obtain ⟨i, hi⟩ := ha
  have := Fact.mk hp
  obtain ⟨x, y, e⟩ := CyclotomicIntegers.isCoprime_one_sub_zeta p (a i) hi
  let b' : Fin s → A := fun j ↦ x * (1 - zeta ↑p) + y * (a j)
  let b := Finsupp.ofSupportFinite b' (Set.toFinite (Function.support _))
  have hb : b i = 1 := by rw [← e]; rfl
  apply lemma2 p hp G s hf S hs i b hb (x • ∑ i, S.units i + y • g)
  rw [smul_add, smul_smul _ y, mul_comm, ← smul_smul, hg, smul_sum, smul_sum, smul_sum,
    ← sum_add_distrib, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
  · congr
    · ext j
      simp only [smul_smul, Finsupp.ofSupportFinite_coe, add_smul, b', b]
      congr 1
      · rw [mul_comm]
      · rw [← Int.cast_smul_eq_zsmul (R := A), smul_smul]
  · simp

end systemOfUnits.IsFundamental
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular
section application

variable
    [Algebra k K] (hKL : finrank k K = p) (σ : K ≃ₐ[k] K)
    (hσ : ∀ x, x ∈ Subgroup.zpowers σ)

def RelativeUnits (k K : Type*) [Field k] [Field K] [Algebra k K] :=
  (𝓞 K)ˣ ⧸
    MonoidHom.range
      (Units.map (algebraMap (𝓞 k) (𝓞 K) : (𝓞 k) →* (𝓞 K)))

scoped instance : CommGroup (RelativeUnits k K) := by delta RelativeUnits; infer_instance

section

lemma norm_eq_prod_pow_gen
    [IsGalois k K] [FiniteDimensional k K]
    (σ : K ≃ₐ[k] K) (hσ : ∀ x, x ∈ Subgroup.zpowers σ) (η : K) :
    algebraMap k K (Algebra.norm k η) = (∏ i ∈ Finset.range (orderOf σ), (σ ^ i) η)   := by
  let _ : Fintype (Subgroup.zpowers σ) := inferInstance
  rw [Algebra.norm_eq_prod_automorphisms, ← Fin.prod_univ_eq_prod_range,
    ← (finEquivZPowers <| isOfFinOrder_of_finite _).symm.prod_comp]
  simp only [pow_finEquivZPowers_symm_apply]
  rw [prod_subtype]
  simp [hσ]

include hKL in
lemma Hilbert92_aux0 (h : ℕ) (ν : (𝓞 k)ˣ) (hν : IsPrimitiveRoot (ν : k) (p ^ h))
    (H : ∀ ε : (𝓞 K)ˣ, algebraMap k K ν ^ (p ^ (h - 1)) ≠ ε / (σ ε : K)) :
    ∃ η : (𝓞 K)ˣ, Algebra.norm k (η : K) = 1 ∧
      ∀ ε : (𝓞 K)ˣ, (η : K) ≠ ε / (σ ε : K) := by
  let η := (Units.map (algebraMap (𝓞 k) (𝓞 K)) ν : (𝓞 K)ˣ)
  use η ^ (p ^ (h - 1))
  refine ⟨?_, fun ε => H ε⟩
  simp only [Units.val_pow_eq_pow_val, map_pow, MonoidHom.coe_toAdditive, Function.comp_apply, Module.End.pow_apply, Function.iterate_succ_apply, Function.iterate_zero_apply, AddMonoidHom.coe_toIntLinearMap]
  change (Algebra.norm k) ((algebraMap k K) _) ^ _ = 1
  rw [Algebra.norm_algebraMap, hKL, ← pow_mul]
  nth_rewrite 1 [← pow_one p]
  rw [← pow_add]
  apply (hν.pow_eq_one_iff_dvd _).2
  cases h <;> simp [add_comm]

variable [NumberField K] [NumberField k]

section Mathlib.Algebra.Algebra.Hom

variable {R A' : Type*} [CommSemiring R] [Semiring A'] [Algebra R A'] (φ ψ : A' →ₐ[R] A')

end Mathlib.Algebra.Algebra.Hom
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular

noncomputable
def relativeUnitsMap (σ : K →ₐ[k] K) : RelativeUnits k K →* RelativeUnits k K := by
  apply QuotientGroup.lift _
    ((QuotientGroup.mk' _).comp (Units.map (galRestrictHom (𝓞 k) k K (𝓞 K) σ)))
  rintro _ ⟨i, rfl⟩
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, QuotientGroup.coe_mk', Function.comp_apply,
    QuotientGroup.eq_one_iff, MonoidHom.mem_range, Units.ext_iff, Units.coe_map, MonoidHom.coe_coe,
    AlgHom.commutes, exists_apply_eq_apply]

lemma relativeUnitsMap_mk (σ : K →ₐ[k] K) (x : (𝓞 K)ˣ) :
    relativeUnitsMap σ (QuotientGroup.mk x) =
      QuotientGroup.mk (Units.map (galRestrictHom (𝓞 k) k K (𝓞 K) σ) x) := rfl

@[scoped simp]
theorem relativeUnitsMap_one (x : RelativeUnits k K) :
    relativeUnitsMap (1 : K →ₐ[k] K) x = x := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  simp only [relativeUnitsMap_mk, map_one]
  rfl

theorem relativeUnitsMap_mul_apply {f g} (x : RelativeUnits k K) :
    (relativeUnitsMap (f * g)) x = (relativeUnitsMap f (relativeUnitsMap g x)) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  simp_rw [relativeUnitsMap_mk, map_mul]
  rfl

/-- The automorphism of relative units induced by a Galois automorphism. -/
noncomputable def relativeUnitsMulEquiv (e : K ≃ₐ[k] K) :
    RelativeUnits k K ≃* RelativeUnits k K where
  toFun := relativeUnitsMap e.toAlgHom
  invFun := relativeUnitsMap e.symm.toAlgHom
  left_inv x := by
    have h : (relativeUnitsMap (e.symm.toAlgHom * e.toAlgHom)) x = x := by
      rw [show e.symm.toAlgHom * e.toAlgHom = (1 : K →ₐ[k] K) from by ext y; simp]
      exact relativeUnitsMap_one x
    rwa [relativeUnitsMap_mul_apply] at h
  right_inv x := by
    have h : (relativeUnitsMap (e.toAlgHom * e.symm.toAlgHom)) x = x := by
      rw [show e.toAlgHom * e.symm.toAlgHom = (1 : K →ₐ[k] K) from by ext y; simp]
      exact relativeUnitsMap_one x
    rwa [relativeUnitsMap_mul_apply] at h
  map_mul' x y := map_mul (relativeUnitsMap e.toAlgHom) x y

@[simp]
theorem relativeUnitsMulEquiv_apply (e : K ≃ₐ[k] K) (x : RelativeUnits k K) :
    relativeUnitsMulEquiv e x = relativeUnitsMap e.toAlgHom x := rfl

set_option backward.isDefEq.respectTransparency false in
include σ hp hKL hσ in
open Polynomial in



lemma isTors' [IsGalois k K] : Module.IsTorsionBySet ℤ[X]
    (Module.AEval' (addMonoidEndRingEquivInt _
      ((relativeUnitsMulEquiv σ).toMonoidHom.toAdditive)))
    (Ideal.span {cyclotomic p ℤ}) := by
  classical
  have := Fact.mk hp
  rw [← Module.isTorsionBySet_iff_is_torsion_by_span, Module.isTorsionBySet_singleton_iff]
  intro x
  obtain ⟨x, rfl⟩ := (Module.AEval.of _ _ _).surjective x
  obtain ⟨x, rfl⟩ := Additive.ofMul.surjective x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  rw [← Module.AEval.of_aeval_smul]
  simp_rw [Module.End.smul_def, Polynomial.cyclotomic_prime ℤ p, EmbeddingLike.map_eq_zero_iff,
    map_sum, map_pow, aeval_X, LinearMap.coe_sum, Finset.sum_apply]
  have hterm : ∀ (c : ℕ) (u : (𝓞 K)ˣ),
      ((addMonoidEndRingEquivInt _
        ((relativeUnitsMulEquiv σ).toMonoidHom.toAdditive)) ^ c)
          (Additive.ofMul (QuotientGroup.mk u)) =
        Additive.ofMul ((QuotientGroup.mk
          (((Units.mapEquiv (galRestrict (𝓞 k) k K (𝓞 K) σ).toRingEquiv) ^ c) u) : RelativeUnits k K)) := by
    have h1 : ∀ z : (𝓞 K)ˣ,
        (addMonoidEndRingEquivInt _
          ((relativeUnitsMulEquiv σ).toMonoidHom.toAdditive))
            (Additive.ofMul (QuotientGroup.mk z)) =
          Additive.ofMul ((QuotientGroup.mk
            ((Units.mapEquiv (galRestrict (𝓞 k) k K (𝓞 K) σ).toRingEquiv) z) : RelativeUnits k K)) := by
      intro z
      show Additive.ofMul ((relativeUnitsMulEquiv σ) (QuotientGroup.mk z)) = _
      rw [relativeUnitsMulEquiv_apply, relativeUnitsMap_mk]
      rfl
    intro c u
    induction c with
    | zero => rfl
    | succ c ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      exact (h1 _).trans (by simp only [pow_succ', MulAut.mul_apply])
  simp_rw [hterm]
  rw [← ofMul_prod (Finset.range p)
      (fun i => ((QuotientGroup.mk
        (((Units.mapEquiv (galRestrict (𝓞 k) k K (𝓞 K) σ).toRingEquiv) ^ i) x)) :
        RelativeUnits k K)), ← QuotientGroup.mk_prod, ofMul_eq_zero, QuotientGroup.eq_one_iff]
  use Units.map (NumberField.RingOfIntegers.norm k) x
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe,
    NumberField.RingOfIntegers.coe_algebraMap_norm, Units.coe_prod,
    Algebra.norm_eq_prod_automorphisms]
  rw [← hKL, ← IsGalois.card_aut_eq_finrank,
    ← orderOf_eq_card_of_forall_mem_zpowers hσ, ← Fin.prod_univ_eq_prod_range,
    ← (finEquivZPowers <| isOfFinOrder_of_finite _).symm.prod_comp]
  simp only [RingOfIntegers.coe_eq_algebraMap, pow_finEquivZPowers_symm_apply, map_prod,
    algebraMap_galRestrictHom_apply]
  exact Fintype.prod_equiv (Equiv.subtypeUnivEquiv hσ).symm _ _ (fun i ↦ by
    have hj : ∀ j : ℕ, (algebraMap (𝓞 K) K)
        (((((Units.mapEquiv (galRestrict (𝓞 k) k K (𝓞 K) σ).toRingEquiv ^ j) x) :
          (𝓞 K)ˣ) : 𝓞 K)) = (σ ^ j) ((algebraMap (𝓞 K) K) x) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ', MulAut.mul_apply, Units.coe_mapEquiv]
        show (algebraMap (𝓞 K) K) ((galRestrict (𝓞 k) k K (𝓞 K) σ)
          ((((Units.mapEquiv (galRestrict (𝓞 k) k K (𝓞 K) σ).toRingEquiv) ^ j) x :
            (𝓞 K)ˣ) : 𝓞 K)) = _
        rw [algebraMap_galRestrict_apply, pow_succ', AlgEquiv.mul_apply, ih]
    rw [hj]
    congr 1
    exact (pow_finEquivZPowers_symm_apply (isOfFinOrder_of_finite σ) ⟨i, hσ i⟩).symm)

@[nolint unusedArguments]
def relativeUnitsWithGenerator (_hp : Nat.Prime p)
  (_hKL : finrank k K = p) (σ : K ≃ₐ[k] K) (_hσ : ∀ x, x ∈ Subgroup.zpowers σ) :=
  RelativeUnits k K

scoped instance : CommGroup (relativeUnitsWithGenerator p hp hKL σ hσ) := by
  delta relativeUnitsWithGenerator; infer_instance

end
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular

local notation "G" =>
  Additive (relativeUnitsWithGenerator p hp hKL σ hσ) ⧸
    AddCommGroup.torsion (Additive (relativeUnitsWithGenerator p hp hKL σ hσ))

def unitToU (u : (𝓞 K)ˣ) : G := QuotientAddGroup.mk (Additive.ofMul <| QuotientGroup.mk u)

local notation "mkG" => unitToU p hp hKL σ hσ

set_option backward.isDefEq.respectTransparency false in
lemma unit_to_U_one : mkG 1 = 0 := by
  rw [unitToU, QuotientGroup.mk_one, ofMul_one, QuotientAddGroup.mk_zero]

set_option backward.isDefEq.respectTransparency false in
lemma unit_to_U_mul (x y) : mkG (x * y) = mkG x + mkG y := by
  rw [unitToU, unitToU, unitToU, QuotientGroup.mk_mul, ofMul_mul, QuotientAddGroup.mk_add]

lemma unit_to_U_inv (x) : mkG (x⁻¹) = - mkG x := by
  rw [eq_neg_iff_add_eq_zero, ← unit_to_U_mul, inv_mul_cancel, unit_to_U_one]

lemma unit_to_U_div (x y) : mkG (x / y) = mkG x - mkG y := by
  rw [div_eq_mul_inv, unit_to_U_mul, unit_to_U_inv, sub_eq_add_neg]

lemma unit_to_U_prod {ι} (s : Finset ι) (f : ι → _) :
    mkG (∏ i ∈ s, f i) = ∑ i ∈ s, mkG (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [prod_empty, sum_empty, unit_to_U_one]
  | @insert x s hxs IH =>
    simp only [hxs, not_false_eq_true, prod_insert, sum_insert, unit_to_U_mul, IH]

lemma unit_to_U_pow (x) (n : ℕ) : mkG (x ^ n) = n • (mkG x) := by
  induction n with
  | zero => simp [unit_to_U_one]
  | succ n IH => simp [unit_to_U_mul, pow_succ, succ_nsmul, IH]

lemma unit_to_U_zpow (x) (n : ℤ) : mkG (x ^ n) = n • (mkG x) := by
  cases n with
  | ofNat n => simp [unit_to_U_pow]
  | negSucc n => simp [unit_to_U_inv, unit_to_U_pow]

set_option backward.isDefEq.respectTransparency false in
lemma unit_to_U_map (x : (𝓞 k)ˣ) : mkG (Units.map (algebraMap (𝓞 k) (𝓞 K)) x) = 0 := by
  delta unitToU
  rw [QuotientAddGroup.eq_zero_iff]
  convert zero_mem (AddCommGroup.torsion (Additive (relativeUnitsWithGenerator p hp hKL σ hσ)))
  rw [ofMul_eq_zero, QuotientGroup.eq_one_iff]
  exact ⟨_, rfl⟩

variable [NumberField k]

include hp in
lemma lh_pow_free_aux {M} [CommGroup M] [Module.Finite ℤ (Additive M)] (ν : M)
    (hk : ∀ (ε : M) (n : ℕ), ε ^ (p ^ n) = 1 → ∃ i, ν ^ i = ε)
    (r) (hr : finrank ℤ (Additive M) < r) (η : Fin r → Additive M) :
    ∃ (a : ℤ) (ι : Fin r → ℤ) (i : Fin r),
      ∑ i, ι i • η i = a • (Additive.ofMul ν) ∧ ¬ ↑p ∣ ι i := by
  obtain ⟨f, hf, hf'⟩ := Fintype.not_linearIndependent_iff.mp
    (mt (LinearIndependent.fintype_card_le_finrank (R := ℤ) (b := η))
      ((hr.trans_eq (Fintype.card_fin r).symm).not_ge))
  obtain ⟨n, f', hf', i, hi⟩ := Int.exists_pow_smul_eq_and_not_dvd f
    (Function.ne_iff.mpr hf') p hp.ne_one
  simp_rw [hf', Pi.smul_apply, smul_assoc, ← smul_sum] at hf
  obtain ⟨a, ha⟩ := hk _ _ hf
  rw [← zpow_natCast] at ha
  exact ⟨a, f', i, ha.symm, hi⟩

include hp in
lemma lh_pow_free' {M} [CommGroup M] [Module.Finite ℤ (Additive M)] (ν : M)
    (hk : ∀ (ε : M) (n : ℕ), ε ^ (p ^ n) = 1 → ∃ i, ν ^ i = ε)
    (r) (hr : finrank ℤ (Additive M) + 1 < r) (η : Fin r → Additive M) :
    ∃ (a : ℤ) (ι : Fin r → ℤ) (i : Fin r),
      ∑ i, ι i • η i = (a * p) • Additive.ofMul ν ∧
        ¬ ↑p ∣ ι i ∧ (ν = 1 → ↑i ≠ r - 1) := by
  cases r with
  | zero => exact (not_lt_zero hr).elim
  | succ r =>
    simp only [add_lt_add_iff_right] at hr
    obtain ⟨a₁, ι₁, i₁, e₁, hi₁⟩ := lh_pow_free_aux p hp ν hk r hr
      (η ∘ Fin.castSucc)
    obtain ⟨a₂, ι₂, i₂, e₂, hi₂⟩ := lh_pow_free_aux p hp ν hk r hr
      (η ∘ Fin.succAbove i₁.castSucc)
    by_cases hν' : ν = 1
    · refine ⟨1, Function.extend Fin.castSucc ι₁ 0, Fin.castSucc i₁, ?_,
        by rwa [(Fin.castSucc_injective r).extend_apply], ?_⟩
      · subst hν'
        simp only [Function.comp_apply, ofMul_one, smul_zero] at e₁ ⊢
        rw [← e₁]
        simp [Fin.sum_univ_castSucc, (Fin.castSucc_injective r).extend_apply,
          (Fin.castSucc_lt_last _).ne]
      · rintro -; simp [(Fin.is_lt _).ne]
    by_cases ha₁ : ↑p ∣ a₁
    · obtain ⟨b, hb⟩ := ha₁
      refine ⟨b, Function.extend Fin.castSucc ι₁ 0, Fin.castSucc i₁, ?_,
        by rwa [(Fin.castSucc_injective r).extend_apply], fun H ↦ (hν' H).elim⟩
      rw [← hb.trans (mul_comm _ _), ← e₁]
      simp [Fin.sum_univ_castSucc, (Fin.castSucc_injective r).extend_apply,
        (Fin.castSucc_lt_last _).ne]
    by_cases ha₂ : ↑p ∣ a₂
    · obtain ⟨b, hb⟩ := ha₂
      refine ⟨b, Function.extend (Fin.succAbove i₁.castSucc) ι₂ 0,
        Fin.succAbove i₁.castSucc i₂, ?_,
        by rwa [Fin.succAbove_right_injective.extend_apply], fun H ↦ (hν' H).elim⟩
      rw [← hb.trans (mul_comm _ _), ← e₂]
      simp [Fin.sum_univ_succAbove _ i₁.castSucc, Fin.succAbove_right_injective.extend_apply]
    obtain ⟨α₁, β₁, h₁⟩ := (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr ha₁
    obtain ⟨α₂, β₂, h₂⟩ := (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr ha₂
    refine ⟨α₂ - α₁,
      β₁ • Function.extend Fin.castSucc ι₁ 0 -
        β₂ • Function.extend (Fin.succAbove i₁.castSucc) ι₂ 0,
      i₁.castSucc, ?_, ?_, fun H ↦ (hν' H).elim⟩
    · rw [sub_mul, eq_sub_iff_add_eq.mpr h₁, eq_sub_iff_add_eq.mpr h₂]
      simp only [zsmul_eq_mul, Pi.intCast_def, Int.cast_id, Pi.sub_apply, Pi.mul_apply,
        sub_sub_sub_cancel_left]
      simp only [sub_smul, mul_smul, ← e₁, ← e₂, sum_sub_distrib]
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_succAbove _ i₁.castSucc]
      simp [(Fin.castSucc_injective r).extend_apply, Fin.succAbove_right_injective.extend_apply,
        (Fin.castSucc_lt_last _).ne, smul_sum]
    · simp only [zsmul_eq_mul, Pi.intCast_def, Int.cast_id, Pi.sub_apply, Pi.mul_apply,
        not_true_eq_false, (Fin.castSucc_injective r).extend_apply,
        Fin.exists_succAbove_eq_iff, ne_eq, not_false_eq_true, Function.extend_apply',
        Pi.zero_apply, mul_zero, sub_zero, (Nat.prime_iff_prime_int.mp hp).dvd_mul, hi₁, not_or,
        and_true]
      intro H
      exact (Nat.prime_iff_prime_int.mp hp).not_dvd_one
        (h₁ ▸ dvd_add (dvd_mul_left (p : ℤ) α₁) (dvd_mul_of_dvd_left H a₁))

include hp in
lemma lh_pow_free (ν : (𝓞 k)ˣ)
    (hk : ∀ (ε : (𝓞 k)ˣ) (n : ℕ), ε ^ (p ^ n) = 1 → ∃ i, ν ^ i = ε)
    (η : Fin (NumberField.Units.rank k + 2) → Additive (𝓞 k)ˣ) :
    ∃ (a : ℤ) (ι : Fin (NumberField.Units.rank k + 2) → ℤ)
      (i₀ : Fin (NumberField.Units.rank k + 2)),
      ∑ i, ι i • η i = (a * p) • Additive.ofMul ν ∧
        ¬ (p : ℤ) ∣ ι i₀ ∧ (ν = 1 → i₀ ≠ Fin.last _) := by
  convert lh_pow_free' p hp ν hk _ ?_ η
  · simp [Fin.ext_iff]
  · rw [NumberField.Units.finrank_eq]
    exact Nat.lt_add_one _

variable [NumberField K]

include hKL in
lemma Hilbert92_aux1 (n : ℕ) (H : Fin n → Additive (𝓞 K)ˣ) (ν : (𝓞 k)ˣ)
    (a : ℤ) (ι : Fin n → ℤ) (η : Fin n → Additive (𝓞 k)ˣ)
    (ha : ∑ i : Fin n, ι i • η i = (a * ↑↑p) • Additive.ofMul ν)
    (hη :
      ∀ i, Additive.toMul (η i) = Algebra.norm k (S := K) ((Additive.toMul (H i) : _) : K)) :
    letI J : (𝓞 K)ˣ := (Additive.toMul (∑ i : Fin n, ι i • H i)) *
      (Units.map (algebraMap (𝓞 k) (𝓞 K)).toMonoidHom ν) ^ (-a)
    Algebra.norm k (S := K) ((J : (𝓞 K)ˣ) : K) = 1 := by
  have hcoe : ((algebraMap (𝓞 K) K) ((algebraMap (𝓞 k) (𝓞 K)) ((ν ^ a)⁻¹).1)) =
    algebraMap (𝓞 k) (𝓞 K) ((ν ^ a)⁻¹).1 := rfl
  simp only [toMul_sum, toMul_zsmul, zpow_neg, Units.val_mul, Units.coe_prod, map_mul, map_prod,
    Units.coe_zpow, map_mul, map_prod, Algebra.norm_zpow]
  rw [← map_zpow, Units.coe_map_inv]
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  have hcoe1 :
      algebraMap (𝓞 k) k (((ν ^ p) ^ a)⁻¹).1 = ((((ν : 𝓞 k) : k) ^ p) ^ a)⁻¹ := by
    change ((Units.map (algebraMap (𝓞 k) k : (𝓞 k) →* k)) _).1 = _
    simp
  have hcoe2 :
      ((algebraMap (𝓞 k) (𝓞 K) ((ν ^ a)⁻¹).1 : 𝓞 K) : K) =
        algebraMap k K ((ν ^ a)⁻¹).1 := rfl
  rw [hcoe, hcoe2, Algebra.norm_algebraMap, hKL, ← map_pow,
    ← Units.val_pow_eq_pow_val, inv_pow, ← zpow_natCast, ← zpow_mul, mul_comm a, zpow_mul,
      zpow_natCast, hcoe1]
  apply_fun Additive.toMul at ha
  apply_fun ((↑) : (𝓞 k)ˣ → k) at ha
  simp only [toMul_sum, toMul_zsmul, Units.coe_prod, map_prod, hη,
    Units.coe_zpow, toMul_ofMul] at ha
  rwa [← zpow_natCast, ← zpow_mul, mul_comm _ a, mul_inv_eq_one₀]
  simp [← Units.coe_zpow]

variable [IsGalois k K]

set_option backward.isDefEq.respectTransparency false in
include hKL in
noncomputable
scoped instance relativeUnitsModule : Module A G := by
  letI : Module A (Additive (relativeUnitsWithGenerator p hp hKL σ hσ)) :=
    (isTors' p hp hKL σ hσ).module
  infer_instance

lemma relativeUnitsModule_zeta_smul (x) :
    (zeta p) • mkG x = mkG (Units.map (galRestrictHom (𝓞 k) k K (𝓞 K) σ) x) := by
  let φ := (addMonoidEndRingEquivInt _
      ((relativeUnitsMulEquiv σ).toMonoidHom.toAdditive))
  change QuotientAddGroup.mk ((Module.AEval'.of φ).symm <|
    Polynomial.X (R := ℤ) • Module.AEval'.of φ (Additive.ofMul (QuotientGroup.mk x))) = _
  simp only [Module.AEval.of_symm_smul, Polynomial.aeval_X,
    LinearEquiv.symm_apply_apply, Module.End.smul_def, unitToU]
  rfl

set_option backward.isDefEq.respectTransparency false in
local instance : Module.Finite ℤ (Additive <| RelativeUnits k K) :=
  inferInstanceAs
    (Module.Finite ℤ (Additive (𝓞 K)ˣ ⧸ AddSubgroup.toIntSubmodule (Subgroup.toAddSubgroup
    (MonoidHom.range <| Units.map (algebraMap (𝓞 k) (𝓞 K) : (𝓞 k) →* (𝓞 K))))))

local instance : Module.Finite ℤ (Additive <| relativeUnitsWithGenerator p hp hKL σ hσ) :=
  inferInstanceAs (Module.Finite ℤ (Additive (RelativeUnits k K)))

local instance : Module.Finite ℤ G := Module.Finite.of_surjective
  (M := Additive (relativeUnitsWithGenerator p hp hKL σ hσ))
  (QuotientAddGroup.mk' _).toIntLinearMap (QuotientAddGroup.mk'_surjective _)

noncomputable
def unitlifts (S : systemOfUnits p G (NumberField.Units.rank k + 1)) :
    Fin (NumberField.Units.rank k + 1) → Additive (𝓞 K)ˣ :=
  fun i ↦ Additive.ofMul (Additive.toMul (S.units i).out).out

lemma unitlifts_spec (S : systemOfUnits p G (NumberField.Units.rank k + 1)) (i) :
    mkG (Additive.toMul <| unitlifts p hp hKL σ hσ S i) = S.units i := by
  delta unitToU unitlifts QuotientGroup.mk QuotientAddGroup.mk
  rw [toMul_ofMul]
  exact (congrArg (fun y => Quotient.mk'' (Additive.ofMul y)) (Quotient.out_eq' _)).trans
    (Quotient.out_eq' _)

lemma u_lemma2 (u v : (𝓞 K)ˣ) (hu : u = v / (σ v : K)) :
    mkG u = (1 - zeta p : A) • mkG v := by
  rw [sub_smul, one_smul, relativeUnitsModule_zeta_smul, ← unit_to_U_div]
  congr
  rw [eq_div_iff_mul_eq']
  ext
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, map_mul,
    algebraMap_galRestrictHom_apply, hu]
  exact div_mul_cancel₀ _ (by simp)

include hKL hσ hp in
lemma Hilbert92_aux2 (E : (𝓞 K)ˣ) (ν : k) (hE : algebraMap k K ν = E / σ E)
  (hν : (ν : k) ^ p = 1) (hpodd : p ≠ 2) :
    algebraMap k K (Algebra.norm k (S := K) E) = E ^ p := by
  have h1 : ∀ (i : ℕ), (σ ^ i) E = ((algebraMap k K ν)⁻¹)^i * E := by
    intro i
    induction i with
    | zero =>
      simp only [pow_zero, AlgEquiv.one_apply, one_mul]
    | succ n ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, pow_succ']
      simp only [inv_pow, map_mul, map_inv₀, map_pow, AlgEquiv.commutes]
      have h0 : algebraMap k K ν ≠ 0 := fun h ↦ by
        simp [(map_eq_zero _).1 h, hp.ne_zero] at hν
      rw [hE]
      field_simp
  rw [norm_eq_prod_pow_gen σ hσ, orderOf_eq_card_of_forall_mem_zpowers hσ,
    IsGalois.card_aut_eq_finrank, hKL]
  conv =>
    enter [1, 2, i]
    rw [h1 i, mul_comm]
  rw [prod_mul_distrib, prod_const, card_range, prod_pow_eq_pow_sum, inv_pow, mul_eq_left₀,
    inv_eq_one, sum_range_id, Nat.mul_div_assoc, pow_mul, ← map_pow, hν, map_one, one_pow]
  · exact even_iff_two_dvd.1 (hp.even_sub_one hpodd)
  · simp

variable [IsUnramifiedAtInfinitePlaces k K]

open scoped NumberField NumberField.Units in
lemma NumberField.Units.rank_of_isUnramified :
    NumberField.Units.rank K = (finrank k K) * NumberField.Units.rank k + (finrank k K) - 1 := by
  delta NumberField.Units.rank
  rw [IsUnramifiedAtInfinitePlaces.card_infinitePlace k,
    mul_comm, mul_tsub, mul_one, tsub_add_cancel_of_le]
  refine (mul_one _).symm.trans_le (Nat.mul_le_mul_left _ ?_)
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Fintype.card_pos_iff]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
lemma finrank_G : finrank ℤ G = (Units.rank k + 1) * (↑p - 1) := by
  rw [← Submodule.torsion_int]
  refine (congr_arg Cardinal.toNat (rank_quotient_eq_of_le_torsion le_rfl)).trans ?_
  change finrank ℤ (Additive (𝓞 K)ˣ ⧸ AddSubgroup.toIntSubmodule (Subgroup.toAddSubgroup
    (MonoidHom.range <| Units.map (algebraMap (𝓞 k) (𝓞 K) : (𝓞 k) →* (𝓞 K))))) = _
  rw [Submodule.finrank_quotient]
  change _ - finrank ℤ (LinearMap.range <| AddMonoidHom.toIntLinearMap <|
    MonoidHom.toAdditive <| Units.map (algebraMap (𝓞 k) (𝓞 K) : (𝓞 k) →* (𝓞 K))) = _
  rw [LinearMap.finrank_range_of_inj, NumberField.Units.finrank_eq, NumberField.Units.finrank_eq,
    NumberField.Units.rank_of_isUnramified (k := k), add_mul, one_mul, mul_tsub, mul_one, mul_comm,
      add_tsub_assoc_of_le, tsub_add_eq_add_tsub, hKL]
  · exact (mul_one _).symm.trans_le (Nat.mul_le_mul_left _ hp.one_lt.le)
  · exact hKL ▸ hp.one_lt.le
  · intros i j e
    apply Additive.toMul.injective
    ext
    apply (algebraMap k K).injective
    exact congr_arg (fun i : Additive (𝓞 K)ˣ ↦ (↑(↑(Additive.toMul i) : 𝓞 K) : K)) e

local instance : HasUniqueDiv G where
  nsmul_right_injective := by
    intro n hn a b h
    exact eq_of_nsmul_eq_nsmul_of_addCommute hn (AddCommute.all a b) h

local instance : Module.Free ℤ G := Module.free_of_finite_type_torsion_free'

theorem Hilbert91 :
    ∃ S : systemOfUnits p G (NumberField.Units.rank k + 1), S.IsFundamental :=
  systemOfUnits.IsFundamental.existence p hp G (NumberField.Units.rank k + 1)
    (finrank_G p hp hKL σ hσ)

include hp in
lemma h_exists' : ∃ (h : ℕ) (ν : (𝓞 k)ˣ),
    IsPrimitiveRoot (ν : k) (p ^ h) ∧
    ∀ (ε : (𝓞 k)ˣ) (n : ℕ), ε ^ (p ^ n) = 1 → ∃ i, ν ^ i = ε := by
  have : NeZero p := ⟨hp.ne_zero⟩
  classical
  let H := Subgroup.toAddSubgroup.symm
    (Submodule.torsion' ℤ (Additive (𝓞 k)ˣ) (Submonoid.powers p)).toAddSubgroup
  have : H ≤ NumberField.Units.torsion k := by
    rintro x ⟨⟨_, i, rfl⟩, hnx : x ^ (p ^ i) = 1⟩
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨p ^ i, Fin.pos', hnx⟩
  obtain ⟨ν, hν⟩ := Subgroup.isCyclic_of_le this
  obtain ⟨⟨_, i, rfl⟩, hiν : (ν : (𝓞 k)ˣ) ^ (p ^ i) = 1⟩ := ν.prop
  obtain ⟨j, _, hj'⟩ := (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hiν)
  refine ⟨j, ν, IsPrimitiveRoot.coe_coe_iff.mpr (hj' ▸ IsPrimitiveRoot.orderOf ν.1),
    fun ε n hn ↦ ?_⟩
  let _ : Fintype (Units.torsion k) := Fintype.ofFinite _
  have : Fintype H := Set.fintypeSubset (NumberField.Units.torsion k) this
  obtain ⟨i, hi⟩ := mem_powers_iff_mem_zpowers.mpr (hν ⟨ε, ⟨_, n, rfl⟩, hn⟩)
  exact ⟨i, congr_arg Subtype.val hi⟩

local notation "r" => NumberField.Units.rank k

scoped instance instCommGroupUnitsRingOfIntegersFltRegular : CommGroup ((𝓞 k))ˣ := inferInstance

include hp hKL hσ in

lemma almostHilbert92 (hpodd : p ≠ 2) :
    ∃ η : (𝓞 K)ˣ, Algebra.norm k (η : K) = 1 ∧
      ∀ ε : (𝓞 K)ˣ, (η : K) ≠ ε / (σ ε : K) := by
  classical
  obtain ⟨h, ν, hν, hν'⟩ := h_exists' p (k := k) hp
  by_cases H : ∀ ε : (𝓞 K)ˣ, algebraMap k K ν ^ (p ^ (h - 1)) ≠ ε / (σ ε : K)
  · exact Hilbert92_aux0 p hKL σ h ν hν H
  simp only [ne_eq, not_forall, not_not] at H
  obtain ⟨E, hE⟩ := H
  let NE := Units.map (NumberField.RingOfIntegers.norm k) E
  have hNE : (NE : k) = Algebra.norm k (E : K) := rfl
  obtain ⟨S, hS⟩ := Hilbert91 p (K := K) (k := k) hp hKL σ hσ
  have NE_p_pow : (Units.map (algebraMap (𝓞 k) (𝓞 K)).toMonoidHom NE) = E ^ p := by
    ext
    simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe,
      RingOfIntegers.coe_eq_algebraMap, Units.val_pow_eq_pow_val, map_pow, MonoidHom.coe_toAdditive, Function.comp_apply, Module.End.pow_apply, Function.iterate_succ_apply, Function.iterate_zero_apply, AddMonoidHom.coe_toIntLinearMap]
    rw [← map_pow] at hE
    refine Hilbert92_aux2 p hp hKL σ hσ E _ hE ?_ hpodd
    rw [← pow_mul, ← pow_succ]
    apply (hν.pow_eq_one_iff_dvd _).2
    cases h <;> simp only [pow_zero, zero_le, tsub_eq_zero_of_le, zero_add, pow_one, one_dvd,
      Nat.succ_sub_succ_eq_sub, tsub_zero, dvd_refl]
  let H := unitlifts p hp hKL σ hσ S
  let N : Fin (r + 1) → Additive (𝓞 k)ˣ :=
    fun e => Additive.ofMul (Units.map (NumberField.RingOfIntegers.norm k) (Additive.toMul (H e)))
  let η : Fin (r + 2) → Additive (𝓞 k)ˣ := Fin.snoc N (Additive.ofMul NE)
  obtain ⟨a, ι, i, ha, ha', ha''⟩ := lh_pow_free p hp ν (k := k) hν' η
  let H2 : Fin (r + 2) → Additive (𝓞 K)ˣ := Fin.snoc H (Additive.ofMul E)
  let J :=
    Additive.toMul (∑ i : Fin (r + 2), ι i • H2 i) *
      (Units.map (algebraMap (𝓞 k) (𝓞 K)).toMonoidHom ν) ^ (-a)
  refine ⟨J, ?_⟩
  constructor
  · apply Hilbert92_aux1 p hKL (r + 2) H2 ν a ι η ha
    intro i
    induction i using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last, toMul_ofMul, Units.coe_map,
        NumberField.RingOfIntegers.coe_norm, NE, η, H2]
    | cast i =>
      simp only [Fin.snoc_castSucc, toMul_ofMul, Units.coe_map,
        NumberField.RingOfIntegers.coe_norm, NE, η, H2, N, H]
  · intro ε hε
    refine hS.corollary p hp _ _ (finrank_G p hp hKL σ hσ) _ (ι ∘ Fin.castSucc) ?_ (mkG ε) ?_
    · by_contra hε'
      simp only [Function.comp_apply, not_exists, not_not] at hε'
      have : i ∉ Set.range Fin.castSucc := by rintro ⟨i, rfl⟩; exact ha' (hε' i)
      rw [← Fin.succAbove_last, Fin.range_succAbove, Set.mem_compl_iff,
        Set.mem_singleton_iff, not_not] at this
      rw [this] at ha'
      cases h with
      | zero =>
          refine ha'' ?_ this
          ext
          simpa only [Units.val_one, map_one, pow_zero, IsPrimitiveRoot.one_right_iff] using hν
      | succ h =>
          obtain ⟨ε', hε'⟩ : ∃ ε' : (𝓞 k)ˣ, ε' ^ p = NE := by
            rw [← (Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd] at ha'
            obtain ⟨α, β, hαβ⟩ := ha'
            choose ι' hι' using hε'
            rw [Fin.sum_univ_castSucc] at ha
            simp (config := { zeta := false, proj := false }) only
              [hι', Fin.snoc_castSucc, Fin.snoc_last, mul_smul, η] at ha
            rw [← smul_sum, add_comm, ← eq_sub_iff_add_eq, smul_comm, ← smul_sub] at ha
            apply_fun ((p : ℤ) • (α • Additive.ofMul NE) + β • ·) at ha
            conv_rhs at ha => rw [smul_comm β, ← smul_add]
            rw [smul_smul, smul_smul, ← add_smul, mul_comm _ α, hαβ, one_smul] at ha
            exact ⟨_, ha.symm⟩
          have hpos : 0 < p ^ h.succ := pow_pos hp.pos _
          have hν'' := (hν.pow hpos (pow_succ _ _)).map_of_injective
            (algebraMap k K).injective
          obtain ⟨ε'', hε''⟩ :
              ∃ ε'' : (𝓞 k)ˣ,
                E = Units.map (algebraMap (𝓞 k) (𝓞 K)).toMonoidHom ε'' := by
              rw [← hε', map_pow, eq_comm, ← mul_inv_eq_one, ← inv_pow,
                ← mul_pow] at NE_p_pow
              apply_fun (fun u : (𝓞 K)ˣ => algebraMap (𝓞 K) K (u : 𝓞 K)) at NE_p_pow
              simp only [RingHom.toMonoidHom_eq_coe, Units.val_pow_eq_pow_val, Units.val_mul,
                Units.coe_map_inv, MonoidHom.coe_coe, Units.val_one, map_pow, map_mul, map_one,
                map_units_inv] at NE_p_pow
              have : NeZero p := ⟨hp.pos.ne'⟩
              obtain ⟨i, -, e⟩ := hν''.eq_pow_of_pow_eq_one NE_p_pow
              use ((ν ^ p ^ h) ^ i * ε')
              rw [map_mul, ← mul_inv_eq_iff_eq_mul]
              ext
              simp only [NumberField.RingOfIntegers.coe_eq_algebraMap] at e ⊢
              push_cast at e ⊢
              simpa [← IsScalarTower.algebraMap_apply] using e.symm
          have hε''coe :
              ((algebraMap (𝓞 k) (𝓞 K) (ε'' : 𝓞 k) : 𝓞 K) : K) =
                algebraMap k K (ε'' : k) := rfl
          simp only [Nat.succ_sub_succ_eq_sub, tsub_zero, ← map_pow, hε'',
            RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe,
            hε''coe, AlgEquiv.commutes] at hE
          replace hE : (algebraMap k K) (((ν : 𝓞 k) : k) ^ p ^ h) = 1 := by
            rwa [div_self (by simp)] at hE
          rw [hE] at hν''
          exact hp.one_lt.ne' (Nat.dvd_one.mp (hν''.dvd_of_pow_eq_one 1 (one_pow 1)))
    · rw [← u_lemma2 p hp hKL σ hσ _ _ hε, unit_to_U_mul, toMul_sum, unit_to_U_prod,
        Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, toMul_zsmul, unit_to_U_zpow, unitlifts_spec, Fin.snoc_last,
        toMul_ofMul, RingHom.toMonoidHom_eq_coe, zpow_neg, unit_to_U_inv, Function.comp_apply,
        unit_to_U_map, smul_zero, neg_zero, add_zero, add_eq_left, H2, H]
      apply_fun mkG at NE_p_pow
      simp only [RingHom.toMonoidHom_eq_coe, unit_to_U_map, unit_to_U_pow] at NE_p_pow
      rw [eq_comm, smul_eq_zero] at NE_p_pow
      simp only [hp.ne_zero, false_or] at NE_p_pow
      rw [NE_p_pow, smul_zero]

end application
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular

lemma Hilbert92 [Algebra k K] [IsGalois k K] [NumberField k] [NumberField K]
    (hKL : Nat.Prime (finrank k K)) (hpodd : finrank k K ≠ 2)
    (σ : K ≃ₐ[k] K) (hσ : ∀ x, x ∈ Subgroup.zpowers σ) :
    ∃ η : (𝓞 K)ˣ, Algebra.norm k (η : K) = 1 ∧
      ∀ ε : (𝓞 K)ˣ, (η : K) ≠ ε / (σ ε : K) :=
  have := IsUnramifiedAtInfinitePlaces_of_odd_finrank (hKL.odd_of_ne_two hpodd)
  have : IsCyclic (K ≃ₐ[k] K) := ⟨σ, hσ⟩
  almostHilbert92 (finrank k K) hKL rfl σ hσ hpodd

end thm91

end FltRegular

end Port_FLT_Deep_Regular_Hilbert92_lean

open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular

section Port_FLT_Deep_Regular_Hilbert94_lean

open scoped NumberField

namespace FltRegular

variable {K : Type} {p : ℕ} [hpri : Fact p.Prime] [Field K]

open Polynomial Module

variable {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L]
  (σ : L ≃ₐ[K] L) (hσ : ∀ x, x ∈ Subgroup.zpowers σ) (hKL : finrank K L = p)

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra A L] [Algebra A K]
    [Algebra B L] [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsIntegralClosure B A L]

scoped instance : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L

include hσ in
lemma comap_span_galRestrict_eq_of_cyclic (β : B) (η : Bˣ)
    (hβ : η * (galRestrict A K L B σ) β = β) (σ' : L ≃ₐ[K] L) :
    (Ideal.span {β}).comap (galRestrict A K L B σ') = Ideal.span {β} := by
  suffices (Ideal.span {β}).map
      (galRestrict A K L B σ'⁻¹).toRingEquiv.toRingHom = Ideal.span {β} by
    rwa [RingEquiv.toRingHom_eq_coe, Ideal.map_comap_of_equiv, map_inv] at this
  apply_fun (Ideal.span {·}) at hβ
  rw [← Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_eq_top.mpr η.isUnit,
    ← Ideal.one_eq_top, one_mul, ← Set.image_singleton, ← Ideal.map_span] at hβ
  change Ideal.map (galRestrict A K L B σ : B →+* B) _ = _ at hβ
  generalize σ'⁻¹ = σ'
  obtain ⟨n, rfl : σ ^ n = σ'⟩ := mem_powers_iff_mem_zpowers.mpr (hσ σ')
  rw [map_pow]
  induction n with
  | zero =>
    simp only [pow_zero, RingEquiv.toRingHom_eq_coe]
    exact Ideal.map_id _
  | succ n IH =>
    simp only [RingEquiv.toRingHom_eq_coe, pow_succ] at IH ⊢
    conv_lhs at IH => rw [← hβ, Ideal.map_map]
    exact IH

variable [IsGalois K L]

include hσ in
open FiniteDimensional in
theorem exists_not_isPrincipal_and_isPrincipal_map_aux
    [IsDedekindDomain A] [Algebra.Unramified A B] (η : Bˣ)
    (hη : Algebra.norm K (algebraMap B L η) = 1)
    (hη' : ¬∃ α : Bˣ, algebraMap B L η = (algebraMap B L α) / σ (algebraMap B L α)) :
    ∃ I : Ideal A, ¬I.IsPrincipal ∧ (I.map (algebraMap A B)).IsPrincipal := by
  have := isCyclic_iff_exists_zpowers_eq_top.2 ⟨σ, (Subgroup.eq_top_iff' _).2 hσ⟩
  obtain ⟨β, hβ_zero, hβ⟩ := groupCohomology.exists_mul_galRestrict_of_norm_eq_one (A := A)
    (B := B) hσ hη
  haveI : IsDomain B :=
    (IsIntegralClosure.equiv A B L (integralClosure A L)).toMulEquiv.isDomain (integralClosure A L)
  have hβ' := Ideal.map_comap_eq_of_unramified_of_galois_invariant A K L B _
    (comap_span_galRestrict_eq_of_cyclic σ hσ (A := A) (B := B) β η hβ)
  refine ⟨(Ideal.span {β}).comap (algebraMap A B), ?_, ?_⟩
  · rintro ⟨⟨γ, hγ : _ = Ideal.span _⟩⟩
    rw [hγ, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_span_singleton] at hβ'
    obtain ⟨a, rfl⟩ := hβ'
    rw [map_mul, AlgEquiv.commutes, mul_left_comm, (mul_right_injective₀ _).eq_iff] at hβ
    · apply hη'
      use a
      conv_rhs => enter [1]; rw [← hβ]
      rw [map_mul, ← algebraMap_galRestrict_apply A]
      refine (mul_div_cancel_right₀ _ ?_).symm
      · rw [ne_eq,
          (injective_iff_map_eq_zero' _).mp (IsIntegralClosure.algebraMap_injective B A L),
          (injective_iff_map_eq_zero' _).mp (galRestrict A K L B σ).injective]
        exact a.isUnit.ne_zero
    · exact (mul_ne_zero_iff.mp hβ_zero).1
  · rw [hβ']
    exact ⟨⟨_, rfl⟩⟩

theorem Ideal.isPrincipal_pow_finrank_of_isPrincipal_map [IsDedekindDomain A] {I : Ideal A}
    (hI : (I.map (algebraMap A B)).IsPrincipal) : (I ^ finrank K L).IsPrincipal := by
  haveI : IsDomain B :=
    (IsIntegralClosure.equiv A B L (integralClosure A L)).toMulEquiv.isDomain (integralClosure A L)
  haveI := IsIntegralClosure.isNoetherian A K L B
  haveI := IsIntegralClosure.isDedekindDomain A K L B
  haveI := IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  have hAB : Function.Injective (algebraMap A B) := by
    refine Function.Injective.of_comp (f := algebraMap B L) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective _ _)
  rw [← Module.isTorsionFree_iff_algebraMap_injective] at hAB
  letI : Algebra (FractionRing A) (FractionRing B) := FractionRing.liftAlgebra _ _
  have : IsScalarTower A (FractionRing A) (FractionRing B) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  have H : RingHom.comp (algebraMap (FractionRing A) (FractionRing B))
    (FractionRing.algEquiv A K).symm.toRingEquiv =
      RingHom.comp (FractionRing.algEquiv B L).symm.toRingEquiv (algebraMap K L) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors A)
    ext
    simp only [RingHom.coe_comp, RingHom.coe_coe,
      AlgEquiv.coe_ringEquiv, Function.comp_apply, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply A B L, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
  have : Algebra.IsSeparable (FractionRing A) (FractionRing B) :=
    Algebra.IsSeparable.of_equiv_equiv _ _ H
  have hLK : finrank (FractionRing A) (FractionRing B) = finrank K L :=
    (Algebra.finrank_eq_of_equiv_equiv (FractionRing.algEquiv A K).symm.toRingEquiv
      (FractionRing.algEquiv B L).symm.toRingEquiv H).symm
  rw [IsFractionRing.finrank_eq A K B L, ← Ideal.relNorm_algebraMap, ← (I.map (algebraMap A B)).span_singleton_generator,
    Ideal.relNorm_singleton]
  exact ⟨⟨_, rfl⟩⟩

theorem exists_not_isPrincipal_and_isPrincipal_map (K L : Type)
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Algebra.Unramified (𝓞 K) (𝓞 L)]
    [h : IsCyclic (L ≃ₐ[K] L)]
    (hKL : Nat.Prime (finrank K L))
    (hKL' : finrank K L ≠ 2) :
    ∃ I : Ideal (𝓞 K), ¬I.IsPrincipal ∧
      (I.map (algebraMap (𝓞 K) (𝓞 L))).IsPrincipal := by
  obtain ⟨⟨σ, hσ⟩⟩ := h
  obtain ⟨η, hη, hη'⟩ := Hilbert92 hKL hKL' σ hσ
  exact exists_not_isPrincipal_and_isPrincipal_map_aux σ hσ η hη (not_exists.mpr hη')

theorem dvd_card_classGroup_of_unramified_isCyclic {K L : Type}
    [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [Algebra.Unramified (𝓞 K) (𝓞 L)]
    [IsCyclic (L ≃ₐ[K] L)]
    (hKL : Nat.Prime (finrank K L))
    (hKL' : finrank K L ≠ 2) :
    finrank K L ∣ Fintype.card (ClassGroup (𝓞 K)) := by
  obtain ⟨I, hI, hI'⟩ := exists_not_isPrincipal_and_isPrincipal_map K L hKL hKL'
  have := Fact.mk hKL
  rw [hKL.dvd_iff_not_coprime]
  exact fun h ↦ hI (isPrincipal_of_isPrincipal_pow_of_coprime h
    (Ideal.isPrincipal_pow_finrank_of_isPrincipal_map hI'))

end FltRegular
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular

end Port_FLT_Deep_Regular_Hilbert94_lean
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular

section Port_FLT_Deep_Regular_KummerField_lean

open scoped NumberField

namespace FltRegular

open scoped NumberField

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K] (hp : p ≠ 2)

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

variable (u : (𝓞 K)ˣ)
  (hcong : (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ (↑u : 𝓞 K) - 1) (hu : ∀ v : K, v ^ p ≠ u)

open Polynomial IsCyclotomicExtension.Rat

open scoped nonZeroDivisors

include hcong hp in
lemma zeta_sub_one_pow_dvd_poly [IsCyclotomicExtension {p} ℚ K] :
    C ((hζ.toInteger - 1 : 𝓞 K) ^ p) ∣
      (C (hζ.toInteger - 1 : 𝓞 K) * X - 1) ^ p + C (u : 𝓞 K) := by
  rw [← dvd_sub_left (_root_.map_dvd C hcong), add_sub_assoc, C.map_sub (u : 𝓞 K), ← sub_add,
    sub_self, map_one, zero_add]
  refine dvd_C_mul_X_sub_one_pow_add_one hpri.out hp _ _ dvd_rfl ?_
  have hassoc : Associated ((hζ.toInteger - 1 : 𝓞 K) ^ (p - 1)) p :=
    IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime _ hζ
  convert mul_dvd_mul_right hassoc.dvd _
  rw [← pow_succ, tsub_add_cancel_of_le (Nat.Prime.one_lt hpri.out).le]

namespace KummersLemma

omit [NumberField K] in
lemma natDegree_poly_aux :
    natDegree ((C (hζ.toInteger - 1 : 𝓞 K) * X - 1) ^ p + C (u : 𝓞 K)) = p := by
  haveI : Fact (Nat.Prime p) := hpri
  rw [natDegree_add_C, natDegree_pow, ← C.map_one, natDegree_sub_C, natDegree_mul_X, natDegree_C,
    zero_add, mul_one]
  exact C_ne_zero.mpr (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt)

omit [NumberField K] in
lemma monic_poly_aux :
    leadingCoeff ((C (hζ.toInteger - 1 : 𝓞 K) * X - 1) ^ p + C (u : 𝓞 K)) =
      (hζ.toInteger - 1 : 𝓞 K) ^ p := by
  haveI : Fact (Nat.Prime p) := hpri
  trans leadingCoeff ((C (hζ.toInteger - 1 : 𝓞 K) * X - 1) ^ p)
  · rw [leadingCoeff, leadingCoeff, coeff_add]
    nth_rewrite 1 [natDegree_add_C]
    convert add_zero _ using 2
    rw [natDegree_poly_aux hζ, coeff_C, if_neg (NeZero.pos p).ne.symm]
  · rw [leadingCoeff_pow, ← C.map_one, leadingCoeff, natDegree_sub_C, natDegree_mul_X]
    · simp only [map_one, natDegree_C, zero_add, coeff_sub, coeff_mul_X, coeff_C,
        coeff_one, sub_zero, one_ne_zero, ↓reduceIte]
    · exact C_ne_zero.mpr (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt)
variable [IsCyclotomicExtension {p} ℚ K]

noncomputable def poly : (𝓞 K)[X] := (zeta_sub_one_pow_dvd_poly hp hζ u hcong).choose

lemma poly_spec :
    C ((hζ.toInteger - 1 : 𝓞 K) ^ p) * poly hp hζ u hcong =
      (C (hζ.toInteger - 1 : 𝓞 K) * X - 1) ^ p + C (u : 𝓞 K) :=
  (zeta_sub_one_pow_dvd_poly hp hζ u hcong).choose_spec.symm

lemma monic_poly : Monic (poly hp hζ u hcong) := by
  haveI : Fact (Nat.Prime p) := hpri
  have := congr_arg leadingCoeff (poly_spec hp hζ u hcong)
  simp only [map_pow, leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_C,
    monic_poly_aux hζ] at this
  refine mul_right_injective₀ ?_ (this.trans (mul_one _).symm)
  exact pow_ne_zero _ (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt)

lemma natDegree_poly : natDegree (poly hp hζ u hcong) = p := by
  haveI : Fact (Nat.Prime p) := hpri
  have := congr_arg natDegree (poly_spec hp hζ u hcong)
  rwa [natDegree_C_mul, natDegree_poly_aux hζ] at this
  exact pow_ne_zero _ (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt)

lemma map_poly : (poly hp hζ u hcong).map (algebraMap (𝓞 K) K) =
    (X - C (1 / (ζ - 1))) ^ p + C (u / (ζ - 1) ^ p : K) := by
  ext i
  have := congr_arg (fun P : (𝓞 K)[X] ↦ (↑(P.coeff i) : K)) (poly_spec hp hζ u hcong)
  change _ = algebraMap (𝓞 K) K _ at this
  rw [← coeff_map] at this
  replace this : (ζ - 1) ^ p * ↑((poly hp hζ u hcong).coeff i) =
    (((C ζ - 1) * X - 1) ^ p).coeff i +
    (C ((algebraMap ((𝓞 K)) K) ↑u)).coeff i := by
      simp only [map_pow, map_sub, map_one, Polynomial.map_add, Polynomial.map_pow,
        Polynomial.map_sub, Polynomial.map_mul, map_C,
        Polynomial.map_one, map_X, coeff_add] at this
      rw [show (algebraMap (𝓞 K) K) hζ.toInteger = ζ from
        IsPrimitiveRoot.coe_toInteger hζ] at this
      have hcoe : (algebraMap (𝓞 K) K) hζ.toInteger = ζ :=
        IsPrimitiveRoot.coe_toInteger hζ
      convert this
      all_goals try rfl
      all_goals
        (simp only [← Polynomial.coeff_map]
         simp only [coeff_map, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
           map_C, Polynomial.map_one]
         rw [← Polynomial.coeff_map, mul_comm, ← Polynomial.coeff_mul_C, mul_comm]
         simp)
      all_goals rw [hcoe]
  apply mul_right_injective₀ (pow_ne_zero p (hζ.sub_one_ne_zero hpri.out.one_lt))
  simp only [coeff_map, one_div, coeff_add, this, mul_add]
  simp_rw [← smul_eq_mul (α := K), ← AddMonoidAlgebra.coeff_smul_apply]
  rw [smul_C, smul_eq_mul, ← _root_.smul_pow, ← mul_div_assoc, mul_div_cancel_left₀, smul_sub,
    smul_C, smul_eq_mul, mul_inv_cancel₀, map_one, Algebra.smul_def, ← C_eq_algebraMap, map_sub,
    map_one]
  · exact hζ.sub_one_ne_zero hpri.out.one_lt
  · exact pow_ne_zero _ (hζ.sub_one_ne_zero hpri.out.one_lt)

include hu in
lemma irreducible_map_poly :
    Irreducible ((poly hp hζ u hcong).map (algebraMap (𝓞 K) K)) := by
  rw [map_poly]
  refine Irreducible.of_map (f := algEquivAevalXAddC (1 / (ζ - 1))) ?_
  simp only [one_div, map_add, algEquivAevalXAddC_apply, map_pow, map_sub, aeval_X, aeval_C,
    algebraMap_eq, add_sub_cancel_right]
  rw [← sub_neg_eq_add, ← (C : K →+* _).map_neg]
  apply X_pow_sub_C_irreducible_of_prime hpri.out
  intro b hb
  apply hu (- b * (ζ - 1))
  rw [mul_pow, (hpri.out.odd_of_ne_two hp).neg_pow, hb, neg_neg,
    div_mul_cancel₀ _ (pow_ne_zero _ (hζ.sub_one_ne_zero hpri.out.one_lt))]

theorem aeval_poly {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) (m : ℕ) :
    aeval (((1 : L) - ζ ^ m • α) / (algebraMap K L (ζ - 1))) (poly hp hζ u hcong) = 0 := by
  have hζ' : algebraMap K L ζ - 1 ≠ 0 := by
    simpa using (algebraMap K L).injective.ne (hζ.sub_one_ne_zero hpri.out.one_lt)
  rw [map_sub, map_one]
  have := congr_arg (aeval ((1 - ζ ^ m • α) / (algebraMap K L (ζ - 1))))
    (poly_spec hp hζ u hcong)
  have hcoe : (algebraMap (𝓞 K) L) (↑hζ.toInteger) = algebraMap K L ζ := rfl
  have hcoe1 : (algebraMap (𝓞 K) L) ↑u = algebraMap K L ↑↑u := rfl
  simp only [map_sub, map_one, map_pow, map_mul, aeval_C, _root_.smul_pow, hcoe, e, hcoe1, map_add,
    aeval_X, ← mul_div_assoc, mul_div_cancel_left₀ _ hζ', sub_sub_cancel_left,
    (hpri.out.odd_of_ne_two hp).neg_pow] at this
  rw [← pow_mul, mul_comm m, pow_mul, hζ.pow_eq_one, one_pow, one_smul, neg_add_cancel,
    mul_eq_zero] at this
  exact this.resolve_left (pow_ne_zero _ hζ')

def polyRoot {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) (m : ℕ) : 𝓞 L :=
  ⟨((1 : L) - ζ ^ m • α) / (algebraMap K L (ζ - 1)), isIntegral_trans _
      ⟨poly hp hζ u hcong, monic_poly hp hζ u hcong, aeval_poly hp hζ u hcong α e m⟩⟩

theorem roots_poly {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) :
    roots ((poly hp hζ u hcong).map (algebraMap (𝓞 K) L)) =
      (Finset.range p).val.map
        (fun i ↦ ((1 : L) - ζ ^ i • α) / (algebraMap K L (ζ - 1))) := by
  by_cases hα : α = 0
  · rw [hα, zero_pow (NeZero.ne p)] at e
    exact (((algebraMap (𝓞 K) L).isUnit_map u.isUnit).ne_zero e.symm).elim
  have hζ' : algebraMap K L ζ - 1 ≠ 0 := by
    simpa using (algebraMap K L).injective.ne (hζ.sub_one_ne_zero hpri.out.one_lt)
  classical
  symm; apply Multiset.eq_of_le_of_card_le
  · rw [← Finset.image_val_of_injOn, Finset.val_le_iff_val_subset]
    · intro x hx
      simp only [Finset.image_val, Finset.range_val, Multiset.mem_dedup, Multiset.mem_map,
        Multiset.mem_range] at hx
      obtain ⟨m, _, rfl⟩ := hx
      rw [mem_roots, IsRoot.def, eval_map, ← aeval_def, aeval_poly hp hζ u hcong α e]
      exact ((monic_poly hp hζ u hcong).map (algebraMap (𝓞 K) L)).ne_zero
    · intros i hi j hj e
      apply (hζ.map_of_injective (algebraMap K L).injective).injOn_pow_mul hα hi hj
      apply_fun (1 - · * (algebraMap K L ζ - 1)) at e
      dsimp only at e
      simpa only [Nat.cast_one, map_sub, map_one, Algebra.smul_def, map_pow,
        div_mul_cancel₀ _ hζ', sub_sub_cancel] using e
  · simp only [Finset.range_val, Multiset.card_map, Multiset.card_range]
    refine (Polynomial.card_roots' _).trans ?_
    rw [(monic_poly hp hζ u hcong).natDegree_map, natDegree_poly hp hζ]

theorem splits_poly {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) :
    ((poly hp hζ u hcong).map (algebraMap (𝓞 K) L)).Splits := by
  rw [splits_iff_card_roots, roots_poly hp hζ u hcong α e,
    (monic_poly hp hζ u hcong).natDegree_map, natDegree_poly hp hζ,
    Finset.range_val, Multiset.card_map, Multiset.card_range]

theorem map_poly_eq_prod {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) :
    (poly hp hζ u hcong).map (algebraMap (𝓞 K) (𝓞 L)) =
      ∏ i ∈ Finset.range p, (X - C (polyRoot hp hζ u hcong α e i)) := by
  apply map_injective (algebraMap (𝓞 L) L) Subtype.coe_injective
  rw [← coe_mapRingHom, map_prod, coe_mapRingHom, map_map, ← IsScalarTower.algebraMap_eq,
    (splits_poly hp hζ u hcong α e).eq_prod_roots_of_monic ((monic_poly hp hζ u hcong).map _),
    roots_poly hp hζ u hcong α e, Multiset.map_map, ← Finset.prod_eq_multiset_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  congr 1

include hu in
lemma minpoly_polyRoot'' {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) (i) :
    minpoly K (polyRoot hp hζ u hcong α e i : L) =
      (poly hp hζ u hcong).map (algebraMap (𝓞 K) K) := by
  have : IsIntegral K (polyRoot hp hζ u hcong α e i : L) :=
    IsIntegral.tower_top (polyRoot hp hζ u hcong α e i).prop
  apply eq_of_monic_of_associated (minpoly.monic this) ((monic_poly hp hζ u hcong).map _)
  refine Irreducible.associated_of_dvd (minpoly.irreducible this)
    (irreducible_map_poly hp hζ u hcong hu) (minpoly.dvd _ _ ?_)
  rw [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq, ← aeval_def]
  exact aeval_poly hp hζ u hcong α e i

include hu in
lemma minpoly_polyRoot' {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) (i) :
    minpoly (𝓞 K) (polyRoot hp hζ u hcong α e i : L) = (poly hp hζ u hcong) := by
  apply map_injective (algebraMap (𝓞 K) K) Subtype.coe_injective
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' K]
  · exact minpoly_polyRoot'' hp hζ u hcong hu α e i
  · exact IsIntegral.tower_top (polyRoot hp hζ u hcong α e i).prop

lemma separable_poly_aux {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) : Separable ((poly hp hζ u hcong).map
    (algebraMap (𝓞 K) (𝓞 L))) := by
  have hζ' : algebraMap K L ζ - 1 ≠ 0 := by
    simpa using (algebraMap K L).injective.ne (hζ.sub_one_ne_zero hpri.out.one_lt)
  rw [map_poly_eq_prod (e := e)]
  refine separable_prod' ?_ (fun _ _ ↦ separable_X_sub_C)
  intros i hi j hj hij
  apply isCoprime_X_sub_C_of_isUnit_sub
  obtain ⟨v, hv⟩ : Associated (hζ.toInteger - 1 : 𝓞 K)
      ((hζ.toInteger : 𝓞 K) ^ j - (hζ.toInteger : 𝓞 K) ^ i) := by
    refine hζ.toInteger_isPrimitiveRoot.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime
      hpri.out ?_ ?_ ?_
    · rw [Finset.mem_coe, mem_nthRootsFinset (NeZero.pos p), ← pow_mul, mul_comm, pow_mul,
        hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
    · rw [Finset.mem_coe, mem_nthRootsFinset (NeZero.pos p), ← pow_mul, mul_comm, pow_mul,
        hζ.toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
    · exact mt (hζ.toInteger_isPrimitiveRoot.injOn_pow hj hi) hij.symm
  rw [NumberField.RingOfIntegers.ext_iff] at hv
  have hcoe : (algebraMap (𝓞 K) K) (↑hζ.toInteger) = ζ := rfl
  simp only [map_mul, map_sub, map_one, map_pow, hcoe] at hv
  have hα : IsIntegral (𝓞 K) α := by
    apply IsIntegral.of_pow (NeZero.pos p); rw [e]; exact isIntegral_algebraMap
  have : IsUnit (⟨α, isIntegral_trans _ hα⟩ : 𝓞 L) := by
    rw [← isUnit_pow_iff (NeZero.pos p).ne.symm]
    have hpow : (⟨α, isIntegral_trans _ hα⟩ : 𝓞 L) ^ p = algebraMap (𝓞 K) (𝓞 L) ↑u := by
      ext; simp only [SubmonoidClass.coe_pow, e]; rfl
    rw [hpow]
    exact (algebraMap (𝓞 K) (𝓞 L)).isUnit_map u.isUnit
  convert ((algebraMap (𝓞 K) (𝓞 L)).isUnit_map v.isUnit).mul this using 1
  ext
  simp only [NumberField.RingOfIntegers.coe_eq_algebraMap]
  rw [map_sub]
  have hroot : ∀ m : ℕ, (algebraMap (𝓞 L) L) (polyRoot hp hζ u hcong α e m) =
      (1 - ζ ^ m • α) / ((algebraMap K L) ζ - 1) := by
    intro m
    simp only [polyRoot, NumberField.RingOfIntegers.map_mk, map_sub, map_one]
  have hvL : ((algebraMap K L) ζ - 1) * (algebraMap (𝓞 K) L ↑v) =
      (algebraMap K L) ζ ^ j - (algebraMap K L) ζ ^ i := by
    have h := congrArg (algebraMap K L) hv
    have hcomp : (algebraMap K L) ((algebraMap (𝓞 K) K) ↑v) =
        (algebraMap (𝓞 K) L) ↑v := rfl
    simpa only [map_mul, map_sub, map_one, map_pow, hcomp] using h
  simp only [hroot, map_mul, NumberField.RingOfIntegers.map_mk,
    IsScalarTower.algebraMap_apply]
  rw [← sub_div, sub_sub_sub_cancel_left, ← sub_smul, Algebra.smul_def, map_sub, map_pow,
    map_pow, ← hvL, mul_assoc]
  exact mul_div_cancel_left₀ _ hζ'

set_option backward.isDefEq.respectTransparency false in
include hu in
open scoped KummerExtension in
attribute [local instance] Ideal.Quotient.field in
lemma separable_poly (I : Ideal (𝓞 K)) [I.IsMaximal] :
    Separable ((poly hp hζ u hcong).map (Ideal.Quotient.mk I)) := by
  let L := K[p√(u : K)]
  have := Fact.mk (X_pow_sub_C_irreducible_of_prime hpri.out hu)
  let J := I.map (algebraMap (𝓞 K) (𝓞 L))
  let i : 𝓞 K ⧸ I →+* 𝓞 L ⧸ J := Ideal.quotientMap _
    (algebraMap (𝓞 K) (𝓞 L)) Ideal.le_comap_map
  haveI : Nontrivial (𝓞 L ⧸ J) := by
    apply Ideal.Quotient.nontrivial_iff.mpr
    rw [ne_eq, Ideal.map_eq_top_iff]
    · exact Ideal.IsMaximal.ne_top ‹_›
    · intros x y e; ext; exact (algebraMap K L).injective (congr_arg Subtype.val e)
    · intros x; exact IsIntegral.tower_top (IsIntegralClosure.isIntegral ℤ L x)
  rw [← Polynomial.separable_map i, map_map, Ideal.quotientMap_comp_mk, ← map_map]
  exact Separable.map <|
    separable_poly_aux hp hζ u hcong (AdjoinRoot.root _) (root_X_pow_sub_C_pow _ _)

lemma polyRoot_spec {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) (i) :
    α = (ζ ^ i)⁻¹ • (1 - (ζ - 1) • (polyRoot hp hζ u hcong α e i : L)) := by
  apply smul_right_injective (M := L) (r := ζ ^ i) (pow_ne_zero _ <| hζ.ne_zero
    (NeZero.pos p).ne.symm)
  simp only [polyRoot, map_sub, map_one, NumberField.RingOfIntegers.map_mk,
    Algebra.smul_def (ζ - 1), ← mul_div_assoc,
    mul_div_cancel_left₀ _
      ((hζ.map_of_injective (algebraMap K L).injective).sub_one_ne_zero hpri.out.one_lt),
    sub_sub_cancel, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ <| hζ.ne_zero (NeZero.pos p).ne.symm), one_smul]

lemma mem_adjoin_polyRoot {L : Type*} [Field L] [Algebra K L] (α : L)
    (e : α ^ p = algebraMap K L u) (i) :
    α ∈ Algebra.adjoin K {(polyRoot hp hζ u hcong α e i : L)} := by
  conv => enter [2]; rw [polyRoot_spec hp hζ u hcong α e i]
  exact Subalgebra.smul_mem _ (sub_mem (one_mem _)
    (Subalgebra.smul_mem _ (Algebra.self_mem_adjoin_singleton K _) _)) _

include hu hp hζ hcong in
attribute [local instance] Ideal.Quotient.field in
lemma isUnramified (L) [Field L] [Algebra K L] [IsSplittingField K L (X ^ p - C (u : K))] :
    Algebra.Unramified (𝓞 K) (𝓞 L) := by
  let α := polyRoot hp hζ u hcong _ (rootOfSplitsXPowSubC_pow _ L) 0
  haveI := Polynomial.IsSplittingField.finiteDimensional L (X ^ p - C (u : K))
  haveI : Module.Finite (𝓞 K) (𝓞 L) := IsIntegralClosure.finite (𝓞 K) K L (𝓞 L)
  have hα : Algebra.adjoin K {(α : L)} = ⊤ := by
    rw [eq_top_iff, ← Algebra.adjoin_root_eq_top_of_isSplittingField
      ⟨ζ, (mem_primitiveRoots (NeZero.pos p)).mpr hζ⟩
      (X_pow_sub_C_irreducible_of_prime hpri.out hu) (rootOfSplitsXPowSubC_pow (u : K) L),
      Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact mem_adjoin_polyRoot hp hζ u hcong _ _ 0

  have key : ∀ (P : Ideal (𝓞 L)) [P.IsPrime], Algebra.IsUnramifiedAt (𝓞 K) P := by
    intro P hP
    by_cases hPbot : P = ⊥
    · subst P
      haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
      haveI : FiniteDimensional ℚ L := Module.Finite.trans K L
      haveI : NumberField L := ⟨⟩
      haveI : IsLocalization (𝓞 L)⁰ (Localization.AtPrime (⊥ : Ideal (𝓞 L))) := by
        convert (inferInstance : IsLocalization (⊥ : Ideal (𝓞 L)).primeCompl
          (Localization.AtPrime (⊥ : Ideal (𝓞 L))))
        ext; simp [Ideal.primeCompl]
      refine (Algebra.FormallyUnramified.iff_of_equiv
        ((IsLocalization.algEquiv (𝓞 L)⁰ L _).restrictScalars (𝓞 K))).mp ?_
      haveI : Algebra.FormallyUnramified (𝓞 K) K :=
        Algebra.FormallyUnramified.of_isLocalization (𝓞 K)⁰
      haveI : Algebra.FormallyUnramified K L :=
        Algebra.FormallyUnramified.of_isSeparable K L
      exact .comp (𝓞 K) K L
    · refine Algebra.isUnramifiedAt_of_separable_minpoly_of_isIntegral K L P hPbot α
        (IsIntegral.tower_top α.prop) hα ?_
      rw [minpoly_polyRoot' hp hζ u hcong hu]
      have hPbot' : P.under (𝓞 K) ≠ ⊥ := Ideal.under_ne_bot (𝓞 K) hPbot
      haveI : (P.under (𝓞 K)).IsMaximal :=
        (inferInstance : (P.under (𝓞 K)).IsPrime).isMaximal hPbot'
      exact separable_poly hp hζ u hcong hu (P.under (𝓞 K))
  haveI : Algebra.FormallyUnramified (𝓞 K) (𝓞 L) := by
    rw [← Algebra.unramifiedLocus_eq_univ_iff]
    exact Set.eq_univ_of_forall fun P ↦ key P.asIdeal
  exact ⟨inferInstance, inferInstance⟩

end KummersLemma
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular FltRegularPort.Internal.FltRegular.KummersLemma

end FltRegular
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular FltRegularPort.Internal.FltRegular.KummersLemma

end Port_FLT_Deep_Regular_KummerField_lean
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular FltRegularPort.Internal.FltRegular.KummersLemma

section Port_FLT_Deep_Regular_KummersLemma_lean

open Polynomial Module

open scoped NumberField

namespace FltRegular

section Feeders

variable {K : Type*} {p : ℕ} [hpri : Fact p.Prime] [Field K] [CharZero K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

lemma quotient_zeta_sub_one_comp_aut [IsCyclotomicExtension {p} ℚ K] (σ : 𝓞 K →+* 𝓞 K) :
    (Ideal.Quotient.mk (Ideal.span {(hζ.toInteger : 𝓞 K) - 1})).comp σ = Ideal.Quotient.mk _ := by
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  apply RingHom.toIntAlgHom_injective
  apply hζ.integralPowerBasis.algHom_ext
  have h : hζ.integralPowerBasis.gen = hζ.toInteger := by
    simp only [IsPrimitiveRoot.integralPowerBasis_gen]
  rw [h]
  simp only [RingHom.toIntAlgHom, AlgHom.coe_mk, RingHom.coe_comp, Function.comp_apply]
  rw [← sub_eq_zero, ← Ideal.Quotient.mk_eq_mk, ← Ideal.Quotient.mk_eq_mk,
    ← Submodule.Quotient.mk_sub, Ideal.Quotient.mk_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]
  by_cases hne : σ hζ.toInteger = hζ.toInteger
  · rw [hne, sub_self]
    exact dvd_zero _
  · refine (hζ.toInteger_isPrimitiveRoot.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime
      hpri.out ?_ ?_ hne).dvd
    · rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset (NeZero.pos p) 1, ← map_pow,
        hζ.toInteger_isPrimitiveRoot.pow_eq_one, map_one]
    · rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset (NeZero.pos p) 1]
      exact hζ.toInteger_isPrimitiveRoot.pow_eq_one

open NumberField.RingOfIntegers in

lemma zeta_sub_one_dvd_trace_sub_smul [IsCyclotomicExtension {p} ℚ K] (x : 𝓞 K) :
    (hζ.toInteger - 1 : 𝓞 K) ∣ Algebra.trace ℤ _ x - (p - 1) • x := by
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  letI := IsCyclotomicExtension.isGalois {p} ℚ K
  have : (Algebra.trace ℤ _ x : 𝓞 K) = ∑ σ : K ≃ₐ[ℚ] K, (mapAlgHom σ).toRingHom x := by
    apply (show Function.Injective (algebraMap (𝓞 K) K) from Subtype.val_injective)
    rw [← eq_intCast (algebraMap ℤ (𝓞 K)), ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply ℤ ℚ K, eq_intCast, Algebra.coe_trace_int,
      trace_eq_sum_automorphisms, map_sum]
    rfl
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, this, map_sum]
  simp_rw [← RingHom.comp_apply, quotient_zeta_sub_one_comp_aut hζ]
  rw [Finset.sum_const, map_nsmul, sub_eq_zero, Finset.card_univ, ← Nat.card_eq_fintype_card,
    IsGalois.card_aut_eq_finrank,
    IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat (NeZero.pos p)),
    Nat.totient_prime hpri.out]

theorem norm_add_one_smul_of_isUnit {K : Type*} [Field K] [NumberField K] {p : ℕ}
    (hpri : p.Prime) (hp : p ≠ 2) (x : 𝓞 K) (hx : IsUnit (1 + p • x)) :
    Algebra.norm ℤ (1 + p • x) = 1 := by

  have H : Algebra.norm ℤ (1 + p • x) = 1 ∨ Algebra.norm ℤ (1 + p • x) = -1 := by
    apply Int.natAbs_eq_iff.mp
    apply (Int.cast_injective (α := ℚ)).comp Nat.cast_injective
    simp only [Int.cast_abs, Function.comp_apply, Nat.cast_one, Int.cast_one, ← Int.abs_eq_natAbs,
      Algebra.coe_norm_int, ← NumberField.isUnit_iff_norm.mp hx,
      NumberField.RingOfIntegers.coe_norm]
  have : Algebra.norm ℤ (1 + p • x) ≠ -1 := by
    intro e
    apply hp
    obtain ⟨r, hr⟩ := Algebra.norm_one_add_smul (p : ℤ) x
    have : (p : ℤ) * (- Algebra.trace ℤ _ x - r * p) = 2 := by
      rw [zsmul_eq_mul, Int.cast_natCast, ← nsmul_eq_mul, e, eq_comm, ← sub_eq_zero] at hr
      rw [eq_comm, ← sub_eq_zero, ← hr]
      ring
    exact (Nat.prime_two.eq_one_or_self_of_dvd _
      (Int.natCast_dvd_natCast.mp ⟨_, this.symm⟩)).resolve_left hpri.ne_one
  exact H.resolve_right this

theorem zeta_sub_one_pow_dvd_norm_sub_pow [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] (x : 𝓞 K) :
    (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ (Algebra.norm ℤ (1 + p • x) : 𝓞 K) - 1 + p • x := by
  obtain ⟨r, hr⟩ := Algebra.norm_one_add_smul (p : ℤ) x
  obtain ⟨s, hs⟩ := zeta_sub_one_dvd_trace_sub_smul hζ x
  obtain ⟨t, ht⟩ := (IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime _ hζ).dvd
  rw [sub_eq_iff_eq_add] at hs
  simp only [zsmul_eq_mul, Int.cast_natCast] at hr
  simp only [nsmul_eq_mul, hr, Int.cast_add, Int.cast_one, Int.cast_mul, hs, NeZero.pos p,
    Nat.cast_pred, Int.cast_natCast, Int.cast_pow]
  suffices (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ (hζ.toInteger - 1) * p * s + (p : 𝓞 K) ^ 2 * (r + x) by
    convert this using 1; ring
  apply dvd_add
  · apply dvd_mul_of_dvd_left
    rw [ht, ← mul_assoc, ← pow_succ', tsub_add_cancel_of_le (Nat.Prime.one_lt hpri.out).le]
    exact dvd_mul_right _ _
  · rw [ht, mul_pow, ← pow_mul, mul_assoc]
    apply dvd_mul_of_dvd_left
    apply pow_dvd_pow
    zify [(Nat.Prime.one_lt hpri.out).le]
    linarith only [Nat.Prime.two_le hpri.out]

end Feeders
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular FltRegularPort.Internal.FltRegular.KummersLemma

section KummersLemma

variable {K : Type} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] (hp : p ≠ 2) [Fintype (ClassGroup (𝓞 K))]
  (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K))
  {ζ : K} (hζ : IsPrimitiveRoot ζ p)

include hp hreg in

theorem exists_pow_eq_of_zeta_sub_one_pow_dvd_sub_one {u : (𝓞 K)ˣ}
    (hcong : (hζ.toInteger - 1 : 𝓞 K) ^ p ∣ (u : 𝓞 K) - 1) : ∃ v : K, v ^ p = u := by
  by_contra! hu
  have hirr := X_pow_sub_C_irreducible_of_prime hpri.out hu
  have := Fact.mk hirr
  let L := AdjoinRoot (X ^ p - C (u : K))
  have := isSplittingField_AdjoinRoot_X_pow_sub_C
    ⟨ζ, (mem_primitiveRoots (NeZero.pos p)).mpr hζ⟩ hirr
  have := isGalois_of_isSplittingField_X_pow_sub_C
    ⟨ζ, (mem_primitiveRoots (NeZero.pos p)).mpr hζ⟩ hirr L
  have := IsSplittingField.finiteDimensional L (X ^ p - C (u : K))
  have := isCyclic_of_isSplittingField_X_pow_sub_C
    ⟨ζ, (mem_primitiveRoots (NeZero.pos p)).mpr hζ⟩ hirr L
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  have : FiniteDimensional ℚ L := Module.Finite.trans K L
  have : NumberField L := ⟨⟩
  have hKL : Module.finrank K L = p :=
    finrank_of_isSplittingField_X_pow_sub_C
      ⟨ζ, (mem_primitiveRoots (NeZero.pos p)).mpr hζ⟩ hirr L
  have := KummersLemma.isUnramified hp hζ u hcong hu L
  have := dvd_card_classGroup_of_unramified_isCyclic (hKL.symm ▸ hpri.out) (hKL.symm ▸ hp)
  rw [hKL, hpri.out.dvd_iff_not_coprime] at this
  exact this (by convert hreg)

include hp hreg in

theorem eq_pow_prime_of_unit_of_congruent (u : (𝓞 K)ˣ)
    (hcong : ∃ n : ℤ, (p : 𝓞 K) ∣ (u - n : 𝓞 K)) :
    ∃ v, u = v ^ p := by
  obtain ⟨ζ', hζ'⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (B := K)
    (Set.mem_singleton p) (NeZero.ne p)
  obtain ⟨x, hx⟩ : (p : 𝓞 K) ∣ (↑(u ^ (p - 1)) : 𝓞 K) - 1 := by
    obtain ⟨n, hn⟩ := hcong
    have hn' : (p : ℤ) ∣ n ^ (p - 1) - 1 := by
      refine Int.modEq_iff_dvd.mp (Int.ModEq.pow_card_sub_one_eq_one hpri.out ?_).symm
      rw [isCoprime_comm, (Nat.prime_iff_prime_int.mp hpri.out).coprime_iff_not_dvd]
      intro h
      replace h := Int.cast_dvd_cast (α := 𝓞 K) _ _ h
      simp only [Int.cast_natCast, ← dvd_iff_dvd_of_dvd_sub hn] at h
      refine hζ'.zeta_sub_one_prime'.not_unit ((isUnit_pow_iff ?_).mp
        (isUnit_of_dvd_unit
          ((IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime _ hζ').dvd.trans h)
          u.isUnit))
      simpa only [ne_eq, tsub_eq_zero_iff_le, not_le] using hpri.out.one_lt
    replace hn' := Int.cast_dvd_cast (α := 𝓞 K) _ _ hn'
    simp only [Int.cast_natCast, Int.cast_sub, Int.cast_pow, Int.cast_one] at hn'
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem,
      RingHom.map_sub, sub_eq_zero] at hn hn' ⊢
    rw [Units.val_pow_eq_pow_val, RingHom.map_pow, hn, ← RingHom.map_pow, hn']
  have : (hζ'.toInteger - 1 : 𝓞 K) ^ p ∣ (↑(u ^ (p - 1)) : 𝓞 K) - 1 := by
    rw [hx]
    rw [sub_eq_iff_eq_add, add_comm] at hx
    have H : Algebra.norm ℤ (1 + p • x) = 1 := norm_add_one_smul_of_isUnit hpri.out
      hp x (by rw [nsmul_eq_mul, ← hx]; exact Units.isUnit _)
    have := H ▸ zeta_sub_one_pow_dvd_norm_sub_pow hζ' x
    simpa [ge_iff_le, Int.cast_one, sub_self, nsmul_eq_mul, Nat.cast_mul, PNat.pos,
      Nat.cast_pred, zero_sub, IsUnit.mul_iff, ne_eq, tsub_eq_zero_iff_le, not_le, dvd_neg,
      Units.isUnit, and_true, zero_add] using this
  obtain ⟨v, hv⟩ := exists_pow_eq_of_zeta_sub_one_pow_dvd_sub_one hp hreg hζ' this
  have hv' : IsIntegral ℤ v :=
    IsIntegral.of_pow (NeZero.pos p) (hv ▸ NumberField.RingOfIntegers.isIntegral_coe _)
  set w : 𝓞 K := ⟨v, hv'⟩
  have : IsUnit w := by
    rw [← isUnit_pow_iff (NeZero.pos p).ne.symm]; convert (u ^ (p - 1) : (𝓞 K)ˣ).isUnit; ext
    exact hv
  have hv'' : this.unit ^ p = u ^ (p - 1) := by
    ext; exact hv
  use u / this.unit
  rw [div_pow, hv'', div_eq_mul_inv, ← pow_sub _ tsub_le_self,
    tsub_tsub_cancel_of_le (Nat.Prime.one_lt hpri.out).le, pow_one]

end KummersLemma
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular FltRegularPort.Internal.FltRegular.KummersLemma

end FltRegular
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular FltRegularPort.Internal.FltRegular.KummersLemma

end Port_FLT_Deep_Regular_KummersLemma_lean
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular FltRegularPort.Internal.FltRegular.KummersLemma

section Port_FLT_Deep_Regular_InductionStep_lean

open scoped nonZeroDivisors NumberField

namespace FltRegular

variable {K : Type*} {p : ℕ} [Field K] [CharZero K] {ζ : K}

open scoped nonZeroDivisors
open Polynomial

theorem isPrincipal_of_isPrincipal_pow_of_Coprime'
    {A K : Type*} [CommRing A] [IsDedekindDomain A] [Fintype (ClassGroup A)]
    [Field K] [Algebra A K] [IsFractionRing A K] (p : ℕ)
    (H : p.Coprime <| Fintype.card <| ClassGroup A) (I : FractionalIdeal A⁰ K)
    (hI : (↑(I ^ p) : Submodule A K).IsPrincipal) : (I : Submodule A K).IsPrincipal := by
  by_cases Izero : I = 0
  · rw [Izero, FractionalIdeal.coe_zero]
    exact bot_isPrincipal
  rw [← Ne, ← isUnit_iff_ne_zero] at Izero
  change Submodule.IsPrincipal ((Izero.unit' : FractionalIdeal A⁰ K) : Submodule A K)
  rw [← ClassGroup.mk_eq_one_iff, ← orderOf_eq_one_iff, ← Nat.dvd_one, ← H, Nat.dvd_gcd_iff]
  refine ⟨?_, orderOf_dvd_card⟩
  rw [orderOf_dvd_iff_pow_eq_one, ← map_pow, ClassGroup.mk_eq_one_iff]
  simp only [Units.val_pow_eq_pow_val, IsUnit.val_unit', hI]

namespace CaseII

open scoped nonZeroDivisors NumberField
open Polynomial IsCyclotomicExtension.Rat

variable {K : Type} {p : ℕ} [NeZero p] [Field K] [NumberField K] (hp : p ≠ 2)

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p) {x y z : 𝓞 K} {ε : (𝓞 K)ˣ}

local notation3 "π" => hζ.toInteger - 1
local notation3 "𝔭" => Ideal.span {π}
local notation3 "𝔦" η => Ideal.span {(x + y * η : 𝓞 K)}
local notation3 "𝔵" => Ideal.span {x}
local notation3 "𝔶" => Ideal.span {y}
local notation3 "𝔷" => Ideal.span {z}

variable {m : ℕ} (e : x ^ p + y ^ p = ε * ((hζ.toInteger - 1) ^ (m + 1) * z) ^ p)
variable (hy : ¬ hζ.toInteger - 1 ∣ y) (hz : ¬ hζ.toInteger - 1 ∣ z)
variable (η : nthRootsFinset p (1 : 𝓞 K))

include e in
omit [NumberField K] in
lemma zeta_sub_one_dvd : π ∣ x ^ p + y ^ p := by
  rw [e, mul_pow, ← pow_mul]
  apply dvd_mul_of_dvd_right
  apply dvd_mul_of_dvd_left
  apply dvd_pow_self
  simp [NeZero.ne]

include e in
omit [NumberField K] in
lemma span_pow_add_pow_eq :
    Ideal.span {x ^ p + y ^ p} = (𝔭 ^ (m + 1) * 𝔷) ^ p := by
  simp only [e, ← Ideal.span_singleton_pow, ← Ideal.span_singleton_mul_span_singleton]
  convert one_mul _
  rw [Ideal.one_eq_top, Ideal.span_singleton_eq_top]
  exact ε.isUnit

local notation3 "𝔪" => gcd 𝔵 𝔶

include hy in
lemma m_ne_zero : 𝔪 ≠ 0 := by
  simp_rw [Ne, gcd_eq_zero_iff, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  rintro ⟨rfl, rfl⟩
  exact hy (dvd_zero _)

variable [hpri : Fact p.Prime]

include hp hζ e hz in
omit [NumberField K] in
lemma x_plus_y_mul_ne_zero : x + y * η ≠ 0 := by
  intro hη
  have : x + y * η ∣ x ^ p + y ^ p := by
    rw [hζ.toInteger_isPrimitiveRoot.pow_add_pow_eq_prod_add_mul _ _ <| Nat.odd_iff.2 <|
      hpri.out.eq_two_or_odd.resolve_left hp]
    simp_rw [mul_comm _ y]
    exact Finset.dvd_prod_of_mem _ η.prop
  rw [hη, zero_dvd_iff, e] at this
  simp only [mul_eq_zero, Units.ne_zero, pow_eq_zero_iff (NeZero.ne p), false_or] at this
  rw [this.resolve_left (pow_ne_zero (m + 1)
    (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt))] at hz
  exact hz (dvd_zero _)

variable [IsCyclotomicExtension {p} ℚ K]

include e hp in
lemma one_sub_zeta_dvd_zeta_pow_sub : π ∣ x + y * η := by
  letI : Fact (Nat.Prime p) := hpri
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  have h := zeta_sub_one_dvd hζ e
  have root_eq_one_mod {ξ : 𝓞 K} (hξ : ξ ∈ nthRootsFinset p (1 : 𝓞 K)) :
      Ideal.Quotient.mk 𝔭 ξ = 1 := by
    obtain ⟨i, -, hi⟩ := hζ.toInteger_isPrimitiveRoot.eq_pow_of_pow_eq_one
      ((Polynomial.mem_nthRootsFinset (NeZero.pos p) 1).1 hξ)
    rw [← hi, map_pow]
    rw [← Ideal.Quotient.algebraMap_eq, eq_one_mod_one_sub, one_pow]
  replace h :
      ∏ _η ∈ nthRootsFinset p (1 : 𝓞 K),
        Ideal.Quotient.mk 𝔭 (x + y * η : 𝓞 K) = 0 := by
    rw [hζ.toInteger_isPrimitiveRoot.pow_add_pow_eq_prod_add_mul _ _ <| Nat.odd_iff.2 <|
      hpri.out.eq_two_or_odd.resolve_left hp, ← Ideal.Quotient.eq_zero_iff_dvd, map_prod] at h
    convert h using 2 with η' hη'
    rw [map_add, map_add, map_mul, map_mul, root_eq_one_mod hη', root_eq_one_mod η.prop,
      one_mul, mul_one]
  rw [Finset.prod_const, ← map_pow, Ideal.Quotient.eq_zero_iff_dvd] at h
  exact hζ.zeta_sub_one_prime'.dvd_of_dvd_pow h

include hp hζ e in
lemma div_one_sub_zeta_mem : IsIntegral ℤ ((x + y * η : 𝓞 K) / (ζ - 1)) := by
  obtain ⟨⟨a, ha⟩, e⟩ := one_sub_zeta_dvd_zeta_pow_sub hp hζ e η
  rw [e]
  have h2 : ((π * ⟨a, ha⟩ : 𝓞 K) : K) / (ζ - 1) = a := by
    have hcoe : (algebraMap (𝓞 K) K) hζ.toInteger = ζ := hζ.coe_toInteger
    simp only [NumberField.RingOfIntegers.coe_eq_algebraMap, map_mul, map_sub, map_one,
      NumberField.RingOfIntegers.map_mk, hcoe]
    exact mul_div_cancel_left₀ a (hζ.sub_one_ne_zero hpri.out.one_lt)
  rw [h2]
  exact ha

def divZetaSubOne : nthRootsFinset p (1 : 𝓞 K) → 𝓞 K :=
fun η ↦ ⟨(x + y * η.1) / (ζ - 1), div_one_sub_zeta_mem hp hζ e η⟩

lemma div_zeta_sub_one_mul_zeta_sub_one (η) :
    divZetaSubOne hp hζ e η * (π) = x + y * η := by
  ext
  have hcoe : (algebraMap (𝓞 K) K) hζ.toInteger = ζ := hζ.coe_toInteger
  simp only [divZetaSubOne, NumberField.RingOfIntegers.coe_eq_algebraMap, map_mul, map_add,
    NumberField.RingOfIntegers.map_mk, map_sub, map_one, hcoe]
  exact div_mul_cancel₀ _ (hζ.sub_one_ne_zero hpri.out.one_lt)

lemma div_zeta_sub_one_sub (η₁ η₂) (hη : η₁ ≠ η₂) :
    Associated y (divZetaSubOne hp hζ e η₁ - divZetaSubOne hp hζ e η₂) := by
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  apply Associated.of_mul_right _ (Associated.refl (π))
    (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt)
  have key : (divZetaSubOne hp hζ e η₁ - divZetaSubOne hp hζ e η₂) * (π)
      = y * ((η₁ : 𝓞 K) - η₂) := by
    rw [sub_mul, div_zeta_sub_one_mul_zeta_sub_one, div_zeta_sub_one_mul_zeta_sub_one]
    ring
  rw [key]
  exact Associated.mul_left _
    (hζ.toInteger_isPrimitiveRoot.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime
      hpri.out (Finset.mem_coe.mpr η₁.prop) (Finset.mem_coe.mpr η₂.prop)
      (Subtype.coe_ne_coe.2 hη))

include hy in
lemma div_zeta_sub_one_Injective :
    Function.Injective (fun η ↦ Ideal.Quotient.mk 𝔭 (divZetaSubOne hp hζ e η)) := by
  letI : AddGroup (𝓞 K ⧸ 𝔭) := inferInstance
  intros η₁ η₂
  contrapose
  intro e₁ e₂
  apply hy
  obtain ⟨u, e⟩ := div_zeta_sub_one_sub hp hζ e η₁ η₂ e₁
  dsimp only at e₂
  rwa [← sub_eq_zero, ← map_sub, ← e, Ideal.Quotient.eq_zero_iff_dvd,
    u.isUnit.dvd_mul_right] at e₂

scoped instance : Finite (𝓞 K ⧸ 𝔭) := by
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  rw [← Ideal.absNorm_ne_zero_iff, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
  exact hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt

include hy in
lemma div_zeta_sub_one_Bijective :
    Function.Bijective (fun η ↦ Ideal.Quotient.mk 𝔭 (divZetaSubOne hp hζ e η)) := by
  letI := Fintype.ofFinite (𝓞 K ⧸ 𝔭)
  letI := IsCyclotomicExtension.numberField {p} ℚ K
  rw [Fintype.bijective_iff_injective_and_card]
  use div_zeta_sub_one_Injective hp hζ e hy
  simp only [Fintype.card_coe]
  rw [hζ.toInteger_isPrimitiveRoot.card_nthRootsFinset, ← Nat.card_eq_fintype_card,
    ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
  simp [show Algebra.norm ℤ π = _ from hζ.norm_toInteger_sub_one_of_prime_ne_two' hp]

include hy in
lemma gcd_zeta_sub_one_eq_one : gcd 𝔪 𝔭 = 1 := by
  rw [gcd_assoc]
  convert gcd_one_right 𝔵 using 2
  rwa [gcd_comm, Irreducible.gcd_eq_one_iff, Ideal.dvd_span_singleton, Ideal.mem_span_singleton]
  · rw [irreducible_iff_prime]
    exact Ideal.prime_span_singleton_iff.mpr hζ.zeta_sub_one_prime'

include hy in
lemma gcd_div_div_zeta_sub_one (η) : 𝔪 ∣ Ideal.span {divZetaSubOne hp hζ e η} := by
  rw [← mul_one (Ideal.span {divZetaSubOne hp hζ e η}),
    ← gcd_zeta_sub_one_eq_one hζ hy (x := x) (y := y)]
  apply dvd_mul_gcd_of_dvd_mul
  rw [Ideal.span_singleton_mul_span_singleton, div_zeta_sub_one_mul_zeta_sub_one,
  Ideal.dvd_span_singleton, Ideal.gcd_eq_sup]
  refine add_mem
    (Ideal.mem_sup_left (Ideal.subset_span (s := {x}) rfl))
    (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span (s := {y}) rfl)))

noncomputable
def divZetaSubOneDvdGcd : Ideal (𝓞 K) :=
  (gcd_div_div_zeta_sub_one hp hζ e hy η).choose

local notation "𝔠" => fun η ↦ divZetaSubOneDvdGcd hp hζ e hy η

lemma div_zeta_sub_one_dvd_gcd_spec :
    𝔪 * 𝔠 η = (Ideal.span <| singleton <| divZetaSubOne hp hζ e η) :=
(gcd_div_div_zeta_sub_one hp hζ e hy η).choose_spec.symm

lemma m_mul_c_mul_p : 𝔪 * 𝔠 η * 𝔭 = 𝔦 η := by
  rw [div_zeta_sub_one_dvd_gcd_spec, Ideal.span_singleton_mul_span_singleton,
    div_zeta_sub_one_mul_zeta_sub_one]

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] in
lemma p_ne_zero : 𝔭 ≠ 0 := by
  rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  exact hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt

lemma coprime_c (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K)) (hη : η₁ ≠ η₂) :
    IsCoprime (𝔠 η₁) (𝔠 η₂) := by
  rw [Ideal.isCoprime_iff_codisjoint, codisjoint_iff_le_sup, ← Ideal.dvd_iff_le]
  rw [← mul_dvd_mul_iff_left (m_ne_zero hζ hy), ← mul_dvd_mul_iff_right (p_ne_zero hζ)]
  rw [Ideal.mul_sup, Ideal.sup_mul, m_mul_c_mul_p, m_mul_c_mul_p, Ideal.mul_top]
  exact hζ.toInteger_isPrimitiveRoot.span_add_mul_sup_dvd_gcd_mul_sub_one hpri.out
    η₁.prop η₂.prop (Subtype.coe_injective.ne hη)

include hy in
lemma gcd_m_p_pow_eq_one : gcd 𝔪 (𝔭 ^ (m + 1)) = 1 := by
  rw [← Ideal.isCoprime_iff_gcd, IsCoprime.pow_right_iff, Ideal.isCoprime_iff_gcd,
    gcd_zeta_sub_one_eq_one hζ hy]
  simp only [add_pos_iff, or_true, one_pos]

include hζ m hy e in
lemma m_dvd_z : 𝔪 ∣ 𝔷 := by
  rw [← one_mul 𝔷, ← gcd_m_p_pow_eq_one hζ hy (x := x) (m := m)]
  apply dvd_gcd_mul_of_dvd_mul
  rw [← UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hpri.out.ne_zero,
    ← span_pow_add_pow_eq hζ e, Ideal.dvd_span_singleton]
  exact add_mem (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self x)) p)
    (Ideal.pow_mem_pow (Ideal.mem_sup_right (Ideal.mem_span_singleton_self y)) p)

noncomputable
def zDivM : Ideal (𝓞 K) :=
  (m_dvd_z hζ e hy).choose

local notation "𝔷'" => zDivM hζ e hy

lemma z_div_m_spec : 𝔷 = 𝔪 * 𝔷' :=
  (m_dvd_z hζ e hy).choose_spec

lemma exists_ideal_pow_eq_c_aux :
    𝔪 ^ p * (𝔷' * 𝔭 ^ m) ^ p * 𝔭 ^ p = (𝔭 ^ (m + 1) * 𝔷) ^ p := by
  rw [mul_comm _ 𝔷, mul_pow, z_div_m_spec hζ e hy, mul_pow, mul_pow, ← pow_mul, ← pow_mul,
    add_mul, one_mul, pow_add, mul_assoc, mul_assoc, mul_assoc]

lemma prod_c :
    ∏ η ∈ Finset.attach (nthRootsFinset p (1 : 𝓞 K)), 𝔠 η = (𝔷' * 𝔭 ^ m) ^ p := by
  have e' := span_pow_add_pow_eq hζ e
  rw [hζ.toInteger_isPrimitiveRoot.pow_add_pow_eq_prod_add_mul _ _ <| Nat.odd_iff.2 <|
    hpri.out.eq_two_or_odd.resolve_left hp] at e'
  rw [← Ideal.prod_span_singleton, ← Finset.prod_attach] at e'
  simp_rw [mul_comm _ y, ← m_mul_c_mul_p hp hζ e hy,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_attach,
    hζ.toInteger_isPrimitiveRoot.card_nthRootsFinset] at e'
  rw [← mul_right_inj'
    ((pow_ne_zero_iff hpri.out.ne_zero).mpr (m_ne_zero hζ hy) : _),
    ← mul_left_inj' ((pow_ne_zero_iff hpri.out.ne_zero).mpr (p_ne_zero hζ) : _), e',
    exists_ideal_pow_eq_c_aux]

lemma exists_ideal_pow_eq_c : ∃ I : Ideal (𝓞 K), (𝔠 η) = I ^ p :=
  Finset.exists_eq_pow_of_mul_eq_pow_of_coprime
    (fun η₁ _ η₂ _ hη ↦ coprime_c hp hζ e hy η₁ η₂ hη)
    (prod_c hp hζ e hy) η (Finset.mem_attach _ _)

noncomputable
def rootDivZetaSubOneDvdGcd : Ideal (𝓞 K) :=
  (exists_ideal_pow_eq_c hp hζ e hy η).choose

local notation "𝔞" => rootDivZetaSubOneDvdGcd hp hζ e hy

lemma root_div_zeta_sub_one_dvd_gcd_spec : (𝔞 η) ^ p = 𝔠 η :=
(exists_ideal_pow_eq_c hp hζ e hy η).choose_spec.symm

lemma c_div_principal_aux (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K)) :
    ((𝔦 η₁) / (𝔦 η₂) : FractionalIdeal (𝓞 K)⁰ K) = 𝔠 η₁ / 𝔠 η₂ := by
  simp_rw [← m_mul_c_mul_p hp hζ e hy, FractionalIdeal.coeIdeal_mul]
  rw [mul_div_mul_right, mul_div_mul_left]
  · rw [← FractionalIdeal.coeIdeal_bot, (FractionalIdeal.coeIdeal_injective' le_rfl).ne_iff]
    exact m_ne_zero hζ hy
  · rw [← FractionalIdeal.coeIdeal_bot, (FractionalIdeal.coeIdeal_injective' le_rfl).ne_iff]
    exact p_ne_zero hζ

lemma c_div_principal (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K)) :
    Submodule.IsPrincipal
      ((𝔠 η₁ / 𝔠 η₂ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  rw [← c_div_principal_aux, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_div_spanSingleton,
    FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨_, rfl⟩⟩

noncomputable
def zetaSubOneDvdRoot : nthRootsFinset p (1 : 𝓞 K) :=
  (Equiv.ofBijective _ (div_zeta_sub_one_Bijective hp hζ e hy)).symm 0

local notation "η₀" => zetaSubOneDvdRoot hp hζ e hy

lemma zeta_sub_one_dvd_root_spec : Ideal.Quotient.mk 𝔭 (divZetaSubOne hp hζ e η₀) = 0 :=
Equiv.ofBijective_apply_symm_apply _ (div_zeta_sub_one_Bijective hp hζ e hy) 0

lemma p_dvd_c_iff : 𝔭 ∣ (𝔠 η) ↔ η = η₀ := by
  rw [← (div_zeta_sub_one_Injective hp hζ e hy).eq_iff, zeta_sub_one_dvd_root_spec,
    Ideal.Quotient.eq_zero_iff_dvd, ← Ideal.mem_span_singleton (α := 𝓞 K),
    ← Ideal.dvd_span_singleton, ← div_zeta_sub_one_dvd_gcd_spec (hy := hy),
    ← dvd_gcd_mul_iff_dvd_mul, gcd_comm, gcd_zeta_sub_one_eq_one hζ hy, one_mul]

lemma p_pow_dvd_c_eta_zero_aux [DecidableEq (𝓞 K)] :
    gcd (𝔭 ^ (m * p))
      (∏ η ∈ Finset.attach (nthRootsFinset p (1 : 𝓞 K)) \ {η₀}, 𝔠 η) = 1 := by
  rw [← Ideal.isCoprime_iff_gcd]
  apply IsCoprime.pow_left
  rw [Ideal.isCoprime_iff_gcd,
    (Ideal.prime_span_singleton_iff.mpr hζ.zeta_sub_one_prime').irreducible.gcd_eq_one_iff,
    (Ideal.prime_span_singleton_iff.mpr hζ.zeta_sub_one_prime').dvd_finsetProd_iff]
  rintro ⟨η, hη, h⟩
  rw [p_dvd_c_iff] at h
  simp only [Finset.mem_sdiff, Finset.mem_singleton] at hη
  exact hη.2 h

lemma p_dvd_a_iff : 𝔭 ∣ 𝔞 η ↔ η = η₀ := by
  rw [← p_dvd_c_iff hp hζ e hy, ← root_div_zeta_sub_one_dvd_gcd_spec,
    (Ideal.prime_span_singleton_iff.mpr hζ.zeta_sub_one_prime').dvd_pow_iff_dvd hpri.out.ne_zero]

lemma p_pow_dvd_c_eta_zero : 𝔭 ^ (m * p) ∣ 𝔠 η₀ := by
  classical
  rw [← one_mul (𝔠 η₀), ← p_pow_dvd_c_eta_zero_aux hp hζ e hy, dvd_gcd_mul_iff_dvd_mul,
    mul_comm _ (𝔠 η₀)]
  rw [← Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_attach _ η₀) 𝔠,
    prod_c, mul_pow]
  apply dvd_mul_of_dvd_right
  rw [pow_mul]

lemma p_pow_dvd_a_eta_zero : 𝔭 ^ m ∣ 𝔞 η₀ := by
  rw [← UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hpri.out.ne_zero,
    root_div_zeta_sub_one_dvd_gcd_spec, ← pow_mul]
  exact p_pow_dvd_c_eta_zero hp hζ e hy

noncomputable
def aEtaZeroDvdPPow : Ideal (𝓞 K) :=
  (p_pow_dvd_a_eta_zero hp hζ e hy).choose

local notation "𝔞₀" => aEtaZeroDvdPPow hp hζ e hy

lemma a_eta_zero_dvd_p_pow_spec : 𝔭 ^ m * 𝔞₀ = 𝔞 η₀ :=
  (p_pow_dvd_a_eta_zero hp hζ e hy).choose_spec.symm

include hz in
lemma not_p_div_a_zero : ¬ 𝔭 ∣ 𝔞₀ := by
  intro h
  have := pow_dvd_pow_of_dvd (mul_dvd_mul (dvd_refl (𝔭 ^ m)) h) p
  rw [a_eta_zero_dvd_p_pow_spec, root_div_zeta_sub_one_dvd_gcd_spec] at this
  have := this.trans (Finset.dvd_prod_of_mem 𝔠 (Finset.mem_attach _ η₀))
  rw [prod_c, mul_pow, mul_pow, mul_comm, mul_dvd_mul_iff_right,
    UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd hpri.out.ne_zero] at this
  · apply hz
    rw [← Ideal.mem_span_singleton, ← Ideal.dvd_span_singleton, z_div_m_spec hζ e hy]
    exact this.trans (dvd_mul_left _ _)
  · apply mt eq_zero_of_pow_eq_zero
    apply mt eq_zero_of_pow_eq_zero
    rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt

include hp hζ e hy hz in
lemma one_le_m : 1 ≤ m := by
  have ha := not_p_div_a_zero hp hζ e hy hz
  have hprime := Ideal.prime_span_singleton_iff.mpr hζ.zeta_sub_one_prime'
  rw [← hprime.irreducible.gcd_eq_one_iff] at ha
  have := (p_dvd_a_iff hp hζ e hy η₀).mpr rfl
  rw [← a_eta_zero_dvd_p_pow_spec, mul_comm, ← dvd_gcd_mul_iff_dvd_mul, ha, one_mul] at this
  nth_rw 1 [← pow_one 𝔭] at this
  rwa [← pow_dvd_pow_iff (p_ne_zero hζ)
    (Ideal.prime_span_singleton_iff.mpr hζ.zeta_sub_one_prime').not_unit]

include hp in
lemma exists_solution'_aux {ε₁ ε₂ : (𝓞 K)ˣ} (hx : ¬ π ∣ x)
    (h : (p : 𝓞 K) ∣ ε₁ * x ^ p + ε₂ * y ^ p) :
    ∃ a : 𝓞 K, ↑p ∣ ↑(ε₁ / ε₂) - a ^ p := by
  obtain ⟨a, b, e⟩ : IsCoprime ↑p x :=
    IsCyclotomicExtension.Rat.isCoprime_of_not_zeta_sub_one_dvd _ hζ hx
  have : (p : 𝓞 K) ∣ b * x - 1 := by
    use -a
    rw [← e]
    ring
  have := (this.trans (sub_one_dvd_pow_sub_one _ p)).trans (dvd_mul_left _ ↑(ε₁ / ε₂))
  use - y * b
  replace h := (h.trans (dvd_mul_right _ (b ^ p))).trans (dvd_mul_left _ ↑(ε₂⁻¹))
  rw [add_mul, mul_assoc, mul_assoc, ← mul_pow, ← mul_pow, mul_add] at h
  simp_rw [← mul_assoc, ← Units.val_mul] at h
  rw [← mul_comm ε₁, ← div_eq_mul_inv, inv_mul_cancel, Units.val_one, one_mul] at h
  convert dvd_sub h this using 1
  rw [neg_mul, (Nat.Prime.odd_of_ne_two hpri.out hp).neg_pow, sub_neg_eq_add, mul_sub, mul_one,
    mul_comm x b, add_sub_sub_cancel, add_comm]

variable [Fintype (ClassGroup (𝓞 K))] (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K))

include hreg in
lemma a_div_principal (η₁ η₂ : nthRootsFinset p (1 : 𝓞 K)) :
    Submodule.IsPrincipal
      ((𝔞 η₁ / 𝔞 η₂ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  apply isPrincipal_of_isPrincipal_pow_of_Coprime' _ hreg
  rw [div_pow, ← FractionalIdeal.coeIdeal_pow, ← FractionalIdeal.coeIdeal_pow,
    root_div_zeta_sub_one_dvd_gcd_spec, root_div_zeta_sub_one_dvd_gcd_spec]
  exact c_div_principal hp hζ e hy η₁ η₂

include hreg in
lemma isPrincipal_a_div_a_zero :
    Submodule.IsPrincipal
      ((𝔞 η / 𝔞₀ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) := by
  have := a_div_principal hp hζ e hy hreg η η₀
  rw [← a_eta_zero_dvd_p_pow_spec, mul_comm, FractionalIdeal.coeIdeal_mul, ← div_div,
    FractionalIdeal.isPrincipal_iff] at this
  obtain ⟨a, ha⟩ := this
  rw [div_eq_iff, Ideal.span_singleton_pow, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_mul_spanSingleton] at ha
  · rw [FractionalIdeal.isPrincipal_iff]
    exact ⟨_, ha⟩
  · rw [← FractionalIdeal.coeIdeal_bot,
      (FractionalIdeal.coeIdeal_injective' (le_rfl : (𝓞 K)⁰ ≤ (𝓞 K)⁰)).ne_iff]
    apply mt eq_zero_of_pow_eq_zero
    rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt

include hz hreg in
lemma exists_not_dvd_spanSingleton_eq_a_div_a_zero (hη : η ≠ η₀) :
    ∃ a b : 𝓞 K, ¬ π ∣ a ∧ ¬ π ∣ b ∧
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (a / b : K) = 𝔞 η / 𝔞₀ :=
  FractionalIdeal.exists_not_dvd_spanSingleton_eq hζ.zeta_sub_one_prime'
    _ _ ((p_dvd_a_iff hp hζ e hy η).not.mpr hη) (not_p_div_a_zero hp hζ e hy hz)
      (isPrincipal_a_div_a_zero hp hζ e hy η hreg)

noncomputable
def aDivAZeroNum (hη : η ≠ η₀) : 𝓞 K :=
  (exists_not_dvd_spanSingleton_eq_a_div_a_zero hp hζ e hy hz η hreg hη).choose

noncomputable
def aDivAZeroDenom (hη : η ≠ η₀) : 𝓞 K :=
  (exists_not_dvd_spanSingleton_eq_a_div_a_zero hp hζ e hy hz η hreg hη).choose_spec.choose

local notation "α" => fun η ↦ aDivAZeroNum hp hζ e hy hz η hreg
local notation "β" => fun η ↦ aDivAZeroDenom hp hζ e hy hz η hreg

include hreg in
lemma a_div_a_zero_num_spec (hη : η ≠ η₀) : ¬ π ∣ α η hη := by
  let h := exists_not_dvd_spanSingleton_eq_a_div_a_zero hp hζ e hy hz η hreg hη
  exact h.choose_spec.choose_spec.1

include hreg in
lemma a_div_a_zero_denom_spec (hη : η ≠ η₀) : ¬ π ∣ β η hη := by
  let h := exists_not_dvd_spanSingleton_eq_a_div_a_zero hp hζ e hy hz η hreg hη
  exact h.choose_spec.choose_spec.2.1

lemma a_div_a_zero_eq (hη : η ≠ η₀) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (α η hη / β η hη : K) = 𝔞 η / 𝔞₀ := by
  let h := exists_not_dvd_spanSingleton_eq_a_div_a_zero hp hζ e hy hz η hreg hη
  exact h.choose_spec.choose_spec.2.2

lemma a_mul_denom_eq_a_zero_mul_num (hη : η ≠ η₀) :
    𝔞 η * Ideal.span {β η hη} = 𝔞₀ * Ideal.span {α η hη} := by
  apply FractionalIdeal.coeIdeal_injective (K := K)
  simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton]
  rw [mul_comm (𝔞₀ : FractionalIdeal (𝓞 K)⁰ K), ← div_eq_div_iff,
    ← a_div_a_zero_eq hp hζ e hy hz η hreg hη, FractionalIdeal.spanSingleton_div_spanSingleton]
  · intro ha
    rw [FractionalIdeal.coeIdeal_eq_zero] at ha
    apply not_p_div_a_zero hp hζ e hy hz
    rw [ha]
    exact dvd_zero _
  · rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff, ← (algebraMap (𝓞 K) K).map_zero,
      (IsFractionRing.injective (𝓞 K) K).eq_iff]
    intro hβ
    apply a_div_a_zero_denom_spec hp hζ e hy hz η hreg hη
    simp only
    rw [hβ]
    exact dvd_zero _

lemma associated_eta_zero (hη : η ≠ η₀) :
    Associated ((x + y * η₀) * α η hη ^ p)
      ((x + y * η) * π ^ (m * p) * β η hη ^ p) := by
  simp_rw [← Ideal.span_singleton_eq_span_singleton,
    ← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow,
    ← m_mul_c_mul_p hp hζ e hy, ← root_div_zeta_sub_one_dvd_gcd_spec,
    ← a_eta_zero_dvd_p_pow_spec]
  rw [mul_comm _ 𝔞₀, mul_pow]
  simp only [mul_assoc, mul_left_comm _ 𝔭]
  rw [mul_left_comm (𝔞 η ^ p), mul_left_comm (𝔞₀ ^ p), ← pow_mul, ← mul_pow,
    ← mul_pow, a_mul_denom_eq_a_zero_mul_num]

noncomputable
def associatedEtaZeroUnit (hη : η ≠ η₀) : (𝓞 K)ˣ :=
  (associated_eta_zero hp hζ e hy hz η hreg hη).choose

local notation "ε" => fun η ↦ associatedEtaZeroUnit hp hζ e hy hz η hreg

lemma associated_eta_zero_unit_spec (η) (hη : η ≠ η₀) :
    ε η hη * (x + y * η₀) * α η hη ^ p = (x + y * η) * π ^ (m * p) * β η hη ^ p := by
  rw [mul_assoc, mul_comm (ε η hη : 𝓞 K)]
  exact (associated_eta_zero hp hζ e hy hz η hreg hη).choose_spec

lemma formula (η₁) (hη₁ : η₁ ≠ η₀) (η₂) (hη₂ : η₂ ≠ η₀) :
    (η₂ - η₀ : 𝓞 K) * ε η₁ hη₁ * (α η₁ hη₁ * β η₂ hη₂) ^ p +
      (η₀ - η₁) * ε η₂ hη₂ * (α η₂ hη₂ * β η₁ hη₁) ^ p =
      (η₂ - η₁) * (π ^ m * (β η₁ hη₁ * β η₂ hη₂)) ^ p := by
  rw [← mul_right_inj' (x_plus_y_mul_ne_zero hp hζ e hz η₀), mul_add]
  simp_rw [mul_left_comm (x + y * η₀), mul_pow, mul_assoc,
    mul_left_comm (η₂ - η₀ : 𝓞 K), mul_left_comm (η₀ - η₁ : 𝓞 K), ← mul_assoc,
    associated_eta_zero_unit_spec, mul_assoc, ← mul_left_comm (η₂ - η₀ : 𝓞 K),
    ← mul_left_comm (η₀ - η₁ : 𝓞 K), pow_mul, ← mul_pow, mul_comm (β η₂ hη₂),
    ← mul_assoc]
  rw [← add_mul]
  congr 1
  ring

include hreg e hy hz hp in
lemma exists_solution :
    ∃ (x' y' z' : 𝓞 K) (ε₁ ε₂ ε₃ : (𝓞 K)ˣ), ¬ π ∣ x' ∧ ¬ π ∣ y' ∧
      ¬ π ∣ z' ∧ ε₁ * x' ^ p + ε₂ * y' ^ p = ε₃ * (π ^ m * z') ^ p := by
  have h₁ :=
    mul_mem_nthRootsFinset (η₀ : _).prop
      (hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset hpri.out.pos)
  rw [one_mul] at h₁
  let η₁ : nthRootsFinset p (1 : 𝓞 K) := ⟨η₀ * hζ.toInteger, h₁⟩
  have h₂ :=
    mul_mem_nthRootsFinset (η₁ : _).prop
      (hζ.toInteger_isPrimitiveRoot.mem_nthRootsFinset hpri.out.pos)
  rw [one_mul] at h₂
  let η₂ : nthRootsFinset p (1 : 𝓞 K) := ⟨η₀ * hζ.toInteger * hζ.toInteger, h₂⟩
  have hη₁ : η₁ ≠ η₀ := by
    rw [← Subtype.coe_injective.ne_iff]
    change (η₀ * hζ.toInteger : 𝓞 K) ≠ η₀
    rw [Ne, mul_right_eq_self₀, not_or]
    exact ⟨hζ.toInteger_isPrimitiveRoot.ne_one hpri.out.one_lt,
      ne_zero_of_mem_nthRootsFinset one_ne_zero (η₀ : _).prop⟩
  have hη₂ : η₂ ≠ η₀ := by
    rw [← Subtype.coe_injective.ne_iff]
    change (η₀ * hζ.toInteger * hζ.toInteger : 𝓞 K) ≠ η₀
    rw [Ne, mul_assoc, ← pow_two, mul_right_eq_self₀, not_or]
    exact ⟨hζ.toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by omega)
      (hpri.out.two_le.lt_or_eq.resolve_right hp.symm),
      ne_zero_of_mem_nthRootsFinset one_ne_zero (η₀ : _).prop⟩
  have hη : η₂ ≠ η₁ := by
    rw [← Subtype.coe_injective.ne_iff]
    change (η₀ * hζ.toInteger * hζ.toInteger : 𝓞 K) ≠ η₀ * hζ.toInteger
    rw [Ne, mul_right_eq_self₀, not_or]
    exact ⟨hζ.toInteger_isPrimitiveRoot.ne_one hpri.out.one_lt,
      mul_ne_zero (ne_zero_of_mem_nthRootsFinset one_ne_zero (η₀ : _).prop)
        (hζ.toInteger_isPrimitiveRoot.ne_zero hpri.out.ne_zero)⟩
  obtain ⟨u₁, hu₁⟩ :=
    hζ.toInteger_isPrimitiveRoot.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime
      hpri.out (Finset.mem_coe.mpr η₂.prop) (Finset.mem_coe.mpr (η₀ : _).prop)
      (Subtype.coe_injective.ne_iff.mpr hη₂)
  obtain ⟨u₂, hu₂⟩ :=
    hζ.toInteger_isPrimitiveRoot.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime
      hpri.out (Finset.mem_coe.mpr (η₀ : _).prop) (Finset.mem_coe.mpr η₁.prop)
      (Subtype.coe_injective.ne_iff.mpr hη₁.symm)
  obtain ⟨u₃, hu₃⟩ :=
    hζ.toInteger_isPrimitiveRoot.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime
      hpri.out (Finset.mem_coe.mpr η₂.prop) (Finset.mem_coe.mpr η₁.prop)
      (Subtype.coe_injective.ne_iff.mpr hη)
  have := formula hp hζ e hy hz hreg η₁ hη₁ η₂ hη₂
  rw [← hu₁, ← hu₂, ← hu₃, mul_assoc _ (u₁ : 𝓞 K), mul_assoc _ (u₂ : 𝓞 K),
    mul_assoc _ (u₃ : 𝓞 K), mul_assoc (π), mul_assoc (π), ← mul_add,
    mul_right_inj' (hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero hpri.out.one_lt), ← Units.val_mul,
    ← Units.val_mul] at this
  refine ⟨_, _, _, _, _, _, ?_, ?_, ?_, this⟩
  · exact hζ.zeta_sub_one_prime'.not_dvd_mul
      (a_div_a_zero_num_spec hp hζ e hy hz η₁ hreg hη₁)
      (a_div_a_zero_denom_spec hp hζ e hy hz η₂ hreg hη₂)
  · exact hζ.zeta_sub_one_prime'.not_dvd_mul
      (a_div_a_zero_num_spec hp hζ e hy hz η₂ hreg hη₂)
      (a_div_a_zero_denom_spec hp hζ e hy hz η₁ hreg hη₁)
  · exact hζ.zeta_sub_one_prime'.not_dvd_mul
      (a_div_a_zero_denom_spec hp hζ e hy hz η₁ hreg hη₁)
      (a_div_a_zero_denom_spec hp hζ e hy hz η₂ hreg hη₂)

include hp hreg e hy hz in
lemma exists_solution' :
    ∃ (x' y' z' : 𝓞 K) (ε₃ : (𝓞 K)ˣ),
      ¬ π ∣ y' ∧ ¬ π ∣ z' ∧ x' ^ p + y' ^ p = ε₃ * (π ^ m * z') ^ p := by
  obtain ⟨x', y', z', ε₁, ε₂, ε₃, hx', hy', hz', e'⟩ :=
    exists_solution hp hζ e hy hz hreg
  obtain ⟨ε', hε'⟩ : ∃ ε', ε₁ / ε₂ = ε' ^ p := by
    apply eq_pow_prime_of_unit_of_congruent hp hreg
    have : p - 1 ≤ m * p := (Nat.sub_le _ _).trans
      ((le_of_eq (one_mul _).symm).trans (Nat.mul_le_mul_right p (one_le_m hp hζ e hy hz)))
    obtain ⟨u, hu⟩ := (IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime _ hζ).symm
    rw [mul_pow, ← pow_mul, mul_comm (ε₃ : 𝓞 K), mul_assoc, ← Nat.sub_add_cancel this,
      add_comm _ (p - 1), pow_add, mul_assoc] at e'
    apply_fun Ideal.Quotient.mk (Ideal.span <| singleton (p : 𝓞 K)) at e'
    rw [map_mul, (Ideal.Quotient.eq_zero_iff_dvd _ _).mpr
      (IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime _ hζ).symm.dvd, zero_mul,
      Ideal.Quotient.eq_zero_iff_dvd] at e'
    obtain ⟨a, ha⟩ := exists_solution'_aux hp hζ hx' e'
    obtain ⟨b, hb⟩ := exists_dvd_pow_sub_Int_pow hp a
    have := dvd_add ha hb
    rw [sub_add_sub_cancel, ← Int.cast_pow] at this
    exact ⟨b ^ p, this⟩
  refine ⟨ε' * x', y', z', ε₃ / ε₂, hy', hz', ?_⟩
  rwa [mul_pow, ← Units.val_pow_eq_pow_val, ← hε', ← mul_right_inj' ε₂.isUnit.ne_zero,
    mul_add, ← mul_assoc, ← Units.val_mul, mul_div_cancel,
    ← mul_assoc, ← Units.val_mul, mul_div_cancel]

end CaseII
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular FltRegularPort.Internal.FltRegular.KummersLemma FltRegularPort.Internal.FltRegular.CaseII

end FltRegular
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular FltRegularPort.Internal.FltRegular.KummersLemma FltRegularPort.Internal.FltRegular.CaseII

end Port_FLT_Deep_Regular_InductionStep_lean
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular FltRegularPort.Internal.FltRegular.KummersLemma FltRegularPort.Internal.FltRegular.CaseII

section Port_FLT_Deep_Regular_CaseIIChain_lean

open scoped nonZeroDivisors NumberField

open Polynomial

namespace FltRegular

section InductionStepInterface

variable {K : Type} {p : ℕ} [hpri : Fact p.Prime] [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] (hp : p ≠ 2)
variable {ζ : K} (hζ : IsPrimitiveRoot ζ p) {x y z : 𝓞 K} {ε : (𝓞 K)ˣ} {m : ℕ}

variable [Fintype (ClassGroup (𝓞 K))] (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K))

include hp hreg in

lemma not_exists_solution {m : ℕ} (hm : 1 ≤ m) :
    ¬∃ (x' y' z' : 𝓞 K) (ε₃ : (𝓞 K)ˣ),
      ¬((hζ.toInteger : 𝓞 K) - 1 ∣ y') ∧ ¬((hζ.toInteger : 𝓞 K) - 1 ∣ z') ∧
      x' ^ p + y' ^ p = ε₃ * (((hζ.toInteger : 𝓞 K) - 1) ^ m * z') ^ p := by
  induction m, hm using Nat.le_induction with
  | base =>
      rintro ⟨x, y, z, ε₃, hy, hz, e⟩
      exact zero_lt_one.not_ge (CaseII.one_le_m hp hζ e hy hz)
  | succ m' _ IH =>
      rintro ⟨x, y, z, ε₃, hy, hz, e⟩
      exact IH (CaseII.exists_solution' hp hζ e hy hz hreg)

include hp hreg in

lemma not_exists_solution' :
    ¬∃ x y z : 𝓞 K, ¬((hζ.toInteger : 𝓞 K) - 1 ∣ y) ∧
      ((hζ.toInteger : 𝓞 K) - 1 ∣ z) ∧ z ≠ 0 ∧ x ^ p + y ^ p = z ^ p := by
  letI : Fact (Nat.Prime p) := hpri
  letI : WfDvdMonoid (𝓞 K) := IsNoetherianRing.wfDvdMonoid
  rintro ⟨x, y, z, hy, hz, hz', e⟩
  obtain ⟨m, z, hm, hz'', rfl⟩ :
      ∃ m z', 1 ≤ m ∧ ¬((hζ.toInteger : 𝓞 K) - 1 ∣ z') ∧
        z = ((hζ.toInteger : 𝓞 K) - 1) ^ m * z' := by
    classical
    have H : FiniteMultiplicity ((hζ.toInteger : 𝓞 K) - 1) z := FiniteMultiplicity.of_not_isUnit
      hζ.zeta_sub_one_prime'.not_unit hz'
    obtain ⟨z', h⟩ := pow_multiplicity_dvd ((hζ.toInteger : 𝓞 K) - 1) z
    refine ⟨_, _, ?_, ?_, h⟩
    · rwa [← Nat.cast_le (α := ENat), ← FiniteMultiplicity.emultiplicity_eq_multiplicity H,
        ← pow_dvd_iff_le_emultiplicity, pow_one]
    · intro h'
      have := mul_dvd_mul_left
        (((hζ.toInteger : 𝓞 K) - 1) ^ (multiplicity ((hζ.toInteger : 𝓞 K) - 1) z)) h'
      rw [← pow_succ, ← h] at this
      refine not_pow_dvd_of_emultiplicity_lt ?_ this
      rw [FiniteMultiplicity.emultiplicity_eq_multiplicity H, Nat.cast_lt]
      exact Nat.lt_succ_self _
  refine not_exists_solution hp hζ hreg hm ⟨x, y, z, 1, hy, hz'', ?_⟩
  rwa [Units.val_one, one_mul]

end InductionStepInterface
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular FltRegularPort.Internal.FltRegular.KummersLemma FltRegularPort.Internal.FltRegular.CaseII

set_option backward.isDefEq.respectTransparency false in

lemma not_exists_Int_solution {p : ℕ} [hpri : Fact (Nat.Prime p)] (hreg : IsRegularPrime p)
    (hodd : p ≠ 2) :
    ¬∃ x y z : ℤ, ¬↑p ∣ y ∧ ↑p ∣ z ∧ z ≠ 0 ∧ x ^ p + y ^ p = z ^ p := by
  haveI := CyclotomicField.isCyclotomicExtension p ℚ
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot
    ℚ (B := (CyclotomicField p ℚ)) (Set.mem_singleton p) hpri.1.ne_zero
  have := fun n : ℤ ↦
    IsCyclotomicExtension.Rat.zeta_sub_one_dvd_intCast_iff' (K := CyclotomicField p ℚ) (n := n) p hζ
  simp_rw [← this]
  rintro ⟨x, y, z, hy, hz, hz', e⟩
  refine not_exists_solution' (K := CyclotomicField p ℚ) hodd hζ ?_
    ⟨x, y, z, hy, hz, ?_, ?_⟩
  · simpa [IsRegularPrime, IsRegularNumber] using hreg
  · rwa [ne_eq, Int.cast_eq_zero]
  · simp_rw [← Int.cast_pow, ← Int.cast_add, e]

lemma not_exists_Int_solution' {p : ℕ} [hpri : Fact (Nat.Prime p)] (hreg : IsRegularPrime p)
    (hodd : p ≠ 2) :
    ¬∃ x y z : ℤ, ({x, y, z} : Finset ℤ).gcd id = 1 ∧ ↑p ∣ z ∧ z ≠ 0 ∧
      x ^ p + y ^ p = z ^ p := by
  rintro ⟨x, y, z, hgcd, hz, hz', e⟩
  refine not_exists_Int_solution hreg hodd ⟨x, y, z, ?_, hz, hz', e⟩
  intro hy
  have := dvd_sub (dvd_pow hz hpri.out.ne_zero) (dvd_pow hy hpri.out.ne_zero)
  rw [← e, add_sub_cancel_right] at this
  replace this := (Nat.prime_iff_prime_int.mp hpri.out).dvd_of_dvd_pow this
  apply (Nat.prime_iff_prime_int.mp hpri.out).not_unit
  rw [isUnit_iff_dvd_one, ← hgcd]
  simp [dvd_gcd_iff, hz, hy, this]

end FltRegular
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular FltRegularPort.Internal.FltRegular.KummersLemma FltRegularPort.Internal.FltRegular.CaseII

end Port_FLT_Deep_Regular_CaseIIChain_lean
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular FltRegularPort.Internal.FltRegular.KummersLemma FltRegularPort.Internal.FltRegular.CaseII

section Port_FLT_Deep_CaseSplit_lean

open Int Finset

namespace FltRegular

theorem caseI {a b c : ℤ} {p : ℕ} [Fact p.Prime] (hreg : IsRegularPrime p)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) (caseI : ¬↑p ∣ a * b * c) :
    a ^ p + b ^ p ≠ c ^ p :=
  CaseI.may_assume
    (fun _ _ _ _ _ hreg' hp5 hgcd hab hI => caseI_easier hreg' hp5 hgcd hab hI)
    hreg hgcd caseI

theorem caseII {a b c : ℤ} {p : ℕ} [hpri : Fact p.Prime] (hreg : IsRegularPrime p)
    (hodd : p ≠ 2) (hprod : a * b * c ≠ 0)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) (caseII : ↑p ∣ a * b * c) :
    a ^ p + b ^ p ≠ c ^ p := by
  intro e
  simp only [ne_eq, mul_eq_zero, not_or] at hprod
  obtain ⟨⟨a0, b0⟩, c0⟩ := hprod
  have hodd' := Nat.Prime.odd_of_ne_two hpri.out hodd
  obtain hab | hc := (Nat.prime_iff_prime_int.mp hpri.out).dvd_or_dvd caseII
  · obtain ha | hb := (Nat.prime_iff_prime_int.mp hpri.out).dvd_or_dvd hab
    · refine not_exists_Int_solution' hreg hodd ⟨b, -c, -a, ?_, ?_, ?_, ?_⟩
      · simp only [← hgcd, Finset.gcd_insert, id_eq, ← Int.coe_gcd, Int.neg_gcd,
          ← LawfulSingleton.insert_empty_eq, Finset.gcd_empty, Int.gcd_left_comm _ a]
      · rwa [dvd_neg]
      · rwa [ne_eq, neg_eq_zero]
      · simp [hodd'.neg_pow, ← e]
    · refine not_exists_Int_solution' hreg hodd ⟨-c, a, -b, ?_, ?_, ?_, ?_⟩
      · simp only [← hgcd, Finset.gcd_insert, id_eq, ← Int.coe_gcd, Int.neg_gcd,
          ← LawfulSingleton.insert_empty_eq, Finset.gcd_empty, Int.gcd_left_comm _ c]
      · rwa [dvd_neg]
      · rwa [ne_eq, neg_eq_zero]
      · simp [hodd'.neg_pow, ← e]
  · exact not_exists_Int_solution' hreg hodd ⟨a, b, c, hgcd, hc, c0, e⟩

end FltRegular
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular FltRegularPort.Internal.FltRegular.KummersLemma FltRegularPort.Internal.FltRegular.CaseII

open FltRegular in

theorem flt_regular_port {p : ℕ} [Fact p.Prime] (hreg : IsRegularPrime p) (hodd : p ≠ 2) :
    FermatLastTheoremFor p := by
  apply fermatLastTheoremFor_iff_int.mpr
  refine fermatLastTheoremWith_of_fermatLastTheoremWith_coprime fun a b c ha hb hc hgcd => ?_
  by_cases case : ↑p ∣ a * b * c
  · exact caseII hreg hodd (mul_ne_zero (mul_ne_zero ha hb) hc) hgcd case
  · exact caseI hreg hgcd case

end Port_FLT_Deep_CaseSplit_lean
open scoped FltRegularPort.Internal.FltRegular.CyclotomicIntegers FltRegularPort.Internal.FltRegular FltRegularPort.Internal.FltRegular.KummersLemma FltRegularPort.Internal.FltRegular.CaseII

end Internal

end FltRegularPort

namespace MetaMathlibExt

open scoped NumberField in
/-- **Kummer's theorem for regular primes.** Let $p$ be an odd prime and let $K$ be a $p$-th
cyclotomic field over $\mathbb{Q}$ (a number field generated over $\mathbb{Q}$ by a primitive
$p$-th root of unity). If $p$ does not divide the class number of $K$, then Fermat's Last Theorem
holds for the exponent $p$: there are no positive integers $a, b, c$ with $a^p + b^p = c^p$.

Source: Seki, *Regular Primes, Non-Wieferich Primes, and Finite Multiple Zeta Values of
Level N*, INTEGERS 24 (2024), Article A22, Theorem 1 (`integers-2024-A22-thm-1`). -/
public theorem fermatLastTheoremFor_of_regular {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (hreg : ¬ p ∣ NumberField.classNumber K) : FermatLastTheoremFor p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  haveI : NeZero (p : ℚ) := ⟨Nat.cast_ne_zero.mpr hp.pos.ne'⟩
  haveI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  let e : K ≃ₐ[ℚ] CyclotomicField p ℚ :=
    IsCyclotomicExtension.algEquiv {p} ℚ K (CyclotomicField p ℚ)
  have hcard : Fintype.card (ClassGroup (𝓞 K)) =
      Fintype.card (ClassGroup (𝓞 (CyclotomicField p ℚ))) :=
    Fintype.card_congr (ClassGroup.mulEquiv
      (NumberField.RingOfIntegers.mapRingEquiv e.toRingEquiv)).toEquiv
  have hreg' : p.Coprime (Fintype.card (ClassGroup (𝓞 (CyclotomicField p ℚ)))) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp, ← hcard]
    exact hreg
  exact FltRegularPort.Internal.flt_regular_port hreg' hp2

end MetaMathlibExt
