/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import MathlibExt.NumberTheory.PrimitiveDivisor
public import MathlibExt.NumberTheory.RieselRepdigit101
public import MathlibExt.NumberTheory.SierpinskiRepinteger18107
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Set.Finite.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Infinitely many Sierpiński repdigits in every base `b > 78557`

Proves `MetaMathlibExt.infinite_sierpinski_repdigits`: for every base `b > 78557` there are
infinitely many Sierpiński numbers among the `b`-repdigits.

Statements from Bispels et al., *On Sierpiński and Riesel Repdigits and Repintegers*,
INTEGERS 26 (2026), Article A12.
-/

namespace MetaMathlibExt

namespace infinite_sierpinski_repdigits

private def primes : Finset ℕ := {3, 5, 7, 13, 19, 37, 73}

private noncomputable def lp (b p : ℕ) : ℕ :=
  if p ∣ b then 1 else if b ≡ 1 [MOD p] then p else orderOf (b : ZMod p)

private noncomputable def L (b : ℕ) : ℕ := Nat.lcm 2 (primes.lcm (lp b))

private theorem primes_mem_prime : ∀ p ∈ primes, Nat.Prime p := by decide

private theorem primes_mem_two_le : ∀ p ∈ primes, 2 ≤ p := by decide

private theorem primes_mem_ne_zero : ∀ p ∈ primes, p ≠ 0 := by decide

private theorem lp_ne_zero (b : ℕ) (p : ℕ) (hp : p ∈ primes) : lp b p ≠ 0 := by
  unfold lp
  by_cases hpb : p ∣ b
  · simp [hpb]
  · simp only [hpb]
    by_cases hb1 : b ≡ 1 [MOD p]
    · simp [hb1, primes_mem_ne_zero p hp]
    · simp only [hb1]
      have hprime : Nat.Prime p := primes_mem_prime p hp
      have hp0 : (b : ZMod p) ≠ 0 := by
        rwa [ne_eq, ZMod.natCast_eq_zero_iff]
      have hfact : Fact (Nat.Prime p) := ⟨hprime⟩
      have hdvd : orderOf (b : ZMod p) ∣ p - 1 :=
        @ZMod.orderOf_dvd_card_sub_one p hfact _ hp0
      have hp1 : p - 1 ≠ 0 := by
        have h2 := primes_mem_two_le p hp
        omega
      exact ne_zero_of_dvd_ne_zero hp1 hdvd

private theorem L_ne_zero (b : ℕ) : L b ≠ 0 := by
  unfold L
  apply Nat.lcm_ne_zero (by decide)
  rw [Finset.lcm_ne_zero_iff]
  intro p hp
  exact lp_ne_zero b p hp

private theorem two_dvd_L (b : ℕ) : 2 ∣ L b := by
  unfold L
  exact Nat.dvd_lcm_left 2 _

private theorem lp_dvd_L (b : ℕ) (p : ℕ) (hp : p ∈ primes) : lp b p ∣ L b := by
  unfold L
  exact (Finset.dvd_lcm hp).trans (Nat.dvd_lcm_right 2 _)

private def S (b t : ℕ) : ℕ := (b ^ t - 1) / (b - 1)

private theorem repstring_eq_78557 {b t : ℕ} (hb : 78557 < b) :
    repstring b 78557 0 t = 78557 * (b ^ t - 1) / (b - 1) := by
  simp only [repstring, Nat.digits_of_lt b 78557 (by decide) (by omega),
    List.length_singleton, zero_add, one_mul, pow_one]

private theorem repstring_eq_mul_S {b t : ℕ} (hb : 78557 < b) :
    repstring b 78557 0 t = 78557 * S b t := by
  rw [repstring_eq_78557 hb]
  unfold S
  exact Nat.mul_div_assoc 78557 (Nat.sub_one_dvd_pow_sub_one b t)

private theorem geom_eq_sum {b t : ℕ} (hb : 2 ≤ b) : S b t = ∑ i ∈ Finset.range t, b ^ i := by
  unfold S
  exact (Nat.geomSum_eq hb t).symm

private theorem S_mul_sub_one (b t : ℕ) : S b t * (b - 1) = b ^ t - 1 := by
  unfold S
  exact Nat.div_mul_cancel (Nat.sub_one_dvd_pow_sub_one b t)

private theorem S_modEq_one_of_dvd {b t p : ℕ} (hb : 2 ≤ b) (ht : 1 ≤ t)
    (hpb : p ∣ b) : S b t ≡ 1 [MOD p] := by
  have hdiv : S b t * (b - 1) = b ^ t - 1 := S_mul_sub_one b t
  have hb1 : 1 ≤ b := by omega
  have hbt : 1 ≤ b ^ t := Nat.one_le_pow t b (by omega)
  have hcast : ((S b t * (b - 1) : ℕ) : ZMod p) = ((b ^ t - 1 : ℕ) : ZMod p) := by
    rw [hdiv]
  rw [Nat.cast_mul, Nat.cast_sub hb1, Nat.cast_sub hbt] at hcast
  simp only [Nat.cast_pow, Nat.cast_one] at hcast
  have hb0 : (b : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff b p).mpr hpb
  rw [hb0] at hcast
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hpow0 : (0 : ZMod p) ^ t = 0 := zero_pow ht0
  rw [hpow0] at hcast
  have hneg : (0 : ZMod p) - 1 = -1 := by simp
  rw [hneg] at hcast
  have hS1 : ((S b t : ℕ) : ZMod p) = 1 := by
    have hsq : (-1 : ZMod p) * (-1) = 1 := by simp
    calc ((S b t : ℕ) : ZMod p)
        = ((S b t : ℕ) : ZMod p) * 1 := by simp
      _ = ((S b t : ℕ) : ZMod p) * ((-1) * (-1)) := by rw [hsq]
      _ = (((S b t : ℕ) : ZMod p) * (-1)) * (-1) := by rw [mul_assoc]
      _ = (-1) * (-1) := by rw [hcast]
      _ = 1 := hsq
  exact (ZMod.natCast_eq_natCast_iff (S b t) 1 p).mp (by simpa using hS1)

private theorem S_modEq_one_of_modEq_one {b t p : ℕ} (hb : 2 ≤ b)
    (hb1 : b ≡ 1 [MOD p]) (ht1 : t ≡ 1 [MOD p]) : S b t ≡ 1 [MOD p] := by
  have hsum : S b t = ∑ i ∈ Finset.range t, b ^ i := geom_eq_sum hb
  have heach : ∀ i ∈ Finset.range t, b ^ i ≡ 1 [MOD p] := by
    intro i _
    simpa using hb1.pow i
  have hmod : (∑ i ∈ Finset.range t, b ^ i) ≡ ∑ i ∈ Finset.range t, 1 [MOD p] :=
    Nat.ModEq.sum heach
  have hsum1 : (∑ i ∈ Finset.range t, 1) = t := by simp
  rw [hsum]
  calc (∑ i ∈ Finset.range t, b ^ i)
      ≡ ∑ i ∈ Finset.range t, 1 [MOD p] := hmod
    _ = t := hsum1
    _ ≡ 1 [MOD p] := ht1

private theorem S_modEq_one_of_order {b t p : ℕ} (hb : 2 ≤ b) (ht : 1 ≤ t)
    (hp : Nat.Prime p) (hb1 : ¬ b ≡ 1 [MOD p])
    (htord : t ≡ 1 [MOD orderOf (b : ZMod p)]) : S b t ≡ 1 [MOD p] := by
  have hb1le : 1 ≤ b := by omega
  have hbtle : 1 ≤ b ^ t := Nat.one_le_pow t b (by omega)
  have hdvd_tsub : orderOf (b : ZMod p) ∣ t - 1 := by
    have hsymm : 1 ≡ t [MOD orderOf (b : ZMod p)] := htord.symm
    exact (Nat.modEq_iff_dvd' ht).mp hsymm
  have hpow1 : (b : ZMod p) ^ (t - 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp hdvd_tsub
  have hpowt : (b : ZMod p) ^ t = (b : ZMod p) := by
    conv_lhs => rw [← Nat.sub_add_cancel ht]
    rw [pow_add, hpow1, one_mul, pow_one]
  have hmod_pow : b ^ t ≡ b [MOD p] := by
    have heq : ((b ^ t : ℕ) : ZMod p) = (b : ZMod p) := by
      simpa using hpowt
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp heq
  have hmod_sub : b ^ t - 1 ≡ b - 1 [MOD p] :=
    Nat.ModEq.sub hbtle hb1le hmod_pow Nat.ModEq.rfl
  have hdiv : S b t * (b - 1) = b ^ t - 1 := S_mul_sub_one b t
  have hmod_mul : S b t * (b - 1) ≡ b - 1 [MOD p] := by
    calc S b t * (b - 1)
        = b ^ t - 1 := hdiv
      _ ≡ b - 1 [MOD p] := hmod_sub
  have hmod_one : S b t * (b - 1) ≡ 1 * (b - 1) [MOD p] := by
    simpa using hmod_mul
  have hnotdvd : ¬ p ∣ b - 1 := by
    intro hd
    apply hb1
    have hiff : (1 ≡ b [MOD p]) ↔ p ∣ b - 1 := Nat.modEq_iff_dvd' hb1le
    exact (hiff.mpr hd).symm
  have hcop : p.Coprime (b - 1) := (hp.coprime_iff_not_dvd).mpr hnotdvd
  have hgcd : p.gcd (b - 1) = 1 := hcop
  exact Nat.ModEq.cancel_right_of_coprime hgcd hmod_one

private theorem S_modEq_one {b t p : ℕ} (hb : 2 ≤ b) (ht : 1 ≤ t)
    (hpmem : p ∈ primes) (htL : t ≡ 1 [MOD L b]) : S b t ≡ 1 [MOD p] := by
  by_cases hpb : p ∣ b
  · exact S_modEq_one_of_dvd hb ht hpb
  · by_cases hb1 : b ≡ 1 [MOD p]
    · have hlp : lp b p = p := by
        unfold lp
        simp [hpb, hb1]
      have hpL : p ∣ L b := by
        have h := lp_dvd_L b p hpmem
        rwa [hlp] at h
      have ht1 : t ≡ 1 [MOD p] := htL.of_dvd hpL
      exact S_modEq_one_of_modEq_one hb hb1 ht1
    · have hlp : lp b p = orderOf (b : ZMod p) := by
        unfold lp
        simp only [hpb, hb1]
        rfl
      have hordL : orderOf (b : ZMod p) ∣ L b := by
        have h := lp_dvd_L b p hpmem
        rwa [hlp] at h
      have htord : t ≡ 1 [MOD orderOf (b : ZMod p)] := htL.of_dvd hordL
      exact S_modEq_one_of_order hb ht (primes_mem_prime p hpmem) hb1 htord

private theorem repstring_modEq {b t p : ℕ} (hb : 78557 < b) (ht : 1 ≤ t)
    (hpmem : p ∈ primes) (htL : t ≡ 1 [MOD L b]) :
    repstring b 78557 0 t ≡ 78557 [MOD p] := by
  have hb2 : 2 ≤ b := by omega
  have hS : S b t ≡ 1 [MOD p] := S_modEq_one hb2 ht hpmem htL
  have hrep : repstring b 78557 0 t = 78557 * S b t := repstring_eq_mul_S hb
  calc repstring b 78557 0 t
      = 78557 * S b t := hrep
    _ ≡ 78557 * 1 [MOD p] := Nat.ModEq.mul_left 78557 hS
    _ = 78557 := by simp

private theorem hcover : ∀ r : Fin 36, ∃ p ∈ [3, 5, 7, 13, 19, 37, 73],
    2 ≤ p ∧ p ≤ 73 ∧ 2 ^ 36 ≡ 1 [MOD p] ∧
    78557 * 2 ^ (r.val) + 1 ≡ 0 [MOD p] := by decide

private theorem primes_list_mem_iff (p : ℕ) :
    p ∈ [3, 5, 7, 13, 19, 37, 73] ↔ p ∈ primes := by
  simp [primes]

private theorem S_modEq_one_mod_two {b t : ℕ} (hb : 2 ≤ b) (ht : 1 ≤ t)
    (htL : t ≡ 1 [MOD L b]) : S b t ≡ 1 [MOD 2] := by
  by_cases hb2 : 2 ∣ b
  · exact S_modEq_one_of_dvd hb ht hb2
  · have hb1 : b ≡ 1 [MOD 2] := by
      unfold Nat.ModEq
      omega
    have ht1 : t ≡ 1 [MOD 2] := htL.of_dvd (two_dvd_L b)
    exact S_modEq_one_of_modEq_one hb hb1 ht1

private theorem repstring_odd {b t : ℕ} (hb : 78557 < b) (ht : 1 ≤ t)
    (htL : t ≡ 1 [MOD L b]) : Odd (repstring b 78557 0 t) := by
  have hb2 : 2 ≤ b := by omega
  have hS : S b t ≡ 1 [MOD 2] := S_modEq_one_mod_two hb2 ht htL
  have h78557 : (78557 : ℕ) ≡ 1 [MOD 2] := by decide
  have hrep : repstring b 78557 0 t = 78557 * S b t := repstring_eq_mul_S hb
  have hmod : repstring b 78557 0 t ≡ 1 [MOD 2] := by
    calc repstring b 78557 0 t
        = 78557 * S b t := hrep
      _ ≡ 1 * 1 [MOD 2] := h78557.mul hS
      _ = 1 := by simp
  exact Nat.odd_iff.mpr hmod

private theorem S_ge_one {b t : ℕ} (hb : 2 ≤ b) (ht : 1 ≤ t) : 1 ≤ S b t := by
  rw [geom_eq_sum hb]
  have h0mem : (0 : ℕ) ∈ Finset.range t := Finset.mem_range.mpr (by omega)
  have hle : b ^ 0 ≤ ∑ i ∈ Finset.range t, b ^ i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le _) h0mem
  simpa using hle

private theorem repstring_ge {b t : ℕ} (hb : 78557 < b) (ht : 1 ≤ t) :
    78557 ≤ repstring b 78557 0 t := by
  have hb2 : 2 ≤ b := by omega
  have hS1 : 1 ≤ S b t := S_ge_one hb2 ht
  have hrep : repstring b 78557 0 t = 78557 * S b t := repstring_eq_mul_S hb
  calc (78557 : ℕ)
      = 78557 * 1 := by simp
    _ ≤ 78557 * S b t := Nat.mul_le_mul_left 78557 hS1
    _ = repstring b 78557 0 t := hrep.symm

private theorem isSierpinski_of_modEq_one {b t : ℕ} (hb : 78557 < b) (ht : 1 ≤ t)
    (htL : t ≡ 1 [MOD L b]) : IsSierpinskiNumber (repstring b 78557 0 t) := by
  let k := repstring b 78557 0 t
  refine ⟨repstring_odd hb ht htL, ?_⟩
  intro n hn
  change ¬ (k * 2 ^ n + 1).Prime
  obtain ⟨p, hpmem, hp2, hple, hperiod, hr⟩ :=
    hcover ⟨n % 36, Nat.mod_lt _ (by decide)⟩
  have hpmem' : p ∈ primes := (primes_list_mem_iff p).mp hpmem
  have hkrep : k ≡ 78557 [MOD p] := repstring_modEq hb ht hpmem' htL
  have hpow : 2 ^ n ≡ 2 ^ (n % 36) [MOD p] := by
    conv_lhs => rw [← Nat.mod_add_div n 36, pow_add, pow_mul]
    simpa only [one_pow, mul_one] using (hperiod.pow (n / 36)).mul_left (2 ^ (n % 36))
  have hdvd : p ∣ k * 2 ^ n + 1 :=
    Nat.modEq_zero_iff_dvd.mp (((hkrep.mul hpow).add_right 1).trans hr)
  have hk_le : 78557 ≤ k := repstring_ge hb ht
  have h2npos : 0 < 2 ^ n := by positivity
  have hkle : k ≤ k * 2 ^ n := Nat.le_mul_of_pos_right k h2npos
  exact Nat.not_prime_of_dvd_of_lt hdvd hp2 (by omega)

private theorem S_strictMono {b : ℕ} (hb : 2 ≤ b) : StrictMono (S b) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hsucc : S b (n + 1) = S b n + b ^ n := by
    rw [geom_eq_sum hb, geom_eq_sum hb, Finset.sum_range_succ]
  have hpos : 0 < b ^ n := by positivity
  omega

private theorem repstring_strictMono {b : ℕ} (hb : 78557 < b) :
    StrictMono (fun t => repstring b 78557 0 t) := by
  have hb2 : 2 ≤ b := by omega
  have hS := S_strictMono hb2
  intro a c hac
  have hlt : S b a < S b c := hS hac
  have hrep_a : repstring b 78557 0 a = 78557 * S b a := repstring_eq_mul_S hb
  have hrep_c : repstring b 78557 0 c = 78557 * S b c := repstring_eq_mul_S hb
  change repstring b 78557 0 a < repstring b 78557 0 c
  rw [hrep_a, hrep_c]
  exact (Nat.mul_lt_mul_left (by decide : 0 < 78557)).mpr hlt

private theorem L_pos (b : ℕ) : 1 ≤ L b := Nat.pos_of_ne_zero (L_ne_zero b)

private theorem arith_strictMono (b : ℕ) : StrictMono (fun n => 1 + L b * n) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hL : 1 ≤ L b := L_pos b
  have hmul : L b * n + L b = L b * (n + 1) := by ring
  omega

private theorem arith_modEq_one (b n : ℕ) : 1 + L b * n ≡ 1 [MOD L b] := by
  have h0 : L b * n ≡ 0 [MOD L b] := (dvd_mul_right (L b) n).modEq_zero_nat
  calc 1 + L b * n
      ≡ 1 + 0 [MOD L b] := Nat.ModEq.add_left 1 h0
    _ = 1 := by simp
end infinite_sierpinski_repdigits

/-- **Infinitely many Sierpiński repdigits in every base $b > 78557$.** Let $b > 78557$ be a
natural number. Then there are infinitely many Sierpiński numbers of the form $k(b^t - 1)/(b - 1)$
with $1 \le k < b$ and $t \ge 1$, that is, $b$-repdigits: the digit $k$ written $t$ times in
base $b$.

Source: Bispels, Cohen, Harrington, Lowrance, Pontes, Schaumann and Wong, *On Sierpiński and
Riesel Repdigits and Repintegers*, INTEGERS 26 (2026), Article A12, Corollary 3.7
(`integers-2026-A12-cor-3-7`). -/
public theorem infinite_sierpinski_repdigits {b : ℕ} (hb : 78557 < b) :
    {N : ℕ | ∃ k t : ℕ, 1 ≤ k ∧ k < b ∧ 1 ≤ t ∧ N = repstring b k 0 t ∧
      IsSierpinskiNumber N}.Infinite := by
  let f : ℕ → ℕ :=
    fun n => repstring b 78557 0 (1 + infinite_sierpinski_repdigits.L b * n)
  apply Set.infinite_of_injective_forall_mem (f := f)
  · have hrep := infinite_sierpinski_repdigits.repstring_strictMono hb
    have harith := infinite_sierpinski_repdigits.arith_strictMono b
    exact (hrep.comp harith).injective
  · intro n
    refine ⟨78557, 1 + infinite_sierpinski_repdigits.L b * n, by decide, hb,
      Nat.le_add_right 1 _, rfl, ?_⟩
    apply infinite_sierpinski_repdigits.isSierpinski_of_modEq_one hb
      (Nat.le_add_right 1 _)
      (infinite_sierpinski_repdigits.arith_modEq_one b n)

end MetaMathlibExt
