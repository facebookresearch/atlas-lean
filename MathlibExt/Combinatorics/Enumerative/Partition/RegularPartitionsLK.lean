/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
import Mathlib.Combinatorics.Enumerative.Partition.Glaisher
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Topology.Instances.ZMod

/-!
# Parity of regular partition counts

This file defines the number of `(ℓ, k)`-regular partitions and proves the parity congruence
for `(2, p)`-regular partitions in nonresidue progressions.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

/-- **Number of $(\ell, k)$-regular partitions.** For natural numbers $\ell$, $k$ and $n$,
$b_{\ell,k}(n)$ is the number of $(\ell, k)$-regular partitions of $n$, that is, partitions of
$n$ none of whose parts is divisible by $\ell$ or by $k$.

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Section 1 (definition of `b_{ℓ,k}(n)`). -/
public def regularPartitionCount (l k n : ℕ) : ℕ :=
  ((Finset.univ : Finset n.Partition).filter fun p => ∀ i ∈ p.parts, ¬ l ∣ i ∧ ¬ k ∣ i).card

/-- **The $(4, 9)$-regular partition count at zero.** The number $b_{4,9}(0)$ of
$(4, 9)$-regular partitions of $0$, that is, partitions of $0$ none of whose parts is divisible by
$4$ or by $9$, equals $1$: the only such partition is the empty partition.

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Section 1 (definition of `b_{ℓ,k}(n)`). -/
public theorem regularPartitionCount_four_nine_zero : regularPartitionCount 4 9 0 = 1 := by
  decide

/-- **For small $n$ every partition is $(\ell, k)$-regular.** Let $\ell$, $k$ and $n$ be natural
numbers with $n < \ell$ and $n < k$, and write $b_{\ell,k}(n)$ for the number of
$(\ell, k)$-regular partitions of $n$ (partitions none of whose parts is divisible by $\ell$ or by
$k$) and $p(n)$ for the number of all partitions of $n$. Then every partition of $n$ is
$(\ell, k)$-regular, so $b_{\ell,k}(n) = p(n)$.

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Section 1 (definition of `b_{ℓ,k}(n)`). -/
public theorem regularPartitionCount_of_lt {l k n : ℕ} (hl : n < l) (hk : n < k) :
    regularPartitionCount l k n = Fintype.card n.Partition := by
  rw [regularPartitionCount, Finset.filter_true_of_mem, Finset.card_univ]
  intro p _ i hi
  have hpos := p.parts_pos hi
  have hle : i ≤ n := by
    rw [← p.parts_sum]
    exact Multiset.le_sum_of_mem hi
  exact ⟨fun h => absurd (Nat.le_of_dvd hpos h) (by omega),
    fun h => absurd (Nat.le_of_dvd hpos h) (by omega)⟩

namespace regularPartitionCount_two_prime_mod_two

open PowerSeries.WithPiTopology

local notation "𝓔" => pentagonalSeries (ZMod 2)

private lemma euler_constantCoeff : constantCoeff 𝓔 = 1 := by
  rw [← coeff_zero_eq_constantCoeff, show (0 : ℕ) = pentagonal 0 by simp [pentagonal_def],
    coeff_pentagonalSeries_pentagonal]
  simp

private lemma hasProd_euler_expand (k : ℕ) (hk : k ≠ 0) :
    HasProd (fun i : ℕ => (1 : (ZMod 2)⟦X⟧) - X ^ (k * (i + 1))) (expand k hk 𝓔) := by
  have hcont : Continuous (expand k hk (R := ZMod 2)) := by
    apply continuous_iff_continuousAt.mpr
    intro f
    rw [ContinuousAt, tendsto_iff_coeff_tendsto]
    intro d
    by_cases hd : k ∣ d
    · obtain ⟨i, rfl⟩ := hd
      simpa only [coeff_expand_mul, ContinuousAt] using
        (continuous_coeff (ZMod 2) i).continuousAt (x := f)
    · simp only [coeff_expand_of_not_dvd _ _ _ hd]
      exact tendsto_const_nhds
  simpa only [Function.comp_def, map_sub, map_one, map_pow, expand_X, ← pow_mul]
    using (hasProd_one_sub_X_pow (ZMod 2)).map (expand k hk (R := ZMod 2)) hcont

private lemma hasProd_euler_multiples (k : ℕ) (hk : k ≠ 0) :
    HasProd (fun i : ℕ => if k ∣ i + 1 then (1 : (ZMod 2)⟦X⟧) - X ^ (i + 1) else 1)
      (expand k hk 𝓔) := by
  let shift (i : ℕ) := k * (i + 1) - 1
  have hshift (i : ℕ) : shift i + 1 = k * (i + 1) :=
    Nat.sub_add_cancel (Nat.mul_pos (Nat.pos_of_ne_zero hk) (Nat.succ_pos i))
  have hinj : Function.Injective shift := by
    intro i j hij
    have h : shift i + 1 = shift j + 1 := congrArg (· + 1) hij
    rw [hshift, hshift, mul_right_inj' hk, Nat.add_right_cancel_iff] at h
    exact h
  refine (hinj.hasProd_iff ?_).mp ?_
  · intro i hi
    have hnd : ¬ k ∣ i + 1 := by
      rintro ⟨j, hj⟩
      refine hi ⟨j - 1, ?_⟩
      have hj0 : j ≠ 0 := by rintro rfl; simp at hj
      rw [← Nat.add_right_cancel_iff (n := 1), hshift,
        Nat.sub_add_cancel (Nat.pos_of_ne_zero hj0), hj]
    simp [hnd]
  · simpa [Function.comp_def, hshift] using hasProd_euler_expand k hk

private lemma euler_expand_two_mul (k : ℕ) (hk : k ≠ 0) :
    expand (2 * k) (mul_ne_zero two_ne_zero hk) 𝓔 = (expand k hk 𝓔) ^ 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [expand_mul]
  simpa only [ZMod.card] using FiniteField.PowerSeries.expand_card (expand k hk 𝓔)

-- Clear the Euler product denominators in the restricted-partition generating function.
private lemma generatingFunction_mul_euler {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (mk fun n => (regularPartitionCount 2 p n : ZMod 2)) * expand p hp.ne_zero 𝓔 = 𝓔 := by
  let G := mk fun n => (regularPartitionCount 2 p n : ZMod 2)
  have hG := Nat.Partition.hasProd_powerSeriesMk_card_restricted (ZMod 2)
    (fun i => ¬ 2 ∣ i ∧ ¬ p ∣ i)
  change HasProd (fun i : ℕ => if ¬ 2 ∣ i + 1 ∧ ¬ p ∣ i + 1 then
    ∑' j : ℕ, X ^ ((i + 1) * j) else 1) G at hG
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (by omega)
  -- The Euler factor occurs twice at part sizes divisible by both 2 and p.
  have hprod : G * 𝓔 * expand (2 * p) (mul_ne_zero two_ne_zero hp.ne_zero) 𝓔 =
      expand 2 two_ne_zero 𝓔 * expand p hp.ne_zero 𝓔 := by
    refine ((hG.mul (hasProd_one_sub_X_pow (ZMod 2))).mul
      (hasProd_euler_multiples _ _)).unique
      (((hasProd_euler_multiples 2 two_ne_zero).mul
        (hasProd_euler_multiples p hp.ne_zero)).congr_fun ?_)
    intro i
    have hboth : 2 * p ∣ i + 1 ↔ 2 ∣ i + 1 ∧ p ∣ i + 1 :=
      ⟨fun h => ⟨dvd_of_mul_right_dvd h, dvd_of_mul_left_dvd h⟩,
        fun h => hcop.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
    by_cases h₂ : 2 ∣ i + 1 <;> by_cases hp' : p ∣ i + 1 <;> simp [hboth, h₂, hp']
    simpa only [pow_mul] using tsum_pow_mul_one_sub_of_constantCoeff_eq_zero
      (f := (X : (ZMod 2)⟦X⟧) ^ (i + 1)) (by simp)
  have hE : 𝓔 ≠ 0 := by
    intro h
    simpa [h] using euler_constantCoeff
  have hEp : expand p hp.ne_zero 𝓔 ≠ 0 := by
    intro h
    have := congrArg (constantCoeff (R := ZMod 2)) h
    simp [euler_constantCoeff] at this
  rw [euler_expand_two_mul p hp.ne_zero, show expand 2 two_ne_zero 𝓔 = 𝓔 ^ 2 by
    simpa using euler_expand_two_mul 1 one_ne_zero] at hprod
  apply mul_right_cancel₀ (mul_ne_zero hE hEp)
  calc
    (G * expand p hp.ne_zero 𝓔) * (𝓔 * expand p hp.ne_zero 𝓔) =
        G * 𝓔 * (expand p hp.ne_zero 𝓔) ^ 2 := by ring
    _ = 𝓔 ^ 2 * expand p hp.ne_zero 𝓔 := hprod
    _ = 𝓔 * (𝓔 * expand p hp.ne_zero 𝓔) := by ring

private lemma coeff_eq_zero_of_nonresidue {p r : ℕ} (hp : p ≠ 0)
    (hr : ¬ IsSquare ((24 * r + 1 : ℕ) : ZMod p))
    {F : (ZMod 2)⟦X⟧} (hF : F * expand p hp 𝓔 = 𝓔) (m : ℕ)
    (hm : (m : ZMod p) = r) : F.coeff m = 0 := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
    -- At a pentagonal index m, completing the square makes 24m + 1 a square.
    have hEuler : coeff m 𝓔 = 0 := by
      apply coeff_pentagonalSeries_eq_zero
      rintro ⟨j, rfl⟩
      apply hr
      refine ⟨(6 * j - 1 : ℤ), ?_⟩
      have hsquare : 24 * (pentagonal j : ℤ) + 1 = (6 * j - 1) * (6 * j - 1) := by
        linear_combination 12 * two_mul_natCast_pentagonal j
      have hcast := congrArg (fun a : ℤ => (a : ZMod p)) hsquare
      push_cast at hcast ⊢
      rwa [hm] at hcast
    have hcoeff : coeff m (F * expand p hp 𝓔) = 0 := by rw [hF, hEuler]
    rw [coeff_mul] at hcoeff
    -- A positive index from the expanded factor leaves a smaller index in the same residue class.
    have hsingle : ∑ a ∈ Finset.antidiagonal m, F.coeff a.1 *
        (expand p hp 𝓔).coeff a.2 = F.coeff m := by
      rw [Finset.sum_eq_single_of_mem (m, 0) (by simp)]
      · simp [coeff_zero_eq_constantCoeff, euler_constantCoeff]
      · intro a ha hne
        have ha' := Finset.mem_antidiagonal.mp ha
        by_cases hd : p ∣ a.2
        · have ha₂ : a.2 ≠ 0 := by
            rintro hz
            apply hne
            exact Prod.ext (by simpa [hz] using ha') hz
          have hlt : a.1 < m := by omega
          have hcast := congrArg (fun k : ℕ => (k : ZMod p)) ha'
          rw [Nat.cast_add, (ZMod.natCast_eq_zero_iff _ _).mpr hd, add_zero, hm] at hcast
          rw [ih a.1 hlt hcast, zero_mul]
        · rw [coeff_expand_of_not_dvd _ _ _ hd, mul_zero]
    exact hsingle ▸ hcoeff

end regularPartitionCount_two_prime_mod_two

open regularPartitionCount_two_prime_mod_two in
/-- **Parity of $(2, p)$-regular partitions in nonresidue progressions.** Let $p \ge 5$ be a
prime and let $r$ be a natural number such that $24r + 1$ is not a square modulo $p$ (a quadratic
nonresidue). Write $b_{2,p}(m)$ for the number of $(2, p)$-regular partitions of $m$, that is,
partitions of $m$ none of whose parts is divisible by $2$ or by $p$. Then
$b_{2,p}(pn + r) \equiv 0 \pmod 2$ for every natural number $n$.

Restricting $r$ to natural numbers loses nothing: every residue class modulo $p$ has a
natural-number representative.

Source: Manjil P. Saikia and James A. Sellers, *Generalizing Recent Results of Kathiravan,
Majumdar, Sangale, and Srinivas on `(ℓ, k)`-regular Partitions*, Journal of Integer Sequences
28 (2025), Article 25.6.1, Theorem 2 (`jis-2025-25.6.1-thm-2`). -/
public theorem regularPartitionCount_two_prime_mod_two {p r : ℕ} (hp : p.Prime)
    (h5 : 5 ≤ p) (hr : ¬ IsSquare ((24 * r + 1 : ℕ) : ZMod p)) (n : ℕ) :
    regularPartitionCount 2 p (p * n + r) ≡ 0 [MOD 2] := by
  have hm : ((p * n + r : ℕ) : ZMod p) = r := by
    simp [Nat.cast_add, Nat.cast_mul]
  have hz := coeff_eq_zero_of_nonresidue hp.ne_zero hr
    (generatingFunction_mul_euler hp h5) (p * n + r) hm
  exact Nat.modEq_zero_iff_dvd.mpr ((ZMod.natCast_eq_zero_iff _ _).mp (by simpa using hz))

end

end MetaMathlibExt
