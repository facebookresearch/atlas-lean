/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Meromorphic Stirling and Bessel numbers

This file formalizes the two explicit identifications in Schork,
*On Generalized Stirling Numbers and Normal Ordering*:
<https://cs.uwaterloo.ca/journals/JIS/VOL15/Schork/schork2.tex>.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The meromorphic Stirling numbers $S_{2;-1}(n,k)$.** For natural numbers $n$ and $k$ with
$1 \le k \le n$, the meromorphic Stirling number $S_{2;-1}(n,k)$ is the rational number
$$S_{2;-1}(n,k) = \frac{(-1)^{n-k}\,(n-1)!}{2^{n-k}\,(k-1)!}\binom{2n-k-1}{n-1}.$$

For other $n$ and $k$ the same expression is evaluated with natural-number subtraction truncated
at $0$.

Source: Schork, On Generalized Stirling Numbers and Normal Ordering, StirW1 formula; concept
`meromorphic Stirling number` (`jis_sem_0210f8899dc06a2d15855412`), source
`jis_source_f3006b7ef496c012bfca9644`, statement `jis_9901739ac9112adc8aea1afb`, required clause
`first_meromorphic`. Defined independently from the Bessel side. -/
public def meromorphicStirlingFirst (n k : ℕ) : ℚ :=
  (((-1 : ℚ) ^ (n - k) * (((n - 1).factorial : ℕ) : ℚ)) /
    (((2 : ℚ) ^ (n - k)) * ((((k - 1).factorial : ℕ)) : ℚ))) *
    (((Nat.choose (2 * n - k - 1) (n - 1) : ℕ)) : ℚ)

/-- **The meromorphic Stirling numbers $S_{-1;1}(n,k)$.** For natural numbers $n$ and $k$ with
$k \le n \le 2k$, the meromorphic Stirling number $S_{-1;1}(n,k)$ is the rational number
$$S_{-1;1}(n,k) = \frac{(2n-2k)!}{2^{n-k}\,(n-k)!}\binom{n}{2k-n}.$$

For other $n$ and $k$ the same expression is evaluated with natural-number subtraction truncated
at $0$.

Source: Schork, On Generalized Stirling Numbers and Normal Ordering, StirW2 formula; concept
`meromorphic Stirling number` (`jis_sem_0210f8899dc06a2d15855412`), source
`jis_source_f3006b7ef496c012bfca9644`, statement `jis_9901739ac9112adc8aea1afb`, required clause
`second_meromorphic`. Defined independently from the Bessel side. -/
public def meromorphicStirlingSecond (n k : ℕ) : ℚ :=
  ((((2 * n - 2 * k).factorial : ℕ)) : ℚ) /
    (((2 : ℚ) ^ (n - k)) * ((((n - k).factorial : ℕ)) : ℚ)) *
    (((Nat.choose n (2 * k - n) : ℕ)) : ℚ)

/-- **Bessel numbers of the first kind.** For natural numbers $n$ and $k$ with $1 \le k \le n$, the
Bessel number of the first kind is the rational number
$$b(n,k) = \frac{(-1)^{n-k}\,(2n-k-1)!}{2^{n-k}\,(k-1)!\,(n-k)!}.$$

For other $n$ and $k$ the same expression is evaluated with natural-number subtraction truncated
at $0$.

Source: Schork, On Generalized Stirling Numbers and Normal Ordering, Bessfirst formula; concept
`meromorphic Stirling number` (`jis_sem_0210f8899dc06a2d15855412`), source
`jis_source_f3006b7ef496c012bfca9644`, statement `jis_9901739ac9112adc8aea1afb`, required clause
`first_bessel`. Defined independently from the meromorphic side. -/
public def besselNumberFirst (n k : ℕ) : ℚ :=
  ((-1 : ℚ) ^ (n - k) * ((((2 * n - k - 1).factorial : ℕ)) : ℚ)) /
    (((2 : ℚ) ^ (n - k)) * ((((k - 1).factorial : ℕ)) : ℚ) *
      ((((n - k).factorial : ℕ)) : ℚ))

/-- **Bessel numbers of the second kind.** For natural numbers $n$ and $k$ with $k \le n \le 2k$,
the Bessel number of the second kind is the rational number
$$B(n,k) = \frac{n!}{2^{n-k}\,(2k-n)!\,(n-k)!}.$$

For other $n$ and $k$ the same expression is evaluated with natural-number subtraction truncated
at $0$.

Source: Schork, On Generalized Stirling Numbers and Normal Ordering, Besssecond formula; concept
`meromorphic Stirling number` (`jis_sem_0210f8899dc06a2d15855412`), source
`jis_source_f3006b7ef496c012bfca9644`, statement `jis_9901739ac9112adc8aea1afb`, required clause
`second_bessel`. Defined independently from the meromorphic side. -/
public def besselNumberSecond (n k : ℕ) : ℚ :=
  ((((n.factorial : ℕ))) : ℚ) /
    (((2 : ℚ) ^ (n - k)) * ((((2 * k - n).factorial : ℕ)) : ℚ) *
      ((((n - k).factorial : ℕ)) : ℚ))

/-- **First identification of meromorphic Stirling and Bessel numbers.** For all natural numbers
$n$ and $k$ with $1 \le k \le n$, the meromorphic Stirling number $S_{2;-1}(n,k)$ equals the
Bessel number of the first kind $b(n,k)$.

Source: concept `meromorphic Stirling number` (`jis_sem_0210f8899dc06a2d15855412`),
source `jis_source_f3006b7ef496c012bfca9644`, statement `jis_9901739ac9112adc8aea1afb`,
required clause `first_identification`. -/
public theorem meromorphicStirlingFirst_eq_besselNumberFirst
    (n k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ n) :
    meromorphicStirlingFirst n k = besselNumberFirst n k := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le h1
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h2
  have hnm : 1 + k' + m = (k' + m) + 1 := by ring
  have e_n1 : 1 + k' + m - 1 = k' + m := by rw [hnm, Nat.add_sub_cancel]
  have hkk : 1 + k' = k' + 1 := by ring
  have e_k1 : 1 + k' - 1 = k' := by rw [hkk, Nat.add_sub_cancel]
  have hnk : 1 + k' + m = (1 + k') + m := by ring
  have e_nk : 1 + k' + m - (1 + k') = m := by rw [hnk, Nat.add_sub_cancel_left]
  have h2n : 2 * (1 + k' + m) = (1 + k') + ((k' + 2 * m) + 1) := by ring
  have estep : 2 * (1 + k' + m) - (1 + k') = (k' + 2 * m) + 1 := by
    rw [h2n, Nat.add_sub_cancel_left]
  have e_N : 2 * (1 + k' + m) - (1 + k') - 1 = k' + 2 * m := by
    rw [estep, Nat.add_sub_cancel]
  have hmm : k' + 2 * m = (k' + m) + m := by ring
  have hle_add : k' + m ≤ k' + 2 * m := by
    rw [hmm]
    exact Nat.le_add_right _ _
  have hle : 1 + k' + m - 1 ≤ 2 * (1 + k' + m) - (1 + k') - 1 := by
    rw [e_n1, e_N]
    exact hle_add
  have hsub_add : k' + 2 * m - (k' + m) = m := by
    rw [hmm, Nat.add_sub_cancel_left]
  have hsub : 2 * (1 + k' + m) - (1 + k') - 1 - (1 + k' + m - 1) =
      1 + k' + m - (1 + k') := by
    rw [e_N, e_n1, e_nk]
    exact hsub_add
  have hChoose := Nat.choose_mul_factorial_mul_factorial hle
  rw [hsub] at hChoose
  have hcast := congrArg (fun x : ℕ => (x : ℚ)) hChoose
  simp only [Nat.cast_mul] at hcast
  have key : (((1 + k' + m - 1).factorial : ℕ) : ℚ) *
      ((Nat.choose (2 * (1 + k' + m) - (1 + k') - 1) (1 + k' + m - 1) : ℕ) : ℚ) *
      ((((1 + k' + m - (1 + k')).factorial : ℕ)) : ℚ) =
      ((((2 * (1 + k' + m) - (1 + k') - 1).factorial : ℕ)) : ℚ) := by
    linear_combination hcast
  have h2ne : (2 : ℚ) ≠ 0 := by norm_num
  have hv : (2 : ℚ) ^ (1 + k' + m - (1 + k')) ≠ 0 := pow_ne_zero _ h2ne
  have hw : ((((1 + k') - 1).factorial : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF3 : ((((1 + k' + m - (1 + k')).factorial : ℕ)) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hd : (2 : ℚ) ^ (1 + k' + m - (1 + k')) *
      ((((1 + k') - 1).factorial : ℕ) : ℚ) ≠ 0 :=
    mul_ne_zero hv hw
  have eS : meromorphicStirlingFirst (1 + k' + m) (1 + k') =
      ((-1 : ℚ) ^ (1 + k' + m - (1 + k')) *
        ((((1 + k' + m - 1).factorial : ℕ)) : ℚ) *
        ((Nat.choose (2 * (1 + k' + m) - (1 + k') - 1) (1 + k' + m - 1) : ℕ) : ℚ)) /
      ((2 : ℚ) ^ (1 + k' + m - (1 + k')) *
        ((((1 + k') - 1).factorial : ℕ) : ℚ)) := by
    unfold meromorphicStirlingFirst
    ring
  have eB : besselNumberFirst (1 + k' + m) (1 + k') =
      ((-1 : ℚ) ^ (1 + k' + m - (1 + k')) *
        ((((2 * (1 + k' + m) - (1 + k') - 1).factorial : ℕ)) : ℚ)) /
      ((2 : ℚ) ^ (1 + k' + m - (1 + k')) *
        ((((1 + k') - 1).factorial : ℕ) : ℚ) *
        ((((1 + k' + m - (1 + k')).factorial : ℕ)) : ℚ)) := by
    unfold besselNumberFirst
    ring
  rw [eS, eB, div_eq_div_iff hd (mul_ne_zero hd hF3)]
  linear_combination ((-1 : ℚ) ^ (1 + k' + m - (1 + k')) *
    ((2 : ℚ) ^ (1 + k' + m - (1 + k')) *
      ((((1 + k') - 1).factorial : ℕ) : ℚ))) * key

/-- **Second identification of meromorphic Stirling and Bessel numbers.** For all natural numbers
$n$ and $k$ with $k \le n \le 2k$, the meromorphic Stirling number $S_{-1;1}(n,k)$ equals the
Bessel number of the second kind $B(n,k)$.

Source: concept `meromorphic Stirling number` (`jis_sem_0210f8899dc06a2d15855412`),
source `jis_source_f3006b7ef496c012bfca9644`, statement `jis_9901739ac9112adc8aea1afb`,
required clause `second_identification`. -/
public theorem meromorphicStirlingSecond_eq_besselNumberSecond
    (n k : ℕ) (h1 : n ≤ 2 * k) (h2 : k ≤ n) :
    meromorphicStirlingSecond n k = besselNumberSecond n k := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h2
  obtain ⟨u, hu⟩ := Nat.exists_eq_add_of_le h1
  have hkk : k + k = 2 * k := by ring
  have hass : (k + t) + u = k + (t + u) := by ring
  have htu : k + k = k + (t + u) := by rw [hkk, hu, hass]
  have hks : k = t + u := by omega
  subst hks
  have e_2kn : 2 * (t + u) - ((t + u) + t) = u := by
    rw [hu, Nat.add_sub_cancel_left]
  have h2n : 2 * ((t + u) + t) = 2 * (t + u) + 2 * t := by ring
  have e_2n2k : 2 * ((t + u) + t) - 2 * (t + u) = 2 * t := by
    rw [h2n, Nat.add_sub_cancel_left]
  have e_nk : (t + u) + t - (t + u) = t := by omega
  have hns : (t + u) + t = 2 * t + u := by ring
  have e_nsub : (t + u) + t - u = 2 * t := by
    rw [hns, Nat.add_sub_cancel]
  have hle_add : u ≤ 2 * t + u := Nat.le_add_left _ _
  have hle' : 2 * (t + u) - ((t + u) + t) ≤ (t + u) + t := by
    rw [e_2kn, hns]
    exact hle_add
  have hsub' : (t + u) + t - (2 * (t + u) - ((t + u) + t)) =
      2 * ((t + u) + t) - 2 * (t + u) := by
    rw [e_2kn, e_nsub, e_2n2k]
  have hChoose2 := Nat.choose_mul_factorial_mul_factorial hle'
  rw [hsub'] at hChoose2
  have hcast2 := congrArg (fun x : ℕ => (x : ℚ)) hChoose2
  simp only [Nat.cast_mul] at hcast2
  have key2 : ((((2 * ((t + u) + t) - 2 * (t + u)).factorial : ℕ)) : ℚ) *
      ((Nat.choose ((t + u) + t) (2 * (t + u) - ((t + u) + t)) : ℕ) : ℚ) *
      ((((2 * (t + u) - ((t + u) + t)).factorial : ℕ)) : ℚ) =
      ((((((t + u) + t).factorial : ℕ))) : ℚ) := by
    linear_combination hcast2
  have h2ne : (2 : ℚ) ≠ 0 := by norm_num
  have hv : (2 : ℚ) ^ ((t + u) + t - (t + u)) ≠ 0 := pow_ne_zero _ h2ne
  have hFt : (((((t + u) + t - (t + u)).factorial : ℕ)) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hF3 : ((((2 * (t + u) - ((t + u) + t)).factorial : ℕ)) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hd : (2 : ℚ) ^ ((t + u) + t - (t + u)) *
      (((((t + u) + t - (t + u)).factorial : ℕ)) : ℚ) ≠ 0 :=
    mul_ne_zero hv hFt
  have eS2 : meromorphicStirlingSecond ((t + u) + t) (t + u) =
      (((((2 * ((t + u) + t) - 2 * (t + u)).factorial : ℕ))) : ℚ) *
        ((Nat.choose ((t + u) + t) (2 * (t + u) - ((t + u) + t)) : ℕ) : ℚ) /
      ((2 : ℚ) ^ ((t + u) + t - (t + u)) *
        (((((t + u) + t - (t + u)).factorial : ℕ)) : ℚ)) := by
    unfold meromorphicStirlingSecond
    ring
  have eB2 : besselNumberSecond ((t + u) + t) (t + u) =
      ((((((t + u) + t).factorial : ℕ))) : ℚ) /
      ((2 : ℚ) ^ ((t + u) + t - (t + u)) *
        (((((t + u) + t - (t + u)).factorial : ℕ)) : ℚ) *
        ((((2 * (t + u) - ((t + u) + t)).factorial : ℕ)) : ℚ)) := by
    unfold besselNumberSecond
    ring
  rw [eS2, eB2, div_eq_div_iff hd (mul_ne_zero hd hF3)]
  linear_combination ((2 : ℚ) ^ ((t + u) + t - (t + u)) *
    (((((t + u) + t - (t + u)).factorial : ℕ)) : ℚ)) * key2

end

end MetaMathlibExt
