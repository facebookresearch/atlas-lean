/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring.RingNF

namespace MetaMathlibExt

@[expose] public section

private theorem tri_ceil_le_self (V k : ℕ) (hV : 1 ≤ V) (hk : 1 ≤ k) :
    (V + k - 1) / k ≤ V := by
  have hkpos : 0 < k := by omega
  rw [Nat.div_le_iff_le_mul_add_pred hkpos]
  have hVle : V ≤ k * V := by
    calc V = 1 * V := (one_mul V).symm
    _ ≤ k * V := Nat.mul_le_mul_right V hk
  omega

private theorem tri_le_ceil_mul (V k : ℕ) (hk : 1 ≤ k) :
    V ≤ ((V + k - 1) / k) * k := by
  have hkpos : 0 < k := by omega
  have hmod := Nat.div_add_mod (V + k - 1) k
  have hlt := Nat.mod_lt (V + k - 1) hkpos
  have hcomm : k * ((V + k - 1) / k) = ((V + k - 1) / k) * k := mul_comm _ _
  omega

private theorem tri_ceil_zero (k : ℕ) (hk : 1 ≤ k) : (0 + k - 1) / k = 0 := by
  have h0 : 0 + k - 1 = k - 1 := by omega
  rw [h0]
  exact Nat.div_eq_of_lt (by omega)

private theorem S_obtain (a d h k n : ℕ) (c : ℕ → ℕ) (_hsup : ∀ i, k < i → c i = 0)
    (heq : n = ∑ i ∈ Finset.range (k + 1),
      c i * (if i = 0 then a else h * a + i * d)) :
    ∃ u v C : ℕ, n = u * a + v * d ∧ h * C ≤ u ∧ C ≤ v ∧ v ≤ C * k := by
  classical
  set s := (Finset.range (k + 1)).erase 0 with hs
  have h0mem : 0 ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.succ_pos k)
  have hsplit := Finset.add_sum_erase (Finset.range (k + 1))
    (fun i => c i * (if i = 0 then a else h * a + i * d)) h0mem
  refine ⟨c 0 + h * (∑ i ∈ s, c i), ∑ i ∈ s, i * c i, ∑ i ∈ s, c i,
    ?_, Nat.le_add_left _ _, ?_, ?_⟩
  · -- value equation
    have hCmul : (∑ i ∈ s, c i) * (h * a) = ∑ i ∈ s, c i * (h * a) := by
      rw [Finset.sum_mul]
    have hTmul : (∑ i ∈ s, i * c i) * d = ∑ i ∈ s, (i * c i) * d := by
      rw [Finset.sum_mul]
    have hterm : ∀ i ∈ s, c i * (h * a + i * d) = c i * (h * a) + (i * c i) * d := by
      intro i _
      ring
    have hsum : ∑ i ∈ s, c i * (h * a + i * d)
        = (∑ i ∈ s, c i) * (h * a) + (∑ i ∈ s, i * c i) * d := by
      rw [hCmul, hTmul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      exact hterm i hi
    have hif : ∀ i ∈ s, (if i = 0 then a else h * a + i * d) = h * a + i * d := by
      intro i hi
      have hne : i ≠ 0 := Finset.ne_of_mem_erase hi
      simp [hne]
    have hrest : ∑ i ∈ s, c i * (if i = 0 then a else h * a + i * d)
        = ∑ i ∈ s, c i * (h * a + i * d) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hif i hi]
    have h0term : c 0 * (if (0 : ℕ) = 0 then a else h * a + 0 * d) = c 0 * a := by
      simp
    rw [heq, ← hsplit, h0term, hrest, hsum]
    ring
  · -- C ≤ T
    apply Finset.sum_le_sum
    intro i hi
    have hi1 : 1 ≤ i := by
      have hne : i ≠ 0 := Finset.ne_of_mem_erase hi
      omega
    calc c i = 1 * c i := (one_mul _).symm
    _ ≤ i * c i := Nat.mul_le_mul_right (c i) hi1
  · -- T ≤ C * k
    have hle : ∑ i ∈ s, i * c i ≤ ∑ i ∈ s, k * c i := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := by
        have hmem : i ∈ Finset.range (k + 1) := Finset.mem_of_mem_erase hi
        have := (Finset.mem_range.mp hmem)
        omega
      exact Nat.mul_le_mul_right (c i) hik
    have hkeq : ∑ i ∈ s, k * c i = (∑ i ∈ s, c i) * k := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    omega

private theorem S_zero_mem (S : Set ℕ) (a d h k : ℕ)
    (hS : S = { n | ∃ c : ℕ → ℕ, (∀ i, k < i → c i = 0) ∧
      n = ∑ i ∈ Finset.range (k + 1),
        c i * (if i = 0 then a else h * a + i * d) }) :
    0 ∈ S := by
  rw [hS]
  refine ⟨fun _ => 0, fun i _ => rfl, ?_⟩
  simp

private theorem S_gen_mem (S : Set ℕ) (a d h k j : ℕ) (hj : j ≤ k)
    (hS : S = { n | ∃ c : ℕ → ℕ, (∀ i, k < i → c i = 0) ∧
      n = ∑ i ∈ Finset.range (k + 1),
        c i * (if i = 0 then a else h * a + i * d) }) :
    (if j = 0 then a else h * a + j * d) ∈ S := by
  classical
  rw [hS]
  refine ⟨fun i => if i = j then 1 else 0, ?_, ?_⟩
  · intro i hi
    have hne : i ≠ j := by omega
    simp [hne]
  · have hjmem : j ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
    have hsum : ∑ i ∈ Finset.range (k + 1),
          (if i = j then 1 else 0) * (if i = 0 then a else h * a + i * d)
        = (if j = 0 then a else h * a + j * d) := by
      have hcongr : ∀ i ∈ Finset.range (k + 1),
            (if i = j then 1 else 0) * (if i = 0 then a else h * a + i * d)
            = (if i = j then (if i = 0 then a else h * a + i * d) else 0) := by
        intro i _
        by_cases hij : i = j
        · simp [hij]
        · simp [hij]
      rw [Finset.sum_congr rfl hcongr]
      rw [Finset.sum_ite_eq' _ j _]
      simp [hjmem]
    exact hsum.symm

private theorem S_add_mem (S : Set ℕ) (a d h k : ℕ) (m n : ℕ) (hm : m ∈ S) (hn : n ∈ S)
    (hS : S = { n | ∃ c : ℕ → ℕ, (∀ i, k < i → c i = 0) ∧
      n = ∑ i ∈ Finset.range (k + 1),
        c i * (if i = 0 then a else h * a + i * d) }) :
    m + n ∈ S := by
  classical
  rw [hS] at hm hn ⊢
  obtain ⟨c1, h1sup, h1eq⟩ := hm
  obtain ⟨c2, h2sup, h2eq⟩ := hn
  refine ⟨fun i => c1 i + c2 i, ?_, ?_⟩
  · intro i hi
    change c1 i + c2 i = 0
    rw [h1sup i hi, h2sup i hi, Nat.add_zero]
  · rw [h1eq, h2eq, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring

private theorem S_ceil_intro (a d h k U V : ℕ) (hk : 1 ≤ k)
    (hle : h * ((V + k - 1) / k) ≤ U) :
    U * a + V * d ∈ { n | ∃ c : ℕ → ℕ, (∀ i, k < i → c i = 0) ∧
      n = ∑ i ∈ Finset.range (k + 1),
        c i * (if i = 0 then a else h * a + i * d) } := by
  classical
  by_cases hV0 : V = 0
  · subst hV0
    rw [tri_ceil_zero k hk] at hle
    refine ⟨fun i => if i = 0 then U else 0, ?_, ?_⟩
    · intro i hi
      have hne : i ≠ 0 := by omega
      simp [hne]
    · have h0mem : (0 : ℕ) ∈ Finset.range (k + 1) :=
        Finset.mem_range.mpr (by omega)
      have hcongr : ∀ i ∈ Finset.range (k + 1),
            (if i = 0 then U else 0) * (if i = 0 then a else h * a + i * d)
            = (if i = 0 then U * (if i = 0 then a else h * a + i * d) else 0) := by
        intro i _
        by_cases hij : i = 0
        · simp [hij]
        · simp [hij]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq' _ 0 _]
      simp [h0mem]
  · have hVpos : 1 ≤ V := by omega
    have hkpos : 0 < k := by omega
    have hCe1 : 1 ≤ (V + k - 1) / k := by
      rw [Nat.le_div_iff_mul_le hkpos]
      omega
    obtain ⟨m, hm⟩ : ∃ m, (V + k - 1) / k = m + 1 :=
      Nat.exists_eq_succ_of_ne_zero (by omega)
    have hdiv : ((V + k - 1) / k) * k ≤ V + k - 1 := Nat.div_mul_le_self _ _
    rw [hm] at hdiv hle
    have hCelo : m * k < V := by
      by_contra hcon
      push Not at hcon
      have hadd : m * k + k = (m + 1) * k := by ring
      omega
    have hCehi : V ≤ (m + 1) * k := by
      rw [← hm]
      exact tri_le_ceil_mul V k hk
    obtain ⟨f, hfm, hf1, hfk⟩ : ∃ f : ℕ, m * k + f = V ∧ 1 ≤ f ∧ f ≤ k := by
      refine ⟨V - m * k, Nat.add_sub_cancel' (by omega), by omega, ?_⟩
      have hadd : m * k + k = (m + 1) * k := by ring
      omega
    obtain ⟨W, hW⟩ : ∃ W, U = W + h * (m + 1) :=
      ⟨U - h * (m + 1), (Nat.sub_add_cancel hle).symm⟩
    refine ⟨fun i => (if i = 0 then W else 0)
      + (if i = k then m else 0) + (if i = f then 1 else 0), ?_, ?_⟩
    · intro i hi
      have hi0 : i ≠ 0 := by omega
      have hik : i ≠ k := by omega
      have hif : i ≠ f := by omega
      simp [hi0, hik, hif]
    · have h0mem : (0 : ℕ) ∈ Finset.range (k + 1) :=
        Finset.mem_range.mpr (by omega)
      have hkmem : k ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
      have hfmem : f ∈ Finset.range (k + 1) :=
        Finset.mem_range.mpr (by omega)
      have e0 : ∑ i ∈ Finset.range (k + 1),
            (if i = 0 then W else 0)
              * (if i = 0 then a else h * a + i * d)
          = W * a := by
        have hcongr : ∀ i ∈ Finset.range (k + 1),
              (if i = 0 then W else 0)
                * (if i = 0 then a else h * a + i * d)
              = (if i = 0 then W * (if i = 0 then a else h * a + i * d) else 0) := by
          intro i _
          by_cases hij : i = 0
          · simp [hij]
          · simp [hij]
        rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq' _ 0 _]
        simp [h0mem]
      have ek : ∑ i ∈ Finset.range (k + 1),
            (if i = k then m else 0) * (if i = 0 then a else h * a + i * d)
          = m * (h * a + k * d) := by
        have hcongr : ∀ i ∈ Finset.range (k + 1),
              (if i = k then m else 0) * (if i = 0 then a else h * a + i * d)
              = (if i = k then m * (if i = 0 then a else h * a + i * d) else 0) := by
          intro i _
          by_cases hij : i = k
          · simp [hij]
          · simp [hij]
        rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq' _ k _]
        have hk0 : k ≠ 0 := by omega
        simp [hkmem, hk0]
      have ef : ∑ i ∈ Finset.range (k + 1),
            (if i = f then 1 else 0)
              * (if i = 0 then a else h * a + i * d)
          = 1 * (h * a + f * d) := by
        have hcongr : ∀ i ∈ Finset.range (k + 1),
              (if i = f then 1 else 0)
                * (if i = 0 then a else h * a + i * d)
              = (if i = f then 1
                  * (if i = 0 then a else h * a + i * d) else 0) := by
          intro i _
          by_cases hij : i = f
          · simp [hij]
          · simp [hij]
        rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq' _ f _]
        have hf0 : f ≠ 0 := by omega
        simp [hfmem, hf0]
      have hsplit : ∑ i ∈ Finset.range (k + 1),
            (((if i = 0 then W else 0)
              + (if i = k then m else 0) + (if i = f then 1 else 0))
              * (if i = 0 then a else h * a + i * d))
          = (∑ i ∈ Finset.range (k + 1),
              (if i = 0 then W else 0)
                * (if i = 0 then a else h * a + i * d))
            + (∑ i ∈ Finset.range (k + 1),
              (if i = k then m else 0) * (if i = 0 then a else h * a + i * d))
            + (∑ i ∈ Finset.range (k + 1),
              (if i = f then 1 else 0)
                * (if i = 0 then a else h * a + i * d)) := by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hsplit, e0, ek, ef, hW, ← hfm]
      ring

private theorem S_mod_bound (a d h k U V u v C : ℕ) (ha : 0 < a) (hk : 0 < k)
    (hgcd : Nat.gcd a d = 1)
    (hCu : h * C ≤ u) (_hCv : C ≤ v) (hvk : v ≤ C * k)
    (hVlt : V < a)
    (heq : U * a + V * d = u * a + v * d) :
    h * ((V + k - 1) / k) ≤ U := by
  have hz1 : U * a ≡ 0 [MOD a] := Nat.modEq_zero_iff_dvd.mpr ⟨U, by ring⟩
  have hz2 : u * a ≡ 0 [MOD a] := Nat.modEq_zero_iff_dvd.mpr ⟨u, by ring⟩
  have hm1 : U * a + V * d ≡ V * d [MOD a] := by
    have h := hz1.add_right (V * d)
    rw [zero_add] at h
    exact h
  have hm2 : u * a + v * d ≡ v * d [MOD a] := by
    have h := hz2.add_right (v * d)
    rw [zero_add] at h
    exact h
  have hmeq : U * a + V * d ≡ u * a + v * d [MOD a] := by
    rw [heq]
  have hVd : V * d ≡ v * d [MOD a] := (hm1.symm.trans hmeq).trans hm2
  have hcongr : d * V ≡ d * v [MOD a] := by
    rw [mul_comm V d, mul_comm v d] at hVd
    exact hVd
  have hVv : V ≡ v [MOD a] := Nat.ModEq.cancel_left_of_coprime hgcd hcongr
  have hveq : v % a = V := by
    have hsymm := hVv.symm
    simp only [Nat.ModEq] at hsymm
    rw [Nat.mod_eq_of_lt hVlt] at hsymm
    omega
  have hle : V ≤ v := by
    by_contra hcon
    push Not at hcon
    have hltv : v < a := by omega
    have hvv : v % a = v := Nat.mod_eq_of_lt hltv
    omega
  obtain ⟨t, ht⟩ : ∃ t, v - V = a * t := (Nat.modEq_iff_dvd' hle).mp hVv
  have hv : v = V + a * t := by omega
  have hexpand : u * a + (V + a * t) * d = (u + t * d) * a + V * d := by ring
  have hU : U = u + t * d := by
    have heq2 : U * a + V * d = (u + t * d) * a + V * d := by
      rw [hv] at heq
      rw [hexpand] at heq
      exact heq
    have hcan : U * a = (u + t * d) * a := add_right_cancel heq2
    exact Nat.mul_right_cancel ha hcan
  have hVle : V ≤ C * k := le_trans hle hvk
  have hceil : (V + k - 1) / k ≤ C := by
    rw [Nat.div_le_iff_le_mul_add_pred hk]
    have hcomm : k * C = C * k := mul_comm _ _
    omega
  calc h * ((V + k - 1) / k) ≤ h * C := Nat.mul_le_mul_left h hceil
  _ ≤ h * C + t * d := Nat.le_add_right _ _
  _ ≤ u + t * d := Nat.add_le_add_right hCu _
  _ = U := hU.symm

private theorem tri_div_sub (x k q r : ℕ) (_hk : 0 < k) (_hr1 : 1 ≤ r) (hrk : r ≤ k)
    (hlo : q * k + 1 ≤ x) (hhi : x ≤ q * k + r) : (x - 1) / k = q := by
  apply Nat.div_eq_of_lt_le
  · omega
  · have h1 : (q + 1) * k = q * k + k := by ring
    omega

private theorem tri_div_add (x k q r : ℕ) (_hk : 0 < k) (_hr1 : 1 ≤ r) (hrk : r ≤ k)
    (hlo : q * k + 1 ≤ x) (hhi : x ≤ q * k + r) : (x + k - 1) / k = q + 1 := by
  apply Nat.div_eq_of_lt_le
  · have h1 : (q + 1) * k = q * k + k := by ring
    omega
  · have h2 : (q + 1 + 1) * k = q * k + k + k := by ring
    omega

private theorem tri_div_le (V k q r : ℕ) (hk : 0 < k) (hrk : r ≤ k)
    (hV : V ≤ q * k + r) : (V + k - 1) / k ≤ q + 1 := by
  rw [Nat.div_le_iff_le_mul_add_pred hk]
  have h1 : k * (q + 1) = q * k + k := by ring
  omega

private theorem S_reduce (a d u v : ℕ) :
    (u + (v / a) * d) * a + (v % a) * d = u * a + v * d := by
  have hdm := Nat.div_add_mod v a
  conv_rhs => rw [← hdm]
  ring

/-! # Explicit pseudo-Frobenius set for arithmetic-progression semigroups
-/

/-- **Tripathi's pseudo-Frobenius formula without assuming $d > 0$.** Let $a$, $h$ and $k$ be
positive integers and $d$ a natural number with $\gcd(a, d) = 1$, and let $q$ and $r$ be natural
numbers with $1 \le r \le k$ and $a - 1 = qk + r$. Let $S$ be the set of all sums
$c_0 a + \sum_{i=1}^{k} c_i (ha + id)$ with natural numbers $c_0, \dots, c_k$. Then the natural
numbers $y \notin S$ such that $y + s \in S$ for every nonzero $s \in S$ are exactly the numbers
$$y = ha \left\lfloor \frac{x - 1}{k} \right\rfloor + (h - 1)a + dx$$
with $x$ a natural number satisfying $a - r \le x \le a - 1$.

The hypotheses force $d > 0$: if $d = 0$, then $\gcd(a, d) = a = 1$, and $a - 1 = qk + r$ with
$r \ge 1$ is impossible. -/
theorem tripathi_pseudo_frobenius_arithmetic_progression_general
    (a d h k : ℕ) (ha : 0 < a) (hh : 0 < h) (hk : 0 < k)
    (hgcd : Nat.gcd a d = 1) (q r : ℕ) (hr1 : 1 ≤ r) (hrk : r ≤ k)
    (hqr : a - 1 = q * k + r)
    (S : Set ℕ)
    (hS : S = { n | ∃ c : ℕ → ℕ, (∀ i, k < i → c i = 0) ∧
      n = ∑ i ∈ Finset.range (k + 1),
        c i * (if i = 0 then a else h * a + i * d) }) :
    { x | x ∉ S ∧ ∀ s ∈ S, s ≠ 0 → x + s ∈ S } =
      { y | ∃ x : ℕ, a - r ≤ x ∧ x ≤ a - 1 ∧
        y = h * a * ((x - 1) / k) + (h - 1) * a + d * x } := by
  classical
  have hk1 : 1 ≤ k := hk
  have ha2 : 2 ≤ a := by omega
  have har : a - r = q * k + 1 := by omega
  have haqr : a = q * k + r + 1 := by omega
  have haS : a ∈ S := by
    have h0 := S_gen_mem S a d h k 0 (by omega) hS
    simpa using h0
  have hane : a ≠ 0 := by omega
  have hGjmem : ∀ j : ℕ, j ≤ k →
      (if j = 0 then a else h * a + j * d) ∈ S :=
    fun j hj => S_gen_mem S a d h k j hj hS
  have hGjpos : ∀ j : ℕ, j ≤ k → 0 < (if j = 0 then a else h * a + j * d) := by
    intro j hj
    by_cases hj0 : j = 0
    · simp [hj0, ha]
    · simp only [hj0, ite_false]
      have hpos : 0 < h * a := Nat.mul_pos hh ha
      omega
  apply Set.ext
  intro y
  constructor
  · -- Forward: every pseudo-Frobenius number has the required form.
    rintro ⟨hynot, hyadd⟩
    have hyaS : y + a ∈ S := hyadd a haS hane
    rw [hS] at hyaS
    obtain ⟨c, hcsup, hceq⟩ := hyaS
    obtain ⟨u, v, C, huv, hCu0, hCv0, hvk0⟩ := S_obtain a d h k (y + a) c hcsup hceq
    have hu1 : 1 ≤ u := by
      by_contra hcon
      push Not at hcon
      have hu0 : u = 0 := by omega
      subst hu0
      have hC0 : C = 0 := by
        by_contra hcon2
        push Not at hcon2
        have hcpos : 0 < C := by omega
        have hpos : 0 < h * C := Nat.mul_pos hh hcpos
        omega
      subst hC0
      simp only [mul_zero, zero_mul, zero_add] at hCu0 hvk0 huv
      have hv0 : v = 0 := by omega
      subst hv0
      simp only [zero_mul] at huv
      omega
    obtain ⟨u', hu'⟩ : ∃ u', u = u' + 1 := ⟨u - 1, by omega⟩
    subst hu'
    have hyUV : y = u' * a + v * d := by
      have heq2 : (u' + 1) * a = u' * a + a := by ring
      rw [heq2] at huv
      omega
    have hV0lt : v % a < a := Nat.mod_lt v ha
    have hyred : y = (u' + (v / a) * d) * a + (v % a) * d := by
      have hred := S_reduce a d u' v
      rw [hyUV]
      exact hred.symm
    have hUbound : u' + (v / a) * d < h * ((v % a + k - 1) / k) := by
      by_contra hcon
      push Not at hcon
      apply hynot
      rw [hS]
      have hmem := S_ceil_intro a d h k (u' + (v / a) * d) (v % a) hk1 hcon
      rwa [← hyred] at hmem
    have hyaeq : (u' + (v / a) * d + 1) * a + (v % a) * d
        = (u' + 1) * a + v * d := by
      have h1 : (u' + (v / a) * d + 1) * a + (v % a) * d = y + a := by
        rw [hyred]
        ring
      rw [h1, huv]
    have hbound2 : h * ((v % a + k - 1) / k) ≤ u' + (v / a) * d + 1 :=
      S_mod_bound a d h k (u' + (v / a) * d + 1) (v % a) (u' + 1) v C
        ha hk hgcd (by omega) hCv0 hvk0 hV0lt hyaeq
    have hHeq : h * ((v % a + k - 1) / k) = u' + (v / a) * d + 1 := by omega
    have hVpos : 1 ≤ v % a := by
      by_contra hcon
      push Not at hcon
      have h0 : v % a = 0 := by omega
      rw [h0, tri_ceil_zero k hk1] at hHeq
      simp only [mul_zero] at hHeq
      omega
    -- Non-carry upper bounds from adding generators.
    have hkey : ∀ j : ℕ, j ≤ k → v % a + j < a →
        h * (((v % a + j) + k - 1) / k) ≤ u' + (v / a) * d + h := by
      intro j hjj hlt
      have hGjS := hGjmem j hjj
      have hGj0 := hGjpos j hjj
      have hyjS : y + (if j = 0 then a else h * a + j * d) ∈ S :=
        hyadd _ hGjS (by omega)
      have hval : y + (if j = 0 then a else h * a + j * d)
          = (u' + (v / a) * d + (if j = 0 then 1 else h)) * a
            + (v % a + j) * d := by
        by_cases hj0 : j = 0
        · simp only [hj0, ite_true]
          rw [hyred]
          ring
        · simp only [hj0, ite_false]
          rw [hyred]
          ring
      rw [hS] at hyjS
      obtain ⟨cc, hccsup, hcceq⟩ := hyjS
      obtain ⟨uu, vv, CC, huveq, hCCu, hCCv, hvvk⟩ :=
        S_obtain a d h k _ cc hccsup hcceq
      have heq2 : (u' + (v / a) * d + (if j = 0 then 1 else h)) * a
          + (v % a + j) * d = uu * a + vv * d := hval.symm.trans huveq
      have hle2 := S_mod_bound a d h k _ _ _ _ _ ha hk hgcd
        hCCu hCCv hvvk hlt heq2
      have hhle : (if j = 0 then 1 else h) ≤ h := by
        by_cases hj0 : j = 0
        · simp only [hj0, ite_true]
          omega
        · simp [hj0]
      omega
    -- Hence V + k ≥ a.
    have hVka : v % a + k ≥ a := by
      by_contra hcon
      push Not at hcon
      have hub := hkey k (le_refl k) (by omega)
      have hAlow : (v % a + k - 1) / k + 1 ≤ ((v % a + k) + k - 1) / k := by
        rw [Nat.le_div_iff_mul_le hk]
        have e1 : ((v % a + k - 1) / k) * k ≤ v % a + k - 1 :=
          Nat.div_mul_le_self _ _
        have e2 : (((v % a + k - 1) / k) + 1) * k
            = ((v % a + k - 1) / k) * k + k := by ring
        omega
      have hmul := Nat.mul_le_mul_left h hAlow
      have hexpand : h * ((v % a + k - 1) / k + 1)
          = h * ((v % a + k - 1) / k) + h := by ring
      omega
    -- Take j₀ = a - 1 - V to bound the ceiling from below by q + 1.
    have hVle : v % a ≤ a - 1 := by omega
    set j0 := a - 1 - v % a with hj0
    have hj0k : j0 ≤ k := by omega
    have hj0eq : v % a + j0 = a - 1 := by omega
    have hj0lt : v % a + j0 < a := by omega
    have hub2 := hkey j0 hj0k hj0lt
    rw [hj0eq, hqr] at hub2
    have hexact : ((q * k + r) + k - 1) / k = q + 1 := by
      apply Nat.div_eq_of_lt_le
      · have e : (q + 1) * k = q * k + k := by ring
        omega
      · have e : (q + 1 + 1) * k = q * k + k + k := by ring
        omega
    rw [hexact] at hub2
    have hqW : q + 1 ≤ (v % a + k - 1) / k := by
      by_contra hcon
      push Not at hcon
      have hWq : h * ((v % a + k - 1) / k) ≤ h * q :=
        Nat.mul_le_mul_left h (by omega)
      have hexpand : h * (q + 1) = h * q + h := by ring
      omega
    have hVlo : q * k + 1 ≤ v % a := by
      have h10 : (q + 1) * k ≤ v % a + k - 1 :=
        (Nat.le_div_iff_mul_le hk).mp hqW
      have e : (q + 1) * k = q * k + k := by ring
      omega
    have hVhi : v % a ≤ q * k + r := by omega
    have hWe : (v % a + k - 1) / k = q + 1 :=
      tri_div_add _ _ _ _ hk hr1 hrk hVlo hVhi
    rw [hWe] at hHeq
    refine ⟨v % a, by omega, by omega, ?_⟩
    have hdivq : (v % a - 1) / k = q := tri_div_sub _ _ _ _ hk hr1 hrk hVlo hVhi
    have e2 : u' + (v / a) * d + 1 = h * (q + 1) := hHeq.symm
    have hplus : y + a
        = (h * a * q + (h - 1) * a + d * (v % a)) + a := by
      have e1 : y + a = (u' + (v / a) * d + 1) * a + (v % a) * d := by
        rw [hyred]
        ring
      have e3 : (h * a * q + (h - 1) * a + d * (v % a)) + a
          = (h * (q + 1)) * a + (v % a) * d := by
        have hsub : (h - 1) * a + a = h * a := by
          have hh1 : h - 1 + 1 = h := Nat.sub_add_cancel (by omega)
          calc (h - 1) * a + a = ((h - 1) + 1) * a := by rw [add_mul, one_mul]
          _ = h * a := by rw [hh1]
        have e4 : h * a * q + h * a = h * (q + 1) * a := by ring
        have e5 : d * (v % a) = (v % a) * d := mul_comm _ _
        omega
      rw [e2] at e1
      rw [e1]
      exact e3.symm
    have hfin : y = h * a * q + (h - 1) * a + d * (v % a) :=
      add_right_cancel hplus
    rw [hdivq]
    exact hfin
  · -- Backward: every number of the required form is pseudo-Frobenius.
    rintro ⟨x, hlo, hhi, rfl⟩
    have hx1 : 1 ≤ x := by omega
    have hxa : x < a := by omega
    have hxlo : q * k + 1 ≤ x := by omega
    have hxhi : x ≤ q * k + r := by omega
    have hdivq : (x - 1) / k = q := tri_div_sub x k q r hk hr1 hrk hxlo hxhi
    have hdivq1 : (x + k - 1) / k = q + 1 :=
      tri_div_add x k q r hk hr1 hrk hxlo hxhi
    have ehq : h * q * a = h * a * q := by ring
    have hyUV : h * a * ((x - 1) / k) + (h - 1) * a + d * x
        = (h * q + (h - 1)) * a + x * d := by
      rw [hdivq, add_mul, ehq, mul_comm x d]
    -- Adding any generator stays in S.
    have H1 : ∀ j : ℕ, j ≤ k →
        (h * a * ((x - 1) / k) + (h - 1) * a + d * x)
          + (if j = 0 then a else h * a + j * d) ∈ S := by
      intro j hjj
      by_cases hj0 : j = 0
      · subst hj0
        simp only [ite_true]
        have hya : (h * a * ((x - 1) / k) + (h - 1) * a + d * x) + a
            = (h * q + (h - 1) + 1) * a + x * d := by
          rw [hyUV]
          simp only [add_mul, one_mul]
          ac_rfl
        rw [hS, hya]
        exact S_ceil_intro a d h k _ _ hk1 (by
          rw [hdivq1]
          have e : h * (q + 1) = h * q + h := by ring
          omega)
      · simp only [hj0, ite_false]
        have hval : (h * a * ((x - 1) / k) + (h - 1) * a + d * x)
            + (h * a + j * d)
            = ((h * q + (h - 1)) + h) * a + (x + j) * d := by
          rw [hyUV]
          simp only [add_mul]
          ac_rfl
        have hred := S_reduce a d ((h * q + (h - 1)) + h) (x + j)
        have hV2lt : (x + j) % a < a := Nat.mod_lt _ ha
        have hleV : ((x + j) % a + k - 1) / k ≤ q + 1 :=
          tri_div_le _ _ _ _ hk hrk (by omega)
        have hmem : ((h * q + (h - 1)) + h + ((x + j) / a) * d) * a
            + ((x + j) % a) * d ∈ { n | ∃ c : ℕ → ℕ, (∀ i, k < i → c i = 0) ∧
              n = ∑ i ∈ Finset.range (k + 1),
                c i * (if i = 0 then a else h * a + i * d) } :=
          S_ceil_intro a d h k _ _ hk1 (by
            have hmul := Nat.mul_le_mul_left h hleV
            have e : h * (q + 1) = h * q + h := by ring
            omega)
        rw [hS]
        have hyj : (h * a * ((x - 1) / k) + (h - 1) * a + d * x)
            + (h * a + j * d)
            = ((h * q + (h - 1)) + h + ((x + j) / a) * d) * a
              + ((x + j) % a) * d := hval.trans hred.symm
        rw [hyj]
        exact hmem
    -- Lifting to arbitrary nonzero s ∈ S.
    have H2 : ∀ s : ℕ, s ∈ S → s ≠ 0 →
        (h * a * ((x - 1) / k) + (h - 1) * a + d * x) + s ∈ S := by
      intro s hsS hsne
      rw [hS] at hsS
      obtain ⟨c, hcsup, hceq⟩ := hsS
      have hex : ∃ j : ℕ, j ≤ k ∧ 0 < c j := by
        by_contra hcon
        push Not at hcon
        apply hsne
        rw [hceq]
        apply Finset.sum_eq_zero
        intro i hi
        have hi2 : i ≤ k := by
          have hmem := Finset.mem_range.mp hi
          omega
        have hci : c i = 0 := by
          have h := hcon i hi2
          omega
        rw [hci, zero_mul]
      obtain ⟨j, hjj, hcj⟩ := hex
      have hGjS := H1 j hjj
      have hGjle : (if j = 0 then a else h * a + j * d) ≤ s := by
        have hmemj : j ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
        have h1 : 1 * (if j = 0 then a else h * a + j * d)
            ≤ c j * (if j = 0 then a else h * a + j * d) :=
          Nat.mul_le_mul (by omega) (le_refl _)
        have h2 : c j * (if j = 0 then a else h * a + j * d)
            ≤ ∑ i ∈ Finset.range (k + 1),
              c i * (if i = 0 then a else h * a + i * d) := by
          apply Finset.single_le_sum _ hmemj
          intro i _
          exact Nat.zero_le _
        rw [one_mul] at h1
        omega
      have hGj_sum : (if j = 0 then a else h * a + j * d)
          = ∑ i ∈ Finset.range (k + 1),
            (if i = j then (if i = 0 then a else h * a + i * d) else 0) := by
        rw [Finset.sum_ite_eq' _ j _]
        have hmemj : j ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
        simp [hmemj]
      have hper : ∀ i ∈ Finset.range (k + 1),
          (if i = j then c i - 1 else c i) * (if i = 0 then a else h * a + i * d)
          + (if i = j then (if i = 0 then a else h * a + i * d) else 0)
          = c i * (if i = 0 then a else h * a + i * d) := by
        intro i _
        by_cases hij : i = j
        · simp only [hij, ite_true]
          have e : (c j - 1) * (if j = 0 then a else h * a + j * d)
              + (if j = 0 then a else h * a + j * d)
              = c j * (if j = 0 then a else h * a + j * d) := by
            have e1 : (c j - 1) * (if j = 0 then a else h * a + j * d)
                + (if j = 0 then a else h * a + j * d)
                = ((c j - 1) + 1) * (if j = 0 then a else h * a + j * d) := by
              rw [add_mul, one_mul]
            rw [e1, Nat.sub_add_cancel (by omega)]
          exact e
        · simp [hij]
      have hsum : (∑ i ∈ Finset.range (k + 1),
            (if i = j then c i - 1 else c i)
              * (if i = 0 then a else h * a + i * d))
          + (if j = 0 then a else h * a + j * d)
          = ∑ i ∈ Finset.range (k + 1),
            c i * (if i = 0 then a else h * a + i * d) := by
        rw [hGj_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl hper
      have hcsup' : ∀ i : ℕ, k < i →
          (if i = j then c i - 1 else c i) = 0 := by
        intro i hi
        have hne : i ≠ j := by omega
        simp only [hne, ite_false]
        exact hcsup i hi
      have hrest : s - (if j = 0 then a else h * a + j * d) ∈ S := by
        rw [hS]
        refine ⟨fun i => if i = j then c i - 1 else c i, hcsup', ?_⟩
        have h2 : s = (∑ i ∈ Finset.range (k + 1),
            (if i = j then c i - 1 else c i)
              * (if i = 0 then a else h * a + i * d))
            + (if j = 0 then a else h * a + j * d) := by
          rw [hsum]
          exact hceq
        rw [h2, Nat.add_sub_cancel]
      have hfin : (h * a * ((x - 1) / k) + (h - 1) * a + d * x) + s
          = ((h * a * ((x - 1) / k) + (h - 1) * a + d * x)
            + (if j = 0 then a else h * a + j * d))
          + (s - (if j = 0 then a else h * a + j * d)) := by
        omega
      rw [hfin]
      exact S_add_mem S a d h k _ _ hGjS hrest hS
    constructor
    · intro hyS
      rw [hS] at hyS
      obtain ⟨c, hcsup, hceq⟩ := hyS
      obtain ⟨u, v, C, hueq, hCu, hCv, hvk⟩ := S_obtain _ _ _ _ _ c hcsup hceq
      have heq2 : (h * q + (h - 1)) * a + x * d = u * a + v * d := by
        rw [← hyUV]
        exact hueq
      have hle2 := S_mod_bound a d h k _ _ _ _ _ ha hk hgcd
        hCu hCv hvk hxa heq2
      rw [hdivq1] at hle2
      have hexpand : h * (q + 1) = h * q + h := by ring
      omega
    · intro s hsS hsne
      exact H2 s hsS hsne

set_option linter.unusedVariables false in
/--
**Tripathi's pseudo-Frobenius formula.** Let $a$, $d$, $h$ and $k$ be positive integers with
$\gcd(a, d) = 1$, and let $q$ and $r$ be natural numbers with $1 \le r \le k$ and
$a - 1 = qk + r$. Let $S$ be the set of all sums $c_0 a + \sum_{i=1}^{k} c_i (ha + id)$ with
natural numbers $c_0, \dots, c_k$, that is, the additive monoid generated by
$a, ha + d, \dots, ha + kd$. Then the natural numbers $y \notin S$ such that $y + s \in S$ for
every nonzero $s \in S$ are exactly the numbers
$$y = ha \left\lfloor \frac{x - 1}{k} \right\rfloor + (h - 1)a + dx$$
with $x$ a natural number satisfying $a - r \le x \le a - 1$.

The case $a = 1$ cannot occur, since then $a - 1 = qk + r$ with $r \ge 1$ is impossible. When
$k \ge a$, these numbers are exactly $(h - 1)a + dx$ for $1 \le x \le a - 1$.

Source: Amitabha Tripathi, "The Frobenius Problem for Modified Arithmetic
Progressions," Journal of Integer Sequences 16 (2013), Article 13.7.4,
Theorem (label S*formula), lines 235–238,
https://cs.uwaterloo.ca/journals/JIS/VOL16/Tripathi/trip22.tex
It follows from `tripathi_pseudo_frobenius_arithmetic_progression_general`;
the hypothesis `hd` is unused and keeps the source's shape.
Proves `Wanted` entry `tripathi_pseudo_frobenius_arithmetic_progression`.
-/
theorem tripathi_pseudo_frobenius_arithmetic_progression
    (a d h k : ℕ) (ha : 0 < a) (hd : 0 < d) (hh : 0 < h) (hk : 0 < k)
    (hgcd : Nat.gcd a d = 1) (q r : ℕ) (hr1 : 1 ≤ r) (hrk : r ≤ k)
    (hqr : a - 1 = q * k + r)
    (S : Set ℕ)
    (hS : S = { n | ∃ c : ℕ → ℕ, (∀ i, k < i → c i = 0) ∧
      n = ∑ i ∈ Finset.range (k + 1),
        c i * (if i = 0 then a else h * a + i * d) }) :
    { x | x ∉ S ∧ ∀ s ∈ S, s ≠ 0 → x + s ∈ S } =
      { y | ∃ x : ℕ, a - r ≤ x ∧ x ≤ a - 1 ∧
        y = h * a * ((x - 1) / k) + (h - 1) * a + d * x } :=
  tripathi_pseudo_frobenius_arithmetic_progression_general a d h k ha hh hk hgcd q r hr1 hrk hqr
    S hS

end

end MetaMathlibExt
