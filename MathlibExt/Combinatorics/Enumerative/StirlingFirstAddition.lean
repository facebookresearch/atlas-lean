/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Nat.SuccPred
import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators

namespace MetaMathlibExt

private theorem inner_zero_all (u v K : ℕ) :
    (∑ i ∈ Finset.range (v + 1),
      v.choose i * u.ascFactorial i * Nat.stirlingFirst (v - i) 0 *
        (if (0:ℕ) ≤ K then Nat.stirlingFirst u (K - 0) else 0))
    = u.ascFactorial v * (if (0:ℕ) ≤ K then Nat.stirlingFirst u K else 0) := by
  rw [Finset.sum_eq_single v]
  · simp
  · intro i hi hiv
    have hi_le : i ≤ v := by
      have := Finset.mem_range.mp hi; omega
    have hlt : i < v := by omega
    have hpos : 0 < v - i := by omega
    obtain ⟨m, hm⟩ : ∃ m, v - i = m + 1 := ⟨v - i - 1, by omega⟩
    rw [hm, Nat.stirlingFirst_succ_zero]
    simp
  · intro habs
    simp at habs

private theorem Gtop_aux (u v k : ℕ) :
    (∑ i ∈ Finset.range (v + 1), v.choose i * u.ascFactorial i *
        Nat.stirlingFirst (v - i) (v + 1) *
        (if v + 1 ≤ k + 1 then Nat.stirlingFirst u (k + 1 - (v + 1)) else 0)) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hlt : v - i < v + 1 := by
    have hi_le : i ≤ v := by
      have := Finset.mem_range.mp hi; omega
    omega
  rw [Nat.stirlingFirst_eq_zero_of_lt hlt]
  simp

private theorem asc_succ_aux (u v : ℕ) : u.ascFactorial (v + 1) = (u + v) * u.ascFactorial v := by
  have := Nat.ascFactorial_succ (n := u) (k := v)
  simpa [Nat.add_comm] using this

private theorem VQ_aux (u v j1 : ℕ) :
    (∑ i ∈ Finset.range (v + 1), v.choose i * (v - i) * u.ascFactorial i *
        Nat.stirlingFirst (v - i) j1)
      + (∑ i ∈ Finset.range (v + 1), v.choose i * i * u.ascFactorial i *
        Nat.stirlingFirst (v - i) j1)
    = v * (∑ i ∈ Finset.range (v + 1), v.choose i * u.ascFactorial i *
        Nat.stirlingFirst (v - i) j1) := by
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ v := by
    have := Finset.mem_range.mp hi; omega
  have h : (v - i) + i = v := Nat.sub_add_cancel hi_le
  have h2 : v.choose i * (v - i) + v.choose i * i = v.choose i * v := by
    rw [← Nat.mul_add, h]
  calc v.choose i * (v - i) * u.ascFactorial i * Nat.stirlingFirst (v - i) j1
        + v.choose i * i * u.ascFactorial i * Nat.stirlingFirst (v - i) j1
      = (v.choose i * (v - i) + v.choose i * i) *
          (u.ascFactorial i * Nat.stirlingFirst (v - i) j1) := by ring
    _ = v.choose i * v * (u.ascFactorial i * Nat.stirlingFirst (v - i) j1) := by rw [h2]
    _ = v * (v.choose i * u.ascFactorial i * Nat.stirlingFirst (v - i) j1) := by ring

private theorem Sb_aux (u v j1 : ℕ) :
    (∑ i ∈ Finset.range (v + 1), v.choose i * u.ascFactorial (i + 1) *
        Nat.stirlingFirst (v - i) j1)
    = u * (∑ i ∈ Finset.range (v + 1), v.choose i * u.ascFactorial i *
        Nat.stirlingFirst (v - i) j1)
      + (∑ i ∈ Finset.range (v + 1), v.choose i * i * u.ascFactorial i *
        Nat.stirlingFirst (v - i) j1) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hasc : u.ascFactorial (i + 1) = (u + i) * u.ascFactorial i :=
    Nat.ascFactorial_succ
  rw [hasc]
  ring

private theorem Sa_reindex_aux (u v j1 : ℕ) :
    Nat.stirlingFirst (v + 1) j1
      + (∑ i ∈ Finset.range (v + 1), v.choose (i + 1) * u.ascFactorial (i + 1) *
        Nat.stirlingFirst (v - i) j1)
    = (∑ i' ∈ Finset.range (v + 1), v.choose i' * u.ascFactorial i' *
        Nat.stirlingFirst (v - i' + 1) j1) := by
  have hdrop : (∑ i ∈ Finset.range (v + 1), v.choose (i + 1) * u.ascFactorial (i + 1) *
        Nat.stirlingFirst (v - i) j1)
      = (∑ i ∈ Finset.range v, v.choose (i + 1) * u.ascFactorial (i + 1) *
        Nat.stirlingFirst (v - i) j1) := by
    cases v with
    | zero => simp
    | succ v =>
      rw [Finset.sum_range_succ]
      simp [Nat.choose_succ_self]
  rw [hdrop]
  rw [Finset.sum_range_succ' (fun i' => v.choose i' * u.ascFactorial i' *
    Nat.stirlingFirst (v - i' + 1) j1) v]
  simp only [Nat.choose_zero_right, Nat.ascFactorial_zero, Nat.one_mul]
  have h0 : v - 0 + 1 = v + 1 := by omega
  rw [h0, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi_lt : i < v := Finset.mem_range.mp hi
  have h1 : v - (i + 1) + 1 = v - i := by omega
  rw [h1]

private theorem expand_mid_aux (u v j' : ℕ) :
    (∑ i ∈ Finset.range (v + 1), v.choose i * u.ascFactorial i *
        Nat.stirlingFirst (v - i + 1) (j' + 1))
    = (∑ i ∈ Finset.range (v + 1), v.choose i * (v - i) * u.ascFactorial i *
        Nat.stirlingFirst (v - i) (j' + 1))
      + (∑ i ∈ Finset.range (v + 1), v.choose i * u.ascFactorial i *
        Nat.stirlingFirst (v - i) j') := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.stirlingFirst_succ_succ (v - i) j']
  ring

private theorem core_aux (u v j' : ℕ) :
    (∑ i ∈ Finset.range (v + 1 + 1), (v + 1).choose i * u.ascFactorial i *
        Nat.stirlingFirst (v + 1 - i) (j' + 1))
    = (u + v) * (∑ i ∈ Finset.range (v + 1), v.choose i * u.ascFactorial i *
        Nat.stirlingFirst (v - i) (j' + 1))
      + (∑ i ∈ Finset.range (v + 1), v.choose i * u.ascFactorial i *
        Nat.stirlingFirst (v - i) j') := by
  have peel : (∑ i ∈ Finset.range (v + 1 + 1), (v + 1).choose i * u.ascFactorial i *
        Nat.stirlingFirst (v + 1 - i) (j' + 1))
      = Nat.stirlingFirst (v + 1) (j' + 1)
        + (∑ i ∈ Finset.range (v + 1), (v + 1).choose (i + 1) * u.ascFactorial (i + 1) *
          Nat.stirlingFirst (v + 1 - (i + 1)) (j' + 1)) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, Nat.ascFactorial_zero, Nat.one_mul, Nat.sub_zero]
    exact add_comm _ _
  have shift : (∑ i ∈ Finset.range (v + 1), (v + 1).choose (i + 1) * u.ascFactorial (i + 1) *
          Nat.stirlingFirst (v + 1 - (i + 1)) (j' + 1))
      = (∑ i ∈ Finset.range (v + 1), (v.choose i + v.choose (i + 1)) *
          u.ascFactorial (i + 1) * Nat.stirlingFirst (v - i) (j' + 1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hpascal : (v + 1).choose (i + 1) = v.choose i + v.choose (i + 1) :=
      Nat.choose_succ_succ v i
    have hsub : v + 1 - (i + 1) = v - i := by
      have hle : i ≤ v := by
        have := Finset.mem_range.mp hi; omega
      omega
    rw [hpascal, hsub]
  have split : (∑ i ∈ Finset.range (v + 1), (v.choose i + v.choose (i + 1)) *
        u.ascFactorial (i + 1) * Nat.stirlingFirst (v - i) (j' + 1))
      = (∑ i ∈ Finset.range (v + 1), v.choose i * u.ascFactorial (i + 1) *
          Nat.stirlingFirst (v - i) (j' + 1))
        + (∑ i ∈ Finset.range (v + 1), v.choose (i + 1) * u.ascFactorial (i + 1) *
          Nat.stirlingFirst (v - i) (j' + 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hSb := Sb_aux u v (j' + 1)
  have hSa := Sa_reindex_aux u v (j' + 1)
  have hExp := expand_mid_aux u v j'
  have hVQ := VQ_aux u v (j' + 1)
  rw [peel, shift, split]
  have e1 : Nat.stirlingFirst (v + 1) (j' + 1)
        + ((∑ i ∈ Finset.range (v + 1), v.choose i * u.ascFactorial (i + 1) *
          Nat.stirlingFirst (v - i) (j' + 1))
        + (∑ i ∈ Finset.range (v + 1), v.choose (i + 1) * u.ascFactorial (i + 1) *
          Nat.stirlingFirst (v - i) (j' + 1)))
      = (Nat.stirlingFirst (v + 1) (j' + 1)
        + (∑ i ∈ Finset.range (v + 1), v.choose (i + 1) * u.ascFactorial (i + 1) *
          Nat.stirlingFirst (v - i) (j' + 1)))
        + (∑ i ∈ Finset.range (v + 1), v.choose i * u.ascFactorial (i + 1) *
          Nat.stirlingFirst (v - i) (j' + 1)) := by ring
  rw [e1, hSa, hExp, hSb]
  have hfin : ((∑ i ∈ Finset.range (v + 1), v.choose i * (v - i) * u.ascFactorial i *
          Nat.stirlingFirst (v - i) (j' + 1))
        + (∑ i ∈ Finset.range (v + 1), v.choose i * u.ascFactorial i *
          Nat.stirlingFirst (v - i) j'))
        + (u * (∑ i ∈ Finset.range (v + 1), v.choose i * u.ascFactorial i *
          Nat.stirlingFirst (v - i) (j' + 1))
        + (∑ i ∈ Finset.range (v + 1), v.choose i * i * u.ascFactorial i *
          Nat.stirlingFirst (v - i) (j' + 1)))
      = (u + v) * (∑ i ∈ Finset.range (v + 1), v.choose i * u.ascFactorial i *
          Nat.stirlingFirst (v - i) (j' + 1))
        + (∑ i ∈ Finset.range (v + 1), v.choose i * u.ascFactorial i *
          Nat.stirlingFirst (v - i) j') := by
    have h4 : ((∑ i ∈ Finset.range (v + 1), v.choose i * (v - i) * u.ascFactorial i *
            Nat.stirlingFirst (v - i) (j' + 1))
          + (∑ i ∈ Finset.range (v + 1), v.choose i * u.ascFactorial i *
            Nat.stirlingFirst (v - i) j'))
          + (u * (∑ i ∈ Finset.range (v + 1), v.choose i * u.ascFactorial i *
            Nat.stirlingFirst (v - i) (j' + 1))
          + (∑ i ∈ Finset.range (v + 1), v.choose i * i * u.ascFactorial i *
            Nat.stirlingFirst (v - i) (j' + 1)))
        = (u * (∑ i ∈ Finset.range (v + 1), v.choose i * u.ascFactorial i *
            Nat.stirlingFirst (v - i) (j' + 1))
          + ((∑ i ∈ Finset.range (v + 1), v.choose i * (v - i) * u.ascFactorial i *
            Nat.stirlingFirst (v - i) (j' + 1))
          + (∑ i ∈ Finset.range (v + 1), v.choose i * i * u.ascFactorial i *
            Nat.stirlingFirst (v - i) (j' + 1))))
          + (∑ i ∈ Finset.range (v + 1), v.choose i * u.ascFactorial i *
            Nat.stirlingFirst (v - i) j') := by ring
    rw [h4, hVQ]
    ring
  exact hfin

private theorem e_rel_aux (u k j' : ℕ) :
    (if j' + 1 ≤ k + 1 then Nat.stirlingFirst u (k + 1 - (j' + 1)) else 0)
    = (if j' ≤ k then Nat.stirlingFirst u (k - j') else 0) := by
  by_cases h : j' ≤ k
  · have h1 : j' + 1 ≤ k + 1 := by omega
    have h2 : k + 1 - (j' + 1) = k - j' := by omega
    simp [h1, h, h2]
  · have h1 : ¬ j' + 1 ≤ k + 1 := by omega
    simp [h1, h]

private theorem inner_succ_aux (u v k j' : ℕ) :
    (∑ i ∈ Finset.range (v + 1 + 1), (v + 1).choose i * u.ascFactorial i *
        Nat.stirlingFirst (v + 1 - i) (j' + 1) *
        (if j' + 1 ≤ k + 1 then Nat.stirlingFirst u (k + 1 - (j' + 1)) else 0))
    = (u + v) * (∑ i ∈ Finset.range (v + 1), v.choose i * u.ascFactorial i *
        Nat.stirlingFirst (v - i) (j' + 1) *
        (if j' + 1 ≤ k + 1 then Nat.stirlingFirst u (k + 1 - (j' + 1)) else 0))
      + (∑ i ∈ Finset.range (v + 1), v.choose i * u.ascFactorial i *
        Nat.stirlingFirst (v - i) j' *
        (if j' ≤ k then Nat.stirlingFirst u (k - j') else 0)) := by
  have he := e_rel_aux u k j'
  have hcore := core_aux u v j'
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, he, hcore]
  ring

private theorem base_aux (u k : ℕ) :
    (∑ j ∈ Finset.range (0 + 1), ∑ i ∈ Finset.range (0 + 1),
      (0:ℕ).choose i * u.ascFactorial i * Nat.stirlingFirst (0 - i) j *
        (if j ≤ k then Nat.stirlingFirst u (k - j) else 0))
    = Nat.stirlingFirst u k := by
  simp

private theorem succ_zero_aux (u v : ℕ) :
    (∑ j ∈ Finset.range (v + 1 + 1), ∑ i ∈ Finset.range (v + 1 + 1),
      (v + 1).choose i * u.ascFactorial i * Nat.stirlingFirst (v + 1 - i) j *
        (if j ≤ 0 then Nat.stirlingFirst u (0 - j) else 0)) = 0 := by
  have outer : ∀ j ∈ Finset.range (v + 1 + 1),
      (∑ i ∈ Finset.range (v + 1 + 1),
        (v + 1).choose i * u.ascFactorial i * Nat.stirlingFirst (v + 1 - i) j *
          (if j ≤ 0 then Nat.stirlingFirst u (0 - j) else 0))
      = if j = 0 then u.ascFactorial (v + 1) * Nat.stirlingFirst u 0 else 0 := by
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      simp only [Nat.le_refl, ↓reduceIte, Nat.sub_zero]
      rw [Finset.sum_eq_single (v + 1)]
      · simp
      · intro i hi hii
        have hi_le : i ≤ v + 1 := by
          have := Finset.mem_range.mp hi; omega
        have hpos : 0 < v + 1 - i := by omega
        obtain ⟨m, hm⟩ : ∃ m, v + 1 - i = m + 1 := ⟨v - i, by omega⟩
        rw [hm, Nat.stirlingFirst_succ_zero]
        simp
      · simp
    · have hfact : (if j ≤ 0 then Nat.stirlingFirst u (0 - j) else 0) = 0 := by
        simp [hj0]
      simp only [hfact, mul_zero, Finset.sum_const_zero, hj0, ↓reduceIte]
  rw [Finset.sum_congr rfl outer]
  simp only [Finset.sum_ite_eq' _ _ (fun _ => u.ascFactorial (v + 1) * Nat.stirlingFirst u 0)]
  simp only [Finset.mem_range]
  cases u with
  | zero => simp [Nat.zero_ascFactorial]
  | succ u => simp

private theorem step_aux (u v k : ℕ) :
    (∑ j ∈ Finset.range (v + 1 + 1), ∑ i ∈ Finset.range (v + 1 + 1),
      (v + 1).choose i * u.ascFactorial i * Nat.stirlingFirst (v + 1 - i) j *
        (if j ≤ k + 1 then Nat.stirlingFirst u (k + 1 - j) else 0))
    = (u + v) * (∑ j ∈ Finset.range (v + 1), ∑ i ∈ Finset.range (v + 1),
      v.choose i * u.ascFactorial i * Nat.stirlingFirst (v - i) j *
        (if j ≤ k + 1 then Nat.stirlingFirst u (k + 1 - j) else 0))
      + (∑ j ∈ Finset.range (v + 1), ∑ i ∈ Finset.range (v + 1),
      v.choose i * u.ascFactorial i * Nat.stirlingFirst (v - i) j *
        (if j ≤ k then Nat.stirlingFirst u (k - j) else 0)) := by
  set F : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (v + 1 + 1),
    (v + 1).choose i * u.ascFactorial i * Nat.stirlingFirst (v + 1 - i) j *
      (if j ≤ k + 1 then Nat.stirlingFirst u (k + 1 - j) else 0) with hF
  set G : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (v + 1),
    v.choose i * u.ascFactorial i * Nat.stirlingFirst (v - i) j *
      (if j ≤ k + 1 then Nat.stirlingFirst u (k + 1 - j) else 0) with hG
  set H : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (v + 1),
    v.choose i * u.ascFactorial i * Nat.stirlingFirst (v - i) j *
      (if j ≤ k then Nat.stirlingFirst u (k - j) else 0) with hH
  have hR : (∑ j ∈ Finset.range (v + 1 + 1), F j)
      = F 0 + ∑ j' ∈ Finset.range (v + 1), F (j' + 1) := by
    rw [Finset.sum_range_succ']
    exact add_comm _ _
  have hFshift : (∑ j' ∈ Finset.range (v + 1), F (j' + 1))
      = (u + v) * (∑ j' ∈ Finset.range (v + 1), G (j' + 1))
        + (∑ j' ∈ Finset.range (v + 1), H j') := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j' hj'
    have h := inner_succ_aux u v k j'
    simpa [hF, hG, hH] using h
  have hS1 : (∑ j ∈ Finset.range (v + 1 + 1), G j)
      = (∑ j ∈ Finset.range (v + 1), G j) + G (v + 1) := Finset.sum_range_succ _ _
  have hS2 : (∑ j ∈ Finset.range (v + 1 + 1), G j)
      = G 0 + ∑ j' ∈ Finset.range (v + 1), G (j' + 1) := by
    rw [Finset.sum_range_succ']
    exact add_comm _ _
  have hGtop : G (v + 1) = 0 := by
    have := Gtop_aux u v k
    simpa [hG] using this
  have hF0 : F 0 = (u + v) * G 0 := by
    have hF0' := inner_zero_all u (v + 1) (k + 1)
    have hG0' := inner_zero_all u v (k + 1)
    have hasc := asc_succ_aux u v
    simp only [Nat.zero_le, ↓reduceIte, Nat.sub_zero] at hF0' hG0'
    simp only [hF, hG, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
    rw [hF0', hG0', hasc]
    ring
  have hLHS : (∑ j ∈ Finset.range (v + 1 + 1), F j)
      = (u + v) * (∑ j ∈ Finset.range (v + 1), G j)
        + (∑ j' ∈ Finset.range (v + 1), H j') := by
    rw [hR, hFshift, hF0]
    have hSG : G 0 + ∑ j' ∈ Finset.range (v + 1), G (j' + 1)
        = (∑ j ∈ Finset.range (v + 1), G j) + G (v + 1) := by
      rw [← hS1, ← hS2]
    rw [hGtop] at hSG
    simp only [add_zero] at hSG
    have hmix : (u + v) * G 0 + ((u + v) * (∑ j' ∈ Finset.range (v + 1), G (j' + 1))
        + (∑ j' ∈ Finset.range (v + 1), H j'))
        = (u + v) * (G 0 + ∑ j' ∈ Finset.range (v + 1), G (j' + 1))
        + (∑ j' ∈ Finset.range (v + 1), H j') := by ring
    rw [hmix, hSG]
  simpa [hF, hG, hH] using hLHS

/-! # Addition formula for Stirling numbers of the first kind
-/

/--
**Addition formula for Stirling numbers of the first kind.** Write $c(n,k)$ for the unsigned
Stirling numbers of the first kind and $u^{\overline{i}} = u(u+1)\cdots(u+i-1)$ for the rising
factorial. For all natural numbers $u$, $v$ and $k$,
$$c(u+v,k) = \sum_{j=0}^{v} \sum_{i=0}^{v} \binom{v}{i}\, u^{\overline{i}}\, c(v-i,j)\, c(u,k-j),$$
where a term with $j > k$ is read as $0$.

Source: Grzegorz Rządkowski, "Two Formulas for Successive Derivatives
and Their Applications," Journal of Integer Sequences 12 (2009),
Article 09.8.2, Theorem, equation (ex44), lines 257–263,
https://cs.uwaterloo.ca/journals/JIS/VOL12/Rzadkowski/rzadkowski3.tex
-/
theorem stirlingFirst_addition (u v k : ℕ) :
    Nat.stirlingFirst (u + v) k =
      ∑ j ∈ Finset.range (v + 1), ∑ i ∈ Finset.range (v + 1),
        v.choose i * u.ascFactorial i * Nat.stirlingFirst (v - i) j *
          (if j ≤ k then Nat.stirlingFirst u (k - j) else 0) := by
  induction v generalizing k with
  | zero =>
    rw [Nat.add_zero]
    exact (base_aux u k).symm
  | succ v ih =>
    cases k with
    | zero =>
      have hL : Nat.stirlingFirst (u + (v + 1)) 0 = 0 := by
        have hpos : 0 < u + (v + 1) := by omega
        obtain ⟨m, hm⟩ : ∃ m, u + (v + 1) = m + 1 := ⟨u + v, by omega⟩
        rw [hm, Nat.stirlingFirst_succ_zero]
      have hR := succ_zero_aux u v
      rw [hL]
      exact hR.symm
    | succ k =>
      have hstep := step_aux u v k
      have ih1 := ih (k + 1)
      have ih2 := ih k
      have hUv : u + (v + 1) = (u + v) + 1 := by omega
      have hLHS : Nat.stirlingFirst (u + (v + 1)) (k + 1)
          = (u + v) * Nat.stirlingFirst (u + v) (k + 1)
            + Nat.stirlingFirst (u + v) k := by
        rw [hUv]
        exact Nat.stirlingFirst_succ_succ (u + v) k
      rw [hLHS, hstep, ih1, ih2]

end MetaMathlibExt
