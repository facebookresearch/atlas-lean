/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SpoofLehmerFactorization
import MathlibExt.NumberTheory.NielsenBound
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Bound on unitary Lehmer factorizations

The spoof evaluation of a unitary spoof `k`-Lehmer factorization on `r` bases is at most
`2 ^ 2 ^ r - 2 ^ 2 ^ (r - 1)` (`spoofEval_le_of_isSpoofLehmer_spoofOfBases`).

Source: Elchin Hasanalizade, *Some Remarks on a Paper of Molnar and Singh*, INTEGERS 26 (2026),
Article A100, Theorem 1.
-/

namespace MetaMathlibExt

-- Card, evaluation and totient of the exponent-one factorization on a multiset of bases.
private theorem card_spoofOfBases (x : Multiset ℕ) :
    Multiset.card (spoofOfBases x) = Multiset.card x := by
  simp only [spoofOfBases, Multiset.card_map]

private theorem eval_spoofOfBases (x : Multiset ℕ) :
    spoofEval (spoofOfBases x) = (x.map fun a : ℕ => (a : ℤ)).prod := by
  simp [spoofEval, spoofOfBases, Multiset.map_map]

private theorem totient_spoofOfBases (x : Multiset ℕ) :
    spoofTotient (spoofOfBases x) = (x.map fun a : ℕ => (a : ℤ) - 1).prod := by
  simp [spoofTotient, spoofOfBases, Multiset.map_map]

-- A unitary spoof Lehmer factorization has at least two factors.
private theorem two_le_card_of_isSpoofLehmer (x : Multiset ℕ) (k : ℤ)
    (h : IsSpoofLehmer k (spoofOfBases x)) : 2 ≤ Multiset.card x := by
  rcases h.2.2 with hr | ⟨p, hp, hlt⟩
  · simpa [card_spoofOfBases] using hr
  · have hp' : p ∈ x.map (fun a => (a, 1)) := hp
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.mp hp'
    simp at hlt

-- The bound is at least one once there are two factors.
private theorem one_le_bound (r : ℕ) (hr : 2 ≤ r) :
    (1 : ℤ) ≤ 2 ^ 2 ^ r - 2 ^ 2 ^ (r - 1) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le (show 1 ≤ r by omega)
  have hsub : 1 + s - 1 = s := by omega
  rw [hsub]
  have hexp : 2 ^ (1 + s) = 2 ^ s + 2 ^ s := by ring
  have h1 : (1 : ℕ) ≤ 2 ^ s := by
    have hpos := pow_pos (show (0 : ℕ) < 2 by norm_num) s
    omega
  have ht2 : (2 : ℤ) ≤ 2 ^ 2 ^ s := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ 2 ^ s := pow_le_pow_right₀ (by norm_num) h1
  have hsq : (2 : ℤ) ^ 2 ^ (1 + s) = (2 ^ 2 ^ s) ^ 2 := by
    rw [hexp, pow_add, pow_two]
  nlinarith [hsq, ht2, sq_nonneg ((2 : ℤ) ^ 2 ^ s - 1)]

-- The remaining factors after dropping the last sorted base.
private theorem filter_eq_erase (r : ℕ) (hr : 2 ≤ r) (h1 : r - 1 < r) :
    Finset.univ.filter (fun j : Fin r => j.val + 1 < r)
      = Finset.univ.erase (⟨r - 1, h1⟩ : Fin r) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_erase, true_and, and_true]
  constructor
  · intro hj hcon
    have hjlt := j.isLt
    have hval : j.val = r - 1 := by rw [hcon]
    omega
  · intro hj
    have hjlt := j.isLt
    by_contra hcon
    have hval : j.val = r - 1 := by omega
    exact hj (Fin.ext hval)

-- One factor of the rational product as a quotient.
private theorem one_sub_inv_eq (x : ℚ) (hx : x ≠ 0) : 1 - 1 / x = (x - 1) / x := by
  rw [eq_div_iff hx, sub_mul, div_mul_cancel₀ _ hx, one_mul]

/-- **Bound on unitary Lehmer factorizations.** Let $k$ be an integer and let $x_1, \dots, x_r$ be
natural numbers. If the spoof factorization $x_1 \cdots x_r$ with every exponent $1$ is a spoof
$k$-Lehmer factorization (a unitary $k$-Lehmer factorization), then its spoof evaluation
$\tilde{e}(x_1 \cdots x_r) = \prod_{i=1}^{r} x_i$ is at most $2^{2^r} - 2^{2^{r-1}}$.

The paper takes $k > 0$; here $k$ is any integer. For $k \le 0$ the hypothesis forces the spoof
evaluation to be $1$.

Source: Elchin Hasanalizade, *Some Remarks on a Paper of Molnar and Singh*, INTEGERS 26 (2026),
Article A100, Theorem 1 (`integers-2026-A100-thm-1`). -/
public theorem spoofEval_le_of_isSpoofLehmer_spoofOfBases (k : ℤ) (x : Multiset ℕ)
    (h : IsSpoofLehmer k (spoofOfBases x)) :
    spoofEval (spoofOfBases x) ≤
      2 ^ 2 ^ Multiset.card x - 2 ^ 2 ^ (Multiset.card x - 1) := by
  have hr : 2 ≤ Multiset.card x := two_le_card_of_isSpoofLehmer x k h
  by_cases htriv : IsTrivialSpoof (spoofOfBases x)
  · have hall1 : ∀ a ∈ x, a = 1 := by
      intro a ha
      have hmem : (a, 1) ∈ spoofOfBases x := Multiset.mem_map_of_mem _ ha
      exact htriv _ hmem
    have heval1 : (x.map fun a : ℕ => (a : ℤ)).prod = 1 := by
      apply Multiset.prod_eq_one
      intro b hb
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hb
      simp [hall1 a ha]
    rw [eval_spoofOfBases, heval1]
    exact one_le_bound _ hr
  · have hge2 : ∀ a ∈ x, 2 ≤ a := by
      intro a ha
      have hpos : 0 < a := (h.1 _ (Multiset.mem_map_of_mem _ ha)).1
      by_contra hcon
      have ha1 : a = 1 := by omega
      apply htriv
      apply isTrivialSpoof_of_isSpoofLehmer_of_one_mem _ ⟨k, h⟩
      exact ⟨(a, 1), Multiset.mem_map_of_mem _ ha, ha1⟩
    obtain ⟨l, hcoe, hpair, hlen⟩ : ∃ l : List ℕ, (↑l : Multiset ℕ) = x ∧
        l.Pairwise (· ≤ ·) ∧ l.length = Multiset.card x :=
      ⟨x.sort (· ≤ ·), Multiset.sort_eq _ _, Multiset.pairwise_sort _ _,
        Multiset.length_sort _⟩
    have hrlen : 2 ≤ l.length := by omega
    have h1len : l.length - 1 < l.length := by omega
    have hmono : Monotone l.get := by
      intro a b hab
      obtain rfl | hlt := Fin.eq_or_lt_of_le hab
      · exact le_rfl
      · exact hpair.rel_get_of_lt hlt
    have hf2 : ∀ i : Fin l.length, 2 ≤ l.get i := by
      intro i
      apply hge2
      rw [← hcoe]
      exact Multiset.mem_coe.mpr (l.get_mem i)
    have hf1 : ∀ i : Fin l.length, 1 < l.get i := by
      intro i
      have h2 := hf2 i
      omega
    have hEfin : (∏ i : Fin l.length, ((l.get i : ℕ) : ℤ)) =
        spoofEval (spoofOfBases x) := by
      have hmap : (fun i : Fin l.length => ((l.get i : ℕ) : ℤ)) =
          ((fun a : ℕ => (a : ℤ)) ∘ l.get) := rfl
      rw [eval_spoofOfBases, ← List.prod_ofFn, hmap, ← List.map_ofFn, List.ofFn_get,
        ← Multiset.prod_coe, ← Multiset.map_coe, hcoe]
    have hPfin : (∏ i : Fin l.length, ((l.get i : ℤ) - 1)) =
        spoofTotient (spoofOfBases x) := by
      have hmap : (fun i : Fin l.length => ((l.get i : ℤ) - 1)) =
          ((fun a : ℕ => ((a : ℤ) - 1)) ∘ l.get) := rfl
      rw [totient_spoofOfBases, ← List.prod_ofFn, hmap, ← List.map_ofFn, List.ofFn_get,
        ← Multiset.prod_coe, ← Multiset.map_coe, hcoe]
    have heq : k * (∏ i : Fin l.length, ((l.get i : ℤ) - 1)) =
        (∏ i : Fin l.length, ((l.get i : ℕ) : ℤ)) - 1 := by
      rw [hEfin, hPfin]
      exact h.2.1
    have hPpos : (0 : ℤ) < ∏ i : Fin l.length, ((l.get i : ℤ) - 1) := by
      apply Finset.prod_pos
      intro i _
      have h2 : (2 : ℤ) ≤ ((l.get i : ℕ) : ℤ) := by exact_mod_cast hf2 i
      linarith
    have hEnat2 : (2 : ℕ) ≤ ∏ i : Fin l.length, l.get i := by
      have h0 : (0 : ℕ) < l.length := by omega
      calc (2 : ℕ) ≤ l.get ⟨0, h0⟩ := hf2 _
        _ ≤ ∏ i : Fin l.length, l.get i :=
          Finset.single_le_prod (fun i _ => by have h2 := hf2 i; omega)
            (Finset.mem_univ _)
    have hEgt1 : (1 : ℤ) < ∏ i : Fin l.length, ((l.get i : ℕ) : ℤ) := by
      have hcast : (∏ i : Fin l.length, ((l.get i : ℕ) : ℤ)) =
          ((∏ i : Fin l.length, l.get i : ℕ) : ℤ) := (Nat.cast_prod _ _).symm
      rw [hcast]
      exact_mod_cast (by omega : (1 : ℕ) < ∏ i : Fin l.length, l.get i)
    have hkpos : (0 : ℤ) < k := by
      have hmul : (0 : ℤ) < k * ∏ i : Fin l.length, ((l.get i : ℤ) - 1) := by
        rw [heq]
        linarith [hEgt1]
      exact pos_of_mul_pos_left hmul hPpos.le
    set b : ℕ := k.toNat with hb_def
    have hkb : (b : ℤ) = k := by
      rw [hb_def]
      exact Int.toNat_of_nonneg hkpos.le
    have hkbQ : (b : ℚ) = (k : ℚ) := by
      rw [← hkb, Int.cast_natCast]
    have hkQpos : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hkpos
    have hfilter : Finset.univ.filter (fun j : Fin l.length => j.val + 1 < l.length)
        = Finset.univ.erase (⟨l.length - 1, h1len⟩ : Fin l.length) :=
      filter_eq_erase l.length hrlen h1len
    have hsplitE : (∏ i : Fin l.length, ((l.get i : ℕ) : ℤ)) =
        (∏ i ∈ Finset.univ.filter (fun j : Fin l.length => j.val + 1 < l.length),
          ((l.get i : ℕ) : ℤ)) * ((l.get ⟨l.length - 1, h1len⟩ : ℕ) : ℤ) := by
      rw [hfilter]
      exact (Finset.prod_erase_mul _ _ (Finset.mem_univ _)).symm
    have hsplitP : (∏ i : Fin l.length, ((l.get i : ℤ) - 1)) =
        (∏ i ∈ Finset.univ.filter (fun j : Fin l.length => j.val + 1 < l.length),
          ((l.get i : ℤ) - 1)) *
          ((((l.get ⟨l.length - 1, h1len⟩ : ℕ) : ℤ)) - 1) := by
      rw [hfilter]
      exact (Finset.prod_erase_mul _ _ (Finset.mem_univ _)).symm
    have hE'2 : (2 : ℤ) ≤ ∏ i ∈ Finset.univ.filter
        (fun j : Fin l.length => j.val + 1 < l.length), ((l.get i : ℕ) : ℤ) := by
      have hcast : (∏ i ∈ Finset.univ.filter
            (fun j : Fin l.length => j.val + 1 < l.length), ((l.get i : ℕ) : ℤ)) =
          ((∏ i ∈ Finset.univ.filter (fun j : Fin l.length => j.val + 1 < l.length),
            l.get i : ℕ) : ℤ) := (Nat.cast_prod _ _).symm
      rw [hcast]
      have hne : (Finset.univ.filter
          (fun j : Fin l.length => j.val + 1 < l.length)).Nonempty :=
        ⟨⟨0, by omega⟩, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by change (0 : ℕ) + 1 < l.length; omega⟩⟩
      obtain ⟨j, hj⟩ := hne
      have hle : (2 : ℕ) ≤ ∏ i ∈ Finset.univ.filter
          (fun j : Fin l.length => j.val + 1 < l.length), l.get i :=
        le_trans (hf2 j)
          (Finset.single_le_prod (fun i _ => by have h2 := hf2 i; omega) hj)
      exact_mod_cast hle
    have hkey : (∏ i ∈ Finset.univ.filter (fun j : Fin l.length => j.val + 1 < l.length),
          ((l.get i : ℕ) : ℤ)) <
        k * (∏ i ∈ Finset.univ.filter (fun j : Fin l.length => j.val + 1 < l.length),
          ((l.get i : ℤ) - 1)) := by
      by_contra hcon
      have hle := le_of_not_gt hcon
      have hy2 : (2 : ℤ) ≤ ((l.get ⟨l.length - 1, h1len⟩ : ℕ) : ℤ) := by
        exact_mod_cast hf2 _
      have hmul := mul_le_mul_of_nonneg_right hle (show (0 : ℤ) ≤
        (((l.get ⟨l.length - 1, h1len⟩ : ℕ) : ℤ) - 1) by linarith)
      have h := heq
      rw [hsplitE, hsplitP] at h
      linarith [hmul, h, hE'2]
    have hfactorQ : ∀ j : Fin l.length, (1 - 1 / (l.get j : ℚ)) =
        (((l.get j : ℕ) : ℚ) - 1) / ((l.get j : ℕ) : ℚ) := by
      intro j
      apply one_sub_inv_eq
      have h2 := hf2 j
      exact_mod_cast (by omega : l.get j ≠ 0)
    have hlowprod : (∏ j : Fin l.length, (1 - 1 / (l.get j : ℚ))) =
        (∏ j : Fin l.length, (((l.get j : ℕ) : ℚ) - 1)) /
          (∏ j : Fin l.length, ((l.get j : ℕ) : ℚ)) := by
      rw [← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl (fun j _ => hfactorQ j)
    have hprod' : (∏ j ∈ Finset.univ.filter
          (fun j : Fin l.length => j.val + 1 < l.length), (1 - 1 / (l.get j : ℚ))) =
        (∏ j ∈ Finset.univ.filter (fun j : Fin l.length => j.val + 1 < l.length),
          (((l.get j : ℕ) : ℚ) - 1)) /
          (∏ j ∈ Finset.univ.filter (fun j : Fin l.length => j.val + 1 < l.length),
            ((l.get j : ℕ) : ℚ)) := by
      rw [← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl (fun j _ => hfactorQ j)
    have hElow_pos : (0 : ℚ) < ∏ j : Fin l.length, ((l.get j : ℕ) : ℚ) := by
      apply Finset.prod_pos
      intro j _
      have h2 := hf2 j
      exact_mod_cast (by omega : 0 < l.get j)
    have hE'Qpos : (0 : ℚ) < ∏ j ∈ Finset.univ.filter
        (fun j : Fin l.length => j.val + 1 < l.length), ((l.get j : ℕ) : ℚ) := by
      apply Finset.prod_pos
      intro j _
      have h2 := hf2 j
      exact_mod_cast (by omega : 0 < l.get j)
    have heqQ : (k : ℚ) * (∏ j : Fin l.length, (((l.get j : ℕ) : ℚ) - 1)) =
        (∏ j : Fin l.length, ((l.get j : ℕ) : ℚ)) - 1 := by
      exact_mod_cast heq
    have hkeyQ : (∏ j ∈ Finset.univ.filter
          (fun j : Fin l.length => j.val + 1 < l.length), ((l.get j : ℕ) : ℚ)) <
        (k : ℚ) * (∏ j ∈ Finset.univ.filter
          (fun j : Fin l.length => j.val + 1 < l.length),
          (((l.get j : ℕ) : ℚ) - 1)) := by
      exact_mod_cast hkey
    have hlow : (∏ j : Fin l.length, (1 - 1 / (l.get j : ℚ))) ≤ (1 : ℚ) / (b : ℚ) := by
      rw [hlowprod, hkbQ]
      exact (div_le_div_iff₀ hElow_pos hkQpos).mpr (by linarith [heqQ])
    have hup : (1 : ℚ) / (b : ℚ) <
        ∏ j ∈ Finset.univ.filter (fun j : Fin l.length => j.val + 1 < l.length),
          (1 - 1 / (l.get j : ℚ)) := by
      rw [hprod', hkbQ]
      exact (div_lt_div_iff₀ hkQpos hE'Qpos).mpr (by linarith [hkeyQ])
    have hn := nielsen_prod_one_sub_inv_bound l.length 1 b l.get hmono hf1
      (by simpa using hlow) (by simpa using hup)
    have hcast : spoofEval (spoofOfBases x) =
        ((∏ j : Fin l.length, l.get j : ℕ) : ℤ) := by
      rw [← hEfin]
      exact (Nat.cast_prod _ _).symm
    have hNz : ((∏ j : Fin l.length, l.get j : ℕ) : ℤ) ≤
        (2 : ℤ) ^ 2 ^ l.length - 2 ^ 2 ^ (l.length - 1) := by
      have hn1 := hn
      have h11 : (1 : ℕ) + 1 = 2 := rfl
      simp only [one_mul, h11] at hn1
      have hsub : (2 : ℕ) ^ 2 ^ (l.length - 1) ≤ 2 ^ 2 ^ l.length :=
        pow_le_pow_right₀ (by norm_num)
          (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _))
      have h2 : ((∏ j : Fin l.length, l.get j : ℕ) : ℤ) ≤
          (((2 : ℕ) ^ 2 ^ l.length - 2 ^ 2 ^ (l.length - 1) : ℕ) : ℤ) := by
        exact_mod_cast hn1
      rw [Nat.cast_sub hsub, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat] at h2
      exact h2
    rw [hcast, ← hlen]
    exact hNz

end MetaMathlibExt
