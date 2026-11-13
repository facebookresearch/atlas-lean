/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Computability.Reduce
import Mathlib.Data.Int.Star
import Mathlib.Tactic.LinearCombination

@[expose] public section

open scoped BigOperators

namespace MetaMathlibExt

/-- **Carry equations for reverse multiples, general form.** Let $g, k, n$ be natural numbers
with $2 \le k < g$, and let $a_0, \dots, a_{n-1}$ be natural numbers with $a_i < g$ for every $i$.
Then $k \sum_{i<n} a_i g^i = \sum_{i<n} a_{n-1-i} g^i$ if and only if there is a unique sequence
of natural numbers $r_0, \dots, r_n$ with $r_0 = 0$, $r_n = 0$ and, for every $i < n$,
$r_{i+1} < k$ and $k a_i + r_i = a_{n-1-i} + r_{i+1} g$.

No hypothesis is placed on $n$ or on the end digits $a_0$ and $a_{n-1}$; in particular $n$ may be
$0$. -/
theorem young_reverse_multiple_carry_path_iff_general
    (g k n : ℕ) (hgk : 2 ≤ k) (hkg : k < g)
    (a : Fin n → ℕ) (hdigit : ∀ i, a i < g) :
    k * (∑ i, a i * g ^ i.val) = ∑ i, a (Fin.rev i) * g ^ i.val ↔
      ∃! r : Fin (n + 1) → ℕ,
        r ⟨0, Nat.succ_pos n⟩ = 0 ∧ r (Fin.last n) = 0 ∧
          ∀ i : Fin n, r i.succ < k ∧
            k * a i + r i.castSucc = a (Fin.rev i) + r i.succ * g := by
  constructor
  · intro h
    classical
    have hgpos : 0 < g := by omega
    have hgposZ : (0:ℤ) < (g:ℤ) := by exact_mod_cast hgpos
    have hgneZ : (g:ℤ) ≠ 0 := ne_of_gt hgposZ
    have hgne : g ≠ 0 := ne_of_gt hgpos
    set A : ℕ → ℤ := fun m => if h : m < n then (a ⟨m, h⟩ : ℤ) else 0 with hA
    set B : ℕ → ℤ := fun m => if h : m < n then (a (Fin.rev ⟨m, h⟩) : ℤ) else 0 with hB
    have hAm : ∀ (m : ℕ) (h : m < n), A m = (a ⟨m, h⟩ : ℤ) := by
      intro m h; simp only [hA]; split <;> simp_all
    have hBm : ∀ (m : ℕ) (h : m < n), B m = (a (Fin.rev ⟨m, h⟩) : ℤ) := by
      intro m h; simp only [hB]; split <;> simp_all
    have hAm0 : ∀ (m : ℕ), ¬ m < n → A m = 0 := by
      intro m h; simp only [hA]; split <;> simp_all
    have hBm0 : ∀ (m : ℕ), ¬ m < n → B m = 0 := by
      intro m h; simp only [hB]; split <;> simp_all
    have hAlt : ∀ m, A m < (g:ℤ) := by
      intro m
      by_cases h : m < n
      · rw [hAm m h]; exact_mod_cast hdigit ⟨m, h⟩
      · rw [hAm0 m h]; exact hgposZ
    have hBlt : ∀ m, B m < (g:ℤ) := by
      intro m
      by_cases h : m < n
      · rw [hBm m h]; exact_mod_cast hdigit (Fin.rev ⟨m, h⟩)
      · rw [hBm0 m h]; exact hgposZ
    have hAge : ∀ m, 0 ≤ A m := by
      intro m
      by_cases h : m < n
      · rw [hAm m h]; positivity
      · rw [hAm0 m h]
    have hBge : ∀ m, 0 ≤ B m := by
      intro m
      by_cases h : m < n
      · rw [hBm m h]; positivity
      · rw [hBm0 m h]
    -- partial sum bounds
    have hLAlt : ∀ m, ∑ j ∈ Finset.range m, A j * (g:ℤ)^j < (g:ℤ)^m := by
      intro m
      induction m with
      | zero => rw [Finset.sum_range_zero, pow_zero]; exact zero_lt_one
      | succ m ih =>
        rw [Finset.sum_range_succ, pow_succ]
        have h1 : A m * (g:ℤ)^m ≤ ((g:ℤ) - 1) * (g:ℤ)^m :=
          mul_le_mul_of_nonneg_right (by linarith [hAlt m]) (pow_nonneg (le_of_lt hgposZ) m)
        nlinarith [ih]
    have hLBlt : ∀ m, ∑ j ∈ Finset.range m, B j * (g:ℤ)^j < (g:ℤ)^m := by
      intro m
      induction m with
      | zero => rw [Finset.sum_range_zero, pow_zero]; exact zero_lt_one
      | succ m ih =>
        rw [Finset.sum_range_succ, pow_succ]
        have h1 : B m * (g:ℤ)^m ≤ ((g:ℤ) - 1) * (g:ℤ)^m :=
          mul_le_mul_of_nonneg_right (by linarith [hBlt m]) (pow_nonneg (le_of_lt hgposZ) m)
        nlinarith [ih]
    have hLAge : ∀ m, 0 ≤ ∑ j ∈ Finset.range m, A j * (g:ℤ)^j :=
      fun m => Finset.sum_nonneg (fun j _ => mul_nonneg (hAge j) (pow_nonneg (le_of_lt hgposZ) _))
    have hLBge : ∀ m, 0 ≤ ∑ j ∈ Finset.range m, B j * (g:ℤ)^j :=
      fun m => Finset.sum_nonneg (fun j _ => mul_nonneg (hBge j) (pow_nonneg (le_of_lt hgposZ) _))
    -- S and its relation to the hypothesis
    set S : ℕ → ℤ := fun m => k * (∑ j ∈ Finset.range m, A j * (g:ℤ)^j)
      - ∑ j ∈ Finset.range m, B j * (g:ℤ)^j with hSdef
    have hZ : (k:ℤ) * (∑ i : Fin n, ((a i : ℕ):ℤ) * (g:ℤ)^i.val)
        = ∑ i : Fin n, ((a (Fin.rev i) : ℕ):ℤ) * (g:ℤ)^i.val := by
      exact_mod_cast h
    have hAfinZ : (∑ i : Fin n, ((a i : ℕ):ℤ) * (g:ℤ)^i.val)
        = ∑ m ∈ Finset.range n, A m * (g:ℤ)^m := by
      have e := Fin.sum_univ_eq_sum_range (fun m => A m * (g:ℤ)^m) n
      rw [← e]
      apply Finset.sum_congr rfl
      intro i _
      show ((a i : ℕ):ℤ) * (g:ℤ)^i.val = A i.val * (g:ℤ)^i.val
      rw [hAm i.val i.isLt]
    have hBfinZ : (∑ i : Fin n, ((a (Fin.rev i) : ℕ):ℤ) * (g:ℤ)^i.val)
        = ∑ m ∈ Finset.range n, B m * (g:ℤ)^m := by
      have e := Fin.sum_univ_eq_sum_range (fun m => B m * (g:ℤ)^m) n
      rw [← e]
      apply Finset.sum_congr rfl
      intro i _
      show ((a (Fin.rev i) : ℕ):ℤ) * (g:ℤ)^i.val = B i.val * (g:ℤ)^i.val
      rw [hBm i.val i.isLt, Fin.eta i i.isLt]
    have hSn : S n = 0 := by
      simp only [hSdef]
      rw [← hAfinZ, ← hBfinZ]
      linear_combination hZ
    -- difference sums equal S
    have hS_eq : ∀ m, (∑ j ∈ Finset.range m, (k * A j - B j) * (g:ℤ)^j)
        = k * (∑ j ∈ Finset.range m, A j * (g:ℤ)^j)
          - ∑ j ∈ Finset.range m, B j * (g:ℤ)^j := by
      intro m
      calc ∑ j ∈ Finset.range m, (k * A j - B j) * (g:ℤ)^j
          = ∑ j ∈ Finset.range m, (k * (A j * (g:ℤ)^j) - B j * (g:ℤ)^j) :=
            Finset.sum_congr rfl (fun j _ => by ring)
        _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    set q : ℕ → ℤ := fun m => (∑ j ∈ Finset.Ico m n, B j * (g:ℤ)^(j-m))
      - k * (∑ j ∈ Finset.Ico m n, A j * (g:ℤ)^(j-m)) with hqdef
    have hqeq : ∀ m, q m = (∑ j ∈ Finset.Ico m n, B j * (g:ℤ)^(j-m))
        - k * (∑ j ∈ Finset.Ico m n, A j * (g:ℤ)^(j-m)) := by
      intro m; simp only [hqdef]
    -- S m = G^m * q m
    have hSq : ∀ m, m ≤ n → S m = (g:ℤ)^m * q m := by
      intro m hm
      have h0 := Finset.sum_range_add_sum_Ico (fun j => (k * A j - B j) * (g:ℤ)^j) hm
      rw [hS_eq m, hS_eq n] at h0
      have hSn' : k * (∑ j ∈ Finset.range n, A j * (g:ℤ)^j)
          - ∑ j ∈ Finset.range n, B j * (g:ℤ)^j = 0 := hSn
      rw [hSn'] at h0
      have h2a : (∑ j ∈ Finset.Ico m n, (k * A j - B j) * (g:ℤ)^j)
          = (g:ℤ)^m * (∑ j ∈ Finset.Ico m n, (k * A j - B j) * (g:ℤ)^(j-m)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have hjm : m ≤ j := (Finset.mem_Ico.mp hj).1
        have hp : (g:ℤ)^j = (g:ℤ)^m * (g:ℤ)^(j-m) := by
          conv_lhs => rw [← Nat.add_sub_cancel' hjm]
          rw [pow_add]
        rw [hp]; ring
      have h2b : (∑ j ∈ Finset.Ico m n, (k * A j - B j) * (g:ℤ)^(j-m))
          = k * (∑ j ∈ Finset.Ico m n, A j * (g:ℤ)^(j-m))
            - ∑ j ∈ Finset.Ico m n, B j * (g:ℤ)^(j-m) := by
        calc ∑ j ∈ Finset.Ico m n, (k * A j - B j) * (g:ℤ)^(j-m)
            = ∑ j ∈ Finset.Ico m n,
              (k * (A j * (g:ℤ)^(j-m)) - B j * (g:ℤ)^(j-m)) :=
              Finset.sum_congr rfl (fun j _ => by ring)
          _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      have h2 : (∑ j ∈ Finset.Ico m n, (k * A j - B j) * (g:ℤ)^j)
          = (g:ℤ)^m * (k * (∑ j ∈ Finset.Ico m n, A j * (g:ℤ)^(j-m))
            - ∑ j ∈ Finset.Ico m n, B j * (g:ℤ)^(j-m)) := by
        rw [h2a, h2b]
      have hSm' : S m = k * (∑ j ∈ Finset.range m, A j * (g:ℤ)^j)
          - ∑ j ∈ Finset.range m, B j * (g:ℤ)^j := rfl
      rw [h2] at h0
      rw [hqeq m, hSm']
      linear_combination h0
    -- S bounds
    have hSlow : ∀ m, -((g:ℤ)^m) < S m := by
      intro m
      have h1 : (0:ℤ) ≤ k * (∑ j ∈ Finset.range m, A j * (g:ℤ)^j) :=
        mul_nonneg (by exact_mod_cast Nat.zero_le k) (hLAge m)
      have h2 : (∑ j ∈ Finset.range m, B j * (g:ℤ)^j) < (g:ℤ)^m := hLBlt m
      have hS' : S m = k * (∑ j ∈ Finset.range m, A j * (g:ℤ)^j)
          - ∑ j ∈ Finset.range m, B j * (g:ℤ)^j := rfl
      rw [hS']
      linarith
    have hShi : ∀ m, S m < (k:ℤ) * (g:ℤ)^m := by
      intro m
      have h1 : k * (∑ j ∈ Finset.range m, A j * (g:ℤ)^j) < k * (g:ℤ)^m :=
        mul_lt_mul_of_pos_left (hLAlt m) (by omega)
      have h2 : 0 ≤ (∑ j ∈ Finset.range m, B j * (g:ℤ)^j) := hLBge m
      have hS' : S m = k * (∑ j ∈ Finset.range m, A j * (g:ℤ)^j)
          - ∑ j ∈ Finset.range m, B j * (g:ℤ)^j := rfl
      rw [hS']
      linarith
    -- q bounds
    have hqb : ∀ m, m ≤ n → 0 ≤ q m ∧ q m < (k:ℤ) := by
      intro m hm
      have hG : (0:ℤ) < (g:ℤ)^m := pow_pos hgposZ m
      have hSqm := hSq m hm
      have hlo := hSlow m
      have hhi := hShi m
      rw [hSqm] at hlo hhi
      constructor
      · by_contra hc
        have hc' : q m < 0 := lt_of_not_ge hc
        have hle : (g:ℤ)^m * q m ≤ (g:ℤ)^m * (-1) :=
          mul_le_mul_of_nonneg_left (by omega) (le_of_lt hG)
        linarith
      · by_contra hc
        have hc' : (k:ℤ) ≤ q m := le_of_not_gt hc
        have hle : (k:ℤ) * (g:ℤ)^m ≤ q m * (g:ℤ)^m :=
          mul_le_mul_of_nonneg_right hc' (le_of_lt hG)
        linarith
    -- recurrence
    have hrec : ∀ m, m < n → (g:ℤ) * q (m+1) = q m + k * A m - B m := by
      intro m hm
      have hSm : S (m+1) = S m + (g:ℤ)^m * (k * A m - B m) := by
        have hS1 : S (m+1) = k * (∑ j ∈ Finset.range (m+1), A j * (g:ℤ)^j)
            - ∑ j ∈ Finset.range (m+1), B j * (g:ℤ)^j := rfl
        have hS0 : S m = k * (∑ j ∈ Finset.range m, A j * (g:ℤ)^j)
            - ∑ j ∈ Finset.range m, B j * (g:ℤ)^j := rfl
        rw [hS1, hS0, Finset.sum_range_succ, Finset.sum_range_succ]
        ring
      have h1 := hSq (m+1) (Nat.succ_le_of_lt hm)
      have h2 := hSq m (le_of_lt hm)
      rw [h1, h2, pow_succ] at hSm
      have hGne : (g:ℤ)^m ≠ 0 := pow_ne_zero _ hgneZ
      have h3 : (g:ℤ)^m * (g * q (m+1)) = (g:ℤ)^m * (q m + k * A m - B m) := by
        linear_combination hSm
      exact mul_left_cancel₀ hGne h3
    -- transfer A B to a-values
    have eA : ∀ i : Fin n, A i.val = (((a i : ℕ)):ℤ) := by
      intro i
      have h1 := hAm i.val i.isLt
      rw [Fin.eta i i.isLt] at h1
      exact h1
    have eB : ∀ i : Fin n, B i.val = (((a (Fin.rev i) : ℕ)):ℤ) := by
      intro i
      have h1 := hBm i.val i.isLt
      rw [Fin.eta i i.isLt] at h1
      exact h1
    have htoNat : ∀ m : ℤ, 0 ≤ m → m < (k:ℤ) → m.toNat < k := by
      intro m h0 hk
      have h1 : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg h0
      have h2 : ((m.toNat : ℕ) : ℤ) < (k : ℤ) := by rw [h1]; exact hk
      exact_mod_cast h2
    have hq0 : q 0 = 0 := by
      have h := hSq 0 (Nat.zero_le n)
      have hS0 : S 0 = 0 := by simp only [hSdef]; simp
      rw [hS0] at h
      have hs := h.symm
      simpa using hs
    have hqn : q n = 0 := by
      have h := hSq n le_rfl
      rw [hSn] at h
      have hs : (g:ℤ)^n * q n = 0 := h.symm
      rw [mul_eq_zero] at hs
      exact hs.resolve_left (pow_ne_zero _ hgneZ)
    -- witness satisfies the equations
    have hwit : ∀ i : Fin n, (q (i.val + 1)).toNat < k ∧
        k * a i + (q i.val).toNat
          = a (Fin.rev i) + (q (i.val + 1)).toNat * g := by
      intro i
      have hm1 : i.val + 1 ≤ n := Nat.succ_le_of_lt i.isLt
      have hm0 : i.val ≤ n := by have := i.isLt; omega
      obtain ⟨hq0i, hqki⟩ := hqb i.val hm0
      obtain ⟨hq0i1, hqki1⟩ := hqb (i.val + 1) hm1
      have hrec_i := hrec i.val i.isLt
      have hcast_eq : ((((q i.val).toNat : ℕ)) : ℤ) = q i.val :=
        Int.toNat_of_nonneg hq0i
      have hsucc_eq : ((((q (i.val + 1)).toNat : ℕ)) : ℤ) = q (i.val + 1) :=
        Int.toNat_of_nonneg hq0i1
      constructor
      · exact htoNat _ hq0i1 hqki1
      · have hz : (k:ℤ) * (((a i : ℕ)):ℤ) + q i.val
            = (((a (Fin.rev i) : ℕ)):ℤ) + q (i.val + 1) * (g:ℤ) := by
          rw [← eA i, ← eB i]
          linarith
        rw [← hcast_eq, ← hsucc_eq] at hz
        exact_mod_cast hz
    -- assemble
    refine ⟨fun j => (q j.val).toNat, ⟨?_, ?_, ?_⟩, ?_⟩
    · change (q 0).toNat = 0
      rw [hq0]
      rfl
    · change (q (Fin.last n).val).toNat = 0
      rw [show (Fin.last n).val = n from Fin.val_last n, hqn]
      rfl
    · intro i
      have hi := hwit i
      have hcs : (fun j => (q j.val).toNat) i.castSucc = (q i.val).toNat := by
        change (q (i.castSucc).val).toNat = _
        rw [Fin.val_castSucc]
      have hss : (fun j => (q j.val).toNat) i.succ = (q (i.val + 1)).toNat := by
        change (q (i.succ).val).toNat = _
        rw [Fin.val_succ]
      rw [hcs, hss]
      exact hi
    · intro s hs
      obtain ⟨hs0, hsn, hseq⟩ := hs
      have hpoint : ∀ (m : ℕ) (h : m < n + 1), s ⟨m, h⟩ = (q m).toNat := by
        intro m
        induction m with
        | zero =>
          intro h
          have e0 : (⟨0, h⟩ : Fin (n + 1)) = ⟨0, Nat.succ_pos n⟩ := rfl
          rw [e0, hs0]
          change 0 = (q 0).toNat
          rw [hq0]
          rfl
        | succ m ih =>
          intro h
          have hm : m < n := Nat.lt_of_succ_lt_succ h
          have e1 : (⟨m + 1, h⟩ : Fin (n + 1)) = (⟨m, hm⟩ : Fin n).succ := by
            apply Fin.ext
            simp
          have e2 : (⟨m, Nat.lt_succ_of_lt hm⟩ : Fin (n + 1))
              = (⟨m, hm⟩ : Fin n).castSucc := by
            apply Fin.ext
            simp
          have ihc : s (⟨m, hm⟩ : Fin n).castSucc = (q m).toNat := by
            rw [← e2]
            exact ih (Nat.lt_succ_of_lt hm)
          obtain ⟨_, hsi⟩ := hseq ⟨m, hm⟩
          obtain ⟨_, hwi⟩ := hwit ⟨m, hm⟩
          simp only at hsi hwi
          have hcancel : s (⟨m, hm⟩ : Fin n).succ * g = (q (m + 1)).toNat * g := by
            have h1 : k * a ⟨m, hm⟩ + s (⟨m, hm⟩ : Fin n).castSucc
                = a (Fin.rev ⟨m, hm⟩) + s (⟨m, hm⟩ : Fin n).succ * g := hsi
            rw [ihc] at h1
            have h2 : k * a ⟨m, hm⟩ + (q m).toNat
                = a (Fin.rev ⟨m, hm⟩) + (q (m + 1)).toNat * g := hwi
            have h3 : a (Fin.rev ⟨m, hm⟩) + s (⟨m, hm⟩ : Fin n).succ * g
                = a (Fin.rev ⟨m, hm⟩) + (q (m + 1)).toNat * g := by
              rw [← h1, ← h2]
            exact Nat.add_left_cancel h3
          have hseq2 : s (⟨m, hm⟩ : Fin n).succ = (q (m + 1)).toNat :=
            mul_right_cancel₀ hgne hcancel
          rw [e1]
          exact hseq2
      have hfun : s = (fun j => (q j.val).toNat) := by
        apply funext
        intro j
        have hj := hpoint j.val j.isLt
        rwa [Fin.eta j j.isLt] at hj
      exact hfun
  · rintro ⟨r, ⟨hr0, hrn, heq⟩, -⟩
    classical
    set A : ℕ → ℕ := fun m => if h : m < n then a ⟨m, h⟩ else 0 with hA
    set B : ℕ → ℕ := fun m => if h : m < n then a (Fin.rev ⟨m, h⟩) else 0 with hB
    set R : ℕ → ℕ := fun m => if h : m < n + 1 then r ⟨m, h⟩ else 0 with hR
    have hAm : ∀ (m : ℕ) (h : m < n), A m = a ⟨m, h⟩ := by
      intro m h; simp only [hA]; split <;> simp_all
    have hBm : ∀ (m : ℕ) (h : m < n), B m = a (Fin.rev ⟨m, h⟩) := by
      intro m h; simp only [hB]; split <;> simp_all
    have hRm : ∀ (m : ℕ) (h : m < n + 1), R m = r ⟨m, h⟩ := by
      intro m h; simp only [hR]; split <;> simp_all
    have hR0 : R 0 = 0 := by
      have e := hRm 0 (Nat.succ_pos n)
      rw [e]; exact hr0
    have hRn : R n = 0 := by
      have e := hRm n (Nat.lt_succ_self n)
      have hlast : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n := by
        apply Fin.ext; simp [Fin.val_last]
      rw [e, hlast]; exact hrn
    have hcastFin : ∀ i : Fin n,
        i.castSucc = (⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1)) := by
      intro i
      apply Fin.ext
      simp [Fin.val_castSucc]
    have hsuccFin : ∀ i : Fin n,
        i.succ = (⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩ : Fin (n + 1)) := by
      intro i
      apply Fin.ext
      simp [Fin.val_succ]
    have hcast : ∀ i : Fin n, r i.castSucc = R i.val := by
      intro i
      rw [hRm i.val (Nat.lt_succ_of_lt i.isLt), hcastFin i]
    have hsucc : ∀ i : Fin n, r i.succ = R (i.val + 1) := by
      intro i
      rw [hRm (i.val + 1) (Nat.add_lt_add_right i.isLt 1), hsuccFin i]
    have key : ∀ m : ℕ, ∀ h : m < n,
        (k * A m + R m) * g ^ m = B m * g ^ m + R (m + 1) * g ^ (m + 1) := by
      intro m h
      have heqi := (heq ⟨m, h⟩).2
      rw [hcast ⟨m, h⟩, hsucc ⟨m, h⟩] at heqi
      simp only at heqi
      rw [hAm m h, hBm m h, heqi, add_mul, pow_succ]
      ring
    have sumkey : ∑ m ∈ Finset.range n, ((k * A m + R m) * g ^ m) =
        ∑ m ∈ Finset.range n, (B m * g ^ m + R (m + 1) * g ^ (m + 1)) :=
      Finset.sum_congr rfl (fun m hm => key m (Finset.mem_range.mp hm))
    rw [Finset.sum_add_distrib] at sumkey
    have hL : ∑ m ∈ Finset.range n, ((k * A m + R m) * g ^ m)
        = k * (∑ m ∈ Finset.range n, A m * g ^ m) + ∑ m ∈ Finset.range n, R m * g ^ m := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m _
      ring
    have htele : ∑ m ∈ Finset.range n, R m * g ^ m =
        ∑ m ∈ Finset.range n, R (m + 1) * g ^ (m + 1) := by
      have h1 : ∑ m ∈ Finset.range (n + 1), R m * g ^ m =
          ∑ m ∈ Finset.range n, R (m + 1) * g ^ (m + 1) + R 0 := by
        have h := Finset.sum_range_succ' (fun m => R m * g ^ m) n
        simpa [pow_zero] using h
      have h2 : ∑ m ∈ Finset.range (n + 1), R m * g ^ m =
          ∑ m ∈ Finset.range n, R m * g ^ m + R n * g ^ n := Finset.sum_range_succ _ n
      rw [hR0] at h1
      rw [hRn] at h2
      simp at h1 h2
      linarith
    have hAfin : (∑ i : Fin n, a i * g ^ i.val) = ∑ m ∈ Finset.range n, A m * g ^ m := by
      have e := Fin.sum_univ_eq_sum_range (fun m => A m * g ^ m) n
      rw [← e]
      apply Finset.sum_congr rfl
      intro i _
      show a i * g ^ i.val = A i.val * g ^ i.val
      rw [hAm i.val i.isLt]
    have hBfin : (∑ i : Fin n, a (Fin.rev i) * g ^ i.val) =
        ∑ m ∈ Finset.range n, B m * g ^ m := by
      have e := Fin.sum_univ_eq_sum_range (fun m => B m * g ^ m) n
      rw [← e]
      apply Finset.sum_congr rfl
      intro i _
      show a (Fin.rev i) * g ^ i.val = B i.val * g ^ i.val
      rw [hBm i.val i.isLt, Fin.eta i i.isLt]
    rw [hL] at sumkey
    rw [htele] at sumkey
    have hfin : k * (∑ m ∈ Finset.range n, A m * g ^ m) =
        ∑ m ∈ Finset.range n, B m * g ^ m := by linarith
    rw [hAfin, hBfin, hfin]

set_option linter.unusedVariables false in
/-- **Carry equations for reverse multiples.** Let $g, k, n$ be natural numbers with
$2 \le k < g$ and $n \ge 1$, and let $a_0, \dots, a_{n-1}$ be natural numbers with $a_i < g$ for
every $i$, $a_{n-1} \ne 0$ and $a_0 \ne 0$. Then $k \sum_{i<n} a_i g^i = \sum_{i<n} a_{n-1-i} g^i$,
that is, $k$ times the number with base-$g$ digits $a_{n-1}, \dots, a_0$ (most significant first)
equals the number with these digits reversed, if and only if there is a unique sequence of natural
numbers $r_0, \dots, r_n$ with $r_0 = 0$, $r_n = 0$ and, for every $i < n$, $r_{i+1} < k$ and
$k a_i + r_i = a_{n-1-i} + r_{i+1} g$.

The carry $r_{i+1}$ here is the source's $r_i$.

Source: L. H. Kendrick, *Young Graphs: 1089 et al.*, Journal of Integer
Sequences 18 (2015), Article 15.9.7, subsection `subsec:eqtns`, lines 128–154
(the column equations for `kN = Reverse_g(N)`, Young's bound `r_i ≤ k - 1`,
and equation `eq:rmdig`),
<https://cs.uwaterloo.ca/journals/JIS/VOL18/Kendrick/ken1.tex>.
It follows from `young_reverse_multiple_carry_path_iff_general`; the hypotheses `hfirst` and `hlast`
(and `hn`, which only serves to state them) are unused and keep the source's shape.
Proves `Wanted` entry `young_reverse_multiple_carry_path_iff`.
-/
theorem young_reverse_multiple_carry_path_iff
    (g k n : ℕ) (hgk : 2 ≤ k) (hkg : k < g) (hn : 0 < n)
    (a : Fin n → ℕ) (hdigit : ∀ i, a i < g)
    (hfirst : a (Fin.rev ⟨0, hn⟩) ≠ 0) (hlast : a ⟨0, hn⟩ ≠ 0) :
    k * (∑ i, a i * g ^ i.val) = ∑ i, a (Fin.rev i) * g ^ i.val ↔
      ∃! r : Fin (n + 1) → ℕ,
        r ⟨0, Nat.succ_pos n⟩ = 0 ∧ r (Fin.last n) = 0 ∧
          ∀ i : Fin n, r i.succ < k ∧
            k * a i + r i.castSucc = a (Fin.rev i) + r i.succ * g := by
  exact young_reverse_multiple_carry_path_iff_general g k n hgk hkg a hdigit

end MetaMathlibExt

end
