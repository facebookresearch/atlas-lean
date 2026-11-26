/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_Nat_MacaulayPow.lean`
and
`P2M/Sol/S_Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Monotone.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push

/-!
# Macaulay's upper function

`Nat.macaulayPow d a` is Macaulay's function `a^⟨d⟩`. Write the greedy `d`-binomial
expansion `a = C(k_d, d) + C(k_{d-1}, d - 1) + ⋯`, where `k_d` is the largest `k` with
`C(k, d) ≤ a` and the remaining terms expand the remainder at level `d - 1`; then
`a^⟨d⟩ = C(k_d + 1, d + 1) + C(k_{d-1} + 1, d) + ⋯`, with `a^⟨0⟩ = 0`.

## Main declarations

* `Nat.macaulayPow`: Macaulay's upper function.
* `Nat.macaulayPow_succ_eq`: the recursion through any `k` with
  `C(k, d + 1) ≤ a < C(k + 1, d + 1)`.
* `Nat.macaulayPow_mono`: `Nat.macaulayPow d` is monotone.
* `Nat.macaulayPow_succ_add_le`: the superadditivity step used in Macaulay's bound.
* `Nat.macaulayPow_sum_choose`: the value on a strict binomial cascade
  `C(a₀, 1) + C(a₁, 2) + ⋯ + C(a_{d-1}, d)` with `a₀ < a₁ < ⋯ < a_{d-1}`, the form of
  `MathlibExt.RingTheory.ProjectiveHilbertGrowth.MacaulayExpansion.successor`.

## References

* F. S. Macaulay, *Some properties of enumeration in the theory of modular systems*,
  Proc. London Math. Soc. 26 (1927), 531–555.
-/

@[expose] public section

namespace Nat

/-- **Macaulay's upper function.** `Nat.macaulayPow d a` is `a^⟨d⟩`, and `a^⟨0⟩ = 0`. At level
`d + 1`, let `k` be the largest natural number with `C(k, d + 1) ≤ a`: the top term `C(k, d + 1)`
of the greedy binomial expansion of `a` is replaced by `C(k + 1, d + 2)`, and the remainder
`a - C(k, d + 1)` is treated at level `d`. -/
def macaulayPow : ℕ → ℕ → ℕ
  | 0, _ => 0
  | d + 1, a =>
      (Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1) + 1).choose (d + 2) +
        macaulayPow d
          (a - (Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1)).choose (d + 1))

namespace MacaulayPowAux

/-- The top index of the greedy binomial expansion of `a` at level `d + 1`. -/
private def top (d a : ℕ) : ℕ := Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1)

/-- The remainder after removing the top greedy binomial term. -/
private def rem (d a : ℕ) : ℕ := a - (top d a).choose (d + 1)

private theorem macaulayPow_succ' (d a : ℕ) :
    macaulayPow (d + 1) a = (top d a + 1).choose (d + 2) + macaulayPow d (rem d a) := by
  rw [macaulayPow]; rfl

private theorem sub_le_choose (d : ℕ) : ∀ k : ℕ, k - d ≤ k.choose (d + 1)
  | 0 => by simp
  | k + 1 => by
      rw [Nat.choose_succ_succ']
      have ih := sub_le_choose d k
      rcases lt_or_ge k d with h | h
      · have : k + 1 - d = 0 := by omega
        omega
      · have hpos : 1 ≤ k.choose d := Nat.choose_pos h
        omega

private theorem choose_top_le (d a : ℕ) : (top d a).choose (d + 1) ≤ a :=
  Nat.findGreatest_spec (P := fun k => k.choose (d + 1) ≤ a) (Nat.zero_le _) (by simp)

private theorem lt_choose_of_top_lt (d a : ℕ) {k : ℕ} (hk : top d a < k) :
    a < k.choose (d + 1) := by
  rcases le_or_gt k (a + d + 1) with h | h
  · have := Nat.findGreatest_is_greatest (P := fun k => k.choose (d + 1) ≤ a) hk h
    simpa using this
  · have := sub_le_choose d k
    omega

private theorem lt_choose_top_succ (d a : ℕ) : a < (top d a + 1).choose (d + 1) :=
  lt_choose_of_top_lt d a (Nat.lt_succ_self _)

private theorem top_eq_of (d a k : ℕ) (h₁ : k.choose (d + 1) ≤ a)
    (h₂ : a < (k + 1).choose (d + 1)) : top d a = k := by
  apply le_antisymm
  · by_contra h
    push Not at h
    have : (k + 1).choose (d + 1) ≤ (top d a).choose (d + 1) := Nat.choose_le_choose _ h
    have := choose_top_le d a
    omega
  · by_contra h
    push Not at h
    have := lt_choose_of_top_lt d a h
    omega

private theorem le_top_of_choose_le (d a k : ℕ) (h : k.choose (d + 1) ≤ a) : k ≤ top d a := by
  by_contra h'
  push Not at h'
  have := lt_choose_of_top_lt d a h'
  omega

private theorem top_lt_of_lt_choose (d a k : ℕ) (h : a < k.choose (d + 1)) : top d a < k := by
  by_contra h'
  push Not at h'
  have : k.choose (d + 1) ≤ (top d a).choose (d + 1) := Nat.choose_le_choose _ h'
  have := choose_top_le d a
  omega

private theorem d_le_top (d a : ℕ) : d ≤ top d a := le_top_of_choose_le d a d (by simp)

private theorem top_zero_right (d : ℕ) : top d 0 = d := top_eq_of d 0 d (by simp) (by simp)

private theorem d_lt_top_of_pos (d a : ℕ) (ha : 0 < a) : d < top d a := by
  have := le_top_of_choose_le d a (d + 1) (by simp; omega)
  omega

private theorem top_zero_left (a : ℕ) : top 0 a = a := top_eq_of 0 a a (by simp) (by simp)

private theorem rem_zero_left (a : ℕ) : rem 0 a = 0 := by simp [rem, top_zero_left]

private theorem rem_zero_right (d : ℕ) : rem d 0 = 0 := by simp [rem]

private theorem rem_add_choose (d a : ℕ) : rem d a + (top d a).choose (d + 1) = a := by
  unfold rem; have := choose_top_le d a; omega

private theorem rem_lt (d a : ℕ) : rem d a < (top d a).choose d := by
  have h := lt_choose_top_succ d a
  rw [Nat.choose_succ_succ'] at h
  unfold rem; have := choose_top_le d a; omega

private theorem macaulayPow_lt_choose : ∀ (d m r : ℕ), r < m.choose d →
    macaulayPow d r < (m + 1).choose (d + 1)
  | 0, m, r, _ => by simp [macaulayPow]
  | d + 1, m, r, h => by
      rw [macaulayPow_succ']
      change _ < (m + 1).choose (d + 2)
      have hK : top d r < m := top_lt_of_lt_choose d r m h
      have hrem : macaulayPow d (rem d r) < (top d r + 1).choose (d + 1) :=
        macaulayPow_lt_choose d (top d r) (rem d r) (rem_lt d r)
      have h1 : (top d r + 1).choose (d + 2) + (top d r + 1).choose (d + 1) =
          (top d r + 2).choose (d + 2) := by
        rw [Nat.choose_succ_succ' (top d r + 1) (d + 1), add_comm]
      have h2 : (top d r + 2).choose (d + 2) ≤ (m + 1).choose (d + 2) :=
        Nat.choose_le_choose _ (by omega)
      omega

private theorem macaulayPow_mono' :
    ∀ (d : ℕ) {a b : ℕ}, a ≤ b → macaulayPow d a ≤ macaulayPow d b
  | 0, a, b, _ => by simp [macaulayPow]
  | d + 1, a, b, h => by
      have ht : top d a ≤ top d b := le_top_of_choose_le d b _ ((choose_top_le d a).trans h)
      rcases ht.eq_or_lt with ht | ht
      · rw [macaulayPow_succ', macaulayPow_succ', ht]
        have hr : rem d a ≤ rem d b := by
          have ha := rem_add_choose d a; have hb := rem_add_choose d b; rw [ht] at ha; omega
        have := macaulayPow_mono' d hr
        omega
      · have h1 : macaulayPow (d + 1) a < (top d a + 1 + 1).choose (d + 1 + 1) :=
          macaulayPow_lt_choose (d + 1) (top d a + 1) a (lt_choose_top_succ d a)
        have h2 : (top d a + 1 + 1).choose (d + 1 + 1) ≤ (top d b + 1).choose (d + 1 + 1) :=
          Nat.choose_le_choose _ (by omega)
        have h3 : (top d b + 1).choose (d + 1 + 1) ≤ macaulayPow (d + 1) b := by
          rw [macaulayPow_succ']; exact Nat.le_add_right _ _
        omega

private theorem macaulayPow_one' (a : ℕ) : macaulayPow 1 a = (a + 1).choose 2 := by
  rw [macaulayPow_succ', top_zero_left, rem_zero_left]; rfl

private theorem macaulayPow_zero_right' : ∀ d : ℕ, macaulayPow d 0 = 0
  | 0 => rfl
  | d + 1 => by
      rw [macaulayPow_succ', top_zero_right, rem_zero_right, macaulayPow_zero_right' d,
        Nat.choose_eq_zero_of_lt (by omega)]

private theorem top_succ_of_le (d a : ℕ) (ha : 1 ≤ a) (h : a ≤ d + 2) : top (d + 1) a = d + 2 :=
  top_eq_of (d + 1) a (d + 2) (by rw [Nat.choose_self]; exact ha)
    (by
      have : (d + 2 + 1).choose (d + 1 + 1) = d + 2 + 1 := Nat.choose_succ_self_right (d + 2)
      omega)

private theorem macaulayPow_eq_self : ∀ (d a : ℕ), a ≤ d + 1 → macaulayPow (d + 1) a = a
  | d, 0, _ => macaulayPow_zero_right' (d + 1)
  | 0, a + 1, h => by
      obtain rfl : a = 0 := by omega
      rw [macaulayPow_one']; rfl
  | d + 1, a + 1, h => by
      have ht : top (d + 1) (a + 1) = d + 2 := top_succ_of_le d (a + 1) (by omega) (by omega)
      have hr : rem (d + 1) (a + 1) = a := by simp [rem, ht]
      rw [macaulayPow_succ', ht, hr, macaulayPow_eq_self d a (by omega)]
      have : (d + 2 + 1).choose (d + 1 + 2) = 1 := by
        rw [show d + 1 + 2 = d + 2 + 1 by omega, Nat.choose_self]
      omega

/-- Macaulay's lower function: each greedy term `C(k, d + 1)` becomes `C(k - 1, d + 1)`. -/
private def low : ℕ → ℕ → ℕ
  | 0, _ => 0
  | d + 1, a => (top d a - 1).choose (d + 1) + low d (rem d a)

private theorem low_zero (a : ℕ) : low 0 a = 0 := rfl

private theorem low_succ (d a : ℕ) :
    low (d + 1) a = (top d a - 1).choose (d + 1) + low d (rem d a) := rfl

private theorem low_zero_right : ∀ d : ℕ, low d 0 = 0
  | 0 => rfl
  | d + 1 => by
      rw [low_succ, top_zero_right, rem_zero_right, low_zero_right d,
        Nat.choose_eq_zero_of_lt (by omega)]

private theorem low_eq_zero : ∀ (d a : ℕ), a ≤ d + 1 → low (d + 1) a = 0
  | d, 0, _ => low_zero_right _
  | 0, a + 1, h => by
      obtain rfl : a = 0 := by omega
      rw [low_succ, top_zero_left, low_zero]; rfl
  | d + 1, a + 1, h => by
      have ht : top (d + 1) (a + 1) = d + 2 := top_succ_of_le d (a + 1) (by omega) (by omega)
      have hr : rem (d + 1) (a + 1) = a := by simp [rem, ht]
      rw [low_succ, ht, hr, low_eq_zero d a (by omega), Nat.choose_eq_zero_of_lt (by omega)]

private theorem choose_pred_add (T d : ℕ) (hT : 1 ≤ T) :
    (T - 1).choose (d + 1) + (T - 1).choose d = T.choose (d + 1) := by
  have := Nat.choose_succ_succ' (T - 1) d
  rw [Nat.sub_add_cancel hT] at this
  rw [add_comm]; exact this.symm

private theorem low_lt_choose : ∀ (d m r : ℕ), r < (m + 1).choose (d + 1) → d + 1 ≤ m →
    low (d + 1) r < m.choose (d + 1)
  | 0, m, r, h, hm => by
      rw [low_succ, top_zero_left, low_zero]
      simp only [zero_add, Nat.choose_one_right, add_zero] at h ⊢
      omega
  | d + 1, m, r, h, hm => by
      rw [low_succ]
      change (top (d + 1) r - 1).choose (d + 2) + low (d + 1) (rem (d + 1) r) <
        m.choose (d + 2)
      have hT : top (d + 1) r ≤ m :=
        Nat.lt_succ_iff.1 (top_lt_of_lt_choose (d + 1) r (m + 1) h)
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr
        rw [top_zero_right, rem_zero_right, low_zero_right, Nat.choose_eq_zero_of_lt (by omega),
          zero_add]
        exact Nat.choose_pos (by omega)
      · have hT' : d + 1 < top (d + 1) r := d_lt_top_of_pos _ _ hr
        have hRlt : rem (d + 1) r < (top (d + 1) r - 1 + 1).choose (d + 1) := by
          rw [Nat.sub_add_cancel (by omega)]; exact rem_lt (d + 1) r
        have ih := low_lt_choose d (top (d + 1) r - 1) (rem (d + 1) r) hRlt (by omega)
        have h1 : (top (d + 1) r - 1).choose (d + 2) + (top (d + 1) r - 1).choose (d + 1) =
            (top (d + 1) r).choose (d + 2) := choose_pred_add (top (d + 1) r) (d + 1) (by omega)
        have h2 : (top (d + 1) r).choose (d + 2) ≤ m.choose (d + 2) := Nat.choose_le_choose _ hT
        omega

private theorem macaulayPow_low_add : ∀ (d a : ℕ),
    macaulayPow (d + 1) (low (d + 1) a) + a = macaulayPow (d + 1) a
  | 0, a => by
      rw [low_succ, top_zero_left, low_zero, add_zero, macaulayPow_one', macaulayPow_one',
        Nat.choose_one_right]
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · rfl
      · have h2 : (a + 1).choose 2 = a + a.choose 2 := by
          have := Nat.choose_succ_succ' a 1; rw [Nat.choose_one_right] at this; exact this
        rw [Nat.sub_add_cancel ha]; omega
  | d + 1, a => by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · rw [low_zero_right, add_zero]
      · set T := top (d + 1) a with hT
        set R := rem (d + 1) a with hR
        have hTd : d + 1 < T := d_lt_top_of_pos _ _ ha
        have hRa : R + T.choose (d + 2) = a := rem_add_choose (d + 1) a
        have hRlt : R < T.choose (d + 1) := rem_lt (d + 1) a
        have ih := macaulayPow_low_add d R
        rw [low_succ, macaulayPow_succ' (d + 1) a]
        change macaulayPow (d + 2) ((T - 1).choose (d + 2) + low (d + 1) R) + a =
          (T + 1).choose (d + 3) + macaulayPow (d + 1) R
        rcases (show T = d + 2 ∨ d + 3 ≤ T by omega) with hT2 | hT3
        · have hC : (d + 2).choose (d + 1) = d + 2 := Nat.choose_succ_self_right (d + 1)
          have hR1 : R ≤ d + 1 := by rw [hT2] at hRlt; omega
          rw [hT2, show d + 2 - 1 = d + 1 from rfl, Nat.choose_succ_self, zero_add,
            low_eq_zero d R hR1, macaulayPow_zero_right', macaulayPow_eq_self d R hR1,
            Nat.choose_self]
          rw [hT2, Nat.choose_self] at hRa
          omega
        · have hlow : low (d + 1) R < (T - 1).choose (d + 1) :=
            low_lt_choose d (T - 1) R (by rw [Nat.sub_add_cancel (by omega)]; exact hRlt)
              (by omega)
          have hpasc : (T - 1).choose (d + 2) + (T - 1).choose (d + 1) = T.choose (d + 2) :=
            choose_pred_add T (d + 1) (by omega)
          have hpasc' : T.choose (d + 3) + T.choose (d + 2) = (T + 1).choose (d + 3) := by
            rw [Nat.choose_succ_succ' T (d + 2), add_comm]
          have htop : top (d + 1) ((T - 1).choose (d + 2) + low (d + 1) R) = T - 1 :=
            top_eq_of (d + 1) _ (T - 1) (Nat.le_add_right _ _)
              (by
                rw [Nat.sub_add_cancel (show 1 ≤ T by omega)]
                change _ < T.choose (d + 2)
                omega)
          have hrem :
              rem (d + 1) ((T - 1).choose (d + 2) + low (d + 1) R) = low (d + 1) R := by
            simp [rem, htop]
          rw [macaulayPow_succ', htop, hrem, Nat.sub_add_cancel (show 1 ≤ T by omega)]
          change T.choose (d + 3) + macaulayPow (d + 1) (low (d + 1) R) + a = _
          omega

private theorem le_choose_add_low :
    ∀ (d m r : ℕ), r < (m + 1).choose (d + 1) → r ≤ m.choose d + low (d + 1) r
  | 0, m, r, _ => by
      rw [low_succ, top_zero_left, low_zero, Nat.choose_zero_right, Nat.choose_one_right]
      omega
  | d + 1, m, r, h => by
      rw [low_succ]
      change r ≤ m.choose (d + 1) +
        ((top (d + 1) r - 1).choose (d + 2) + low (d + 1) (rem (d + 1) r))
      have hT : top (d + 1) r ≤ m :=
        Nat.lt_succ_iff.1 (top_lt_of_lt_choose (d + 1) r (m + 1) h)
      have hT1 : 1 ≤ top (d + 1) r := by have := d_le_top (d + 1) r; omega
      have hRa : rem (d + 1) r + (top (d + 1) r).choose (d + 2) = r := rem_add_choose (d + 1) r
      have hRlt : rem (d + 1) r < (top (d + 1) r - 1 + 1).choose (d + 1) := by
        rw [Nat.sub_add_cancel hT1]; exact rem_lt (d + 1) r
      have ih := le_choose_add_low d (top (d + 1) r - 1) (rem (d + 1) r) hRlt
      have h1 : (top (d + 1) r - 1).choose (d + 2) + (top (d + 1) r - 1).choose (d + 1) =
          (top (d + 1) r).choose (d + 2) := choose_pred_add (top (d + 1) r) (d + 1) hT1
      have h2 := choose_pred_add (top (d + 1) r) d hT1
      have h3 : (top (d + 1) r).choose (d + 1) ≤ m.choose (d + 1) := Nat.choose_le_choose _ hT
      omega

private theorem le_add_low : ∀ (d a s : ℕ), a ≤ macaulayPow d s → a ≤ s + low (d + 1) a
  | 0, a, s, h => by simp only [macaulayPow] at h; omega
  | d + 1, a, s, h => by
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · exact Nat.zero_le _
      set T := top (d + 1) a with hT
      set R := rem (d + 1) a with hR
      have hTd : d + 1 < T := d_lt_top_of_pos _ _ ha
      have hRa : R + T.choose (d + 2) = a := rem_add_choose (d + 1) a
      have hRlt : R < T.choose (d + 1) := rem_lt (d + 1) a
      set T' := top d s with hT'
      have hs : rem d s + T'.choose (d + 1) = s := rem_add_choose d s
      have hlt : macaulayPow (d + 1) s < (T' + 1 + 1).choose (d + 1 + 1) :=
        macaulayPow_lt_choose (d + 1) (T' + 1) s (lt_choose_top_succ d s)
      have hTT' : T ≤ T' + 1 := by
        have := top_lt_of_lt_choose (d + 1) a (T' + 1 + 1) (h.trans_lt hlt); omega
      rw [low_succ]
      change a ≤ s + ((T - 1).choose (d + 2) + low (d + 1) R)
      have hpasc : (T - 1).choose (d + 2) + (T - 1).choose (d + 1) = T.choose (d + 2) :=
        choose_pred_add T (d + 1) (by omega)
      rcases (show T ≤ T' ∨ T = T' + 1 by omega) with hle | heq
      · have h1 : T.choose (d + 1) ≤ T'.choose (d + 1) := Nat.choose_le_choose _ hle
        have h2 : R ≤ (T - 1).choose d + low (d + 1) R :=
          le_choose_add_low d (T - 1) R (by rw [Nat.sub_add_cancel (by omega)]; exact hRlt)
        have h3 := choose_pred_add T d (by omega)
        omega
      · have hμ : macaulayPow (d + 1) s = (T' + 1).choose (d + 2) + macaulayPow d (rem d s) :=
          macaulayPow_succ' d s
        rw [← heq] at hμ
        rw [show T' = T - 1 by omega] at hs
        have hR' : R ≤ macaulayPow d (rem d s) := by omega
        have ih := le_add_low d R (rem d s) hR'
        omega

/-- A strict binomial cascade whose upper indices are all below `b` sums to less than
`C(b, d)`. -/
private theorem sum_choose_lt_choose : ∀ (d b : ℕ) (a : Fin d → ℕ), StrictMono a →
    (∀ i, a i < b) → ∑ i, (a i).choose (i.val + 1) < b.choose d
  | 0, b, a, _, _ => by simp
  | d + 1, b, a, ha, hb => by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hlow := sum_choose_lt_choose d (a (Fin.last d)) (fun i => a i.castSucc)
        (ha.comp Fin.strictMono_castSucc) (fun i => ha (Fin.castSucc_lt_last i))
      have h1 := Nat.choose_succ_succ' (a (Fin.last d)) d
      have h2 : (a (Fin.last d) + 1).choose (d + 1) ≤ b.choose (d + 1) :=
        Nat.choose_le_choose _ (hb (Fin.last d))
      omega

end MacaulayPowAux

open MacaulayPowAux

@[simp]
theorem macaulayPow_zero_left (a : ℕ) : macaulayPow 0 a = 0 := rfl

@[simp]
theorem macaulayPow_zero_right (d : ℕ) : macaulayPow d 0 = 0 := macaulayPow_zero_right' d

theorem macaulayPow_one (a : ℕ) : macaulayPow 1 a = (a + 1).choose 2 := macaulayPow_one' a

/-- **Recursion of Macaulay's upper function.** For any `k` with
`C(k, d + 1) ≤ a < C(k + 1, d + 1)`, the term `C(k, d + 1)` is replaced by `C(k + 1, d + 2)` and
the remainder is treated at level `d`: `a^⟨d+1⟩ = C(k + 1, d + 2) + (a - C(k, d + 1))^⟨d⟩`. -/
theorem macaulayPow_succ_eq (d a k : ℕ) (h₁ : k.choose (d + 1) ≤ a)
    (h₂ : a < (k + 1).choose (d + 1)) :
    macaulayPow (d + 1) a = (k + 1).choose (d + 2) + macaulayPow d (a - k.choose (d + 1)) := by
  rw [macaulayPow_succ', rem, top_eq_of d a k h₁ h₂]

/-- **Macaulay's upper function below the first binomial block.** If `a ≤ d + 1`, then
`a^⟨d+1⟩ = a`. -/
theorem macaulayPow_succ_of_le (d a : ℕ) (h : a ≤ d + 1) : macaulayPow (d + 1) a = a :=
  macaulayPow_eq_self d a h

theorem macaulayPow_mono (d : ℕ) : Monotone (macaulayPow d) := fun _ _ h =>
  macaulayPow_mono' d h

/-- **Superadditivity step for Macaulay's upper function.** If `b + s ≤ s^⟨d⟩`, then
`b^⟨d+1⟩ + (b + s) ≤ (b + s)^⟨d+1⟩`; this is the step behind Macaulay's bound. -/
theorem macaulayPow_succ_add_le (d b s : ℕ) (h : b + s ≤ macaulayPow d s) :
    macaulayPow (d + 1) b + (b + s) ≤ macaulayPow (d + 1) (b + s) := by
  have h1 : b ≤ low (d + 1) (b + s) := by have := le_add_low d (b + s) s h; omega
  have h2 := macaulayPow_mono' (d + 1) h1
  have h3 := macaulayPow_low_add d (b + s)
  omega

/-- **Macaulay's upper function on a binomial cascade.** For natural numbers
`a₀ < a₁ < ⋯ < a_{d-1}`, `(∑_{i<d} C(aᵢ, i + 1))^⟨d⟩ = ∑_{i<d} C(aᵢ + 1, i + 2)`. -/
theorem macaulayPow_sum_choose : ∀ (d : ℕ) (a : Fin d → ℕ), StrictMono a →
    macaulayPow d (∑ i, (a i).choose (i.val + 1)) = ∑ i, (a i + 1).choose (i.val + 2)
  | 0, a, _ => by simp
  | d + 1, a, ha => by
      have hlow := sum_choose_lt_choose d (a (Fin.last d)) (fun i => a i.castSucc)
        (ha.comp Fin.strictMono_castSucc) (fun i => ha (Fin.castSucc_lt_last i))
      have ih := macaulayPow_sum_choose d (fun i => a i.castSucc) (ha.comp Fin.strictMono_castSucc)
      have h1 := Nat.choose_succ_succ' (a (Fin.last d)) d
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last] at ih ⊢
      rw [macaulayPow_succ_eq d _ (a (Fin.last d)) (Nat.le_add_left _ _) (by omega),
        Nat.add_sub_cancel, ih, add_comm]

end Nat
