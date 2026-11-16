/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Logic.Function.Basic

/-!
# Linear probing

Insertion and lookup probe consecutive slots modulo the
table size. Successful insertion stores the key at a probed
slot, and lookup with the same fuel finds it. Expected-cost
analysis is not included here.
-/

@[expose] public section

/-- Linear probing with natural slot arithmetic (ALG-57
core). The table is `ℕ → Option ℕ` used at slots `< m`;
`h x` is the home slot (assumed `< m` where used). Insert
probes `(h x + off) % m` for `off = 0, 1, ...` up to fuel. -/
def probeInsert (m : ℕ) (h : ℕ → ℕ) (x : ℕ) :
    ℕ → ℕ → (ℕ → Option ℕ) → Option (ℕ → Option ℕ)
  | 0, _, _ => none
  | fuel + 1, off, t =>
      let slot := (h x + off) % m
      match t slot with
      | none => some (Function.update t slot (some x))
      | some y =>
          if y = x then some t
          else probeInsert m h x fuel (off + 1) t

/-- Lookup probes the same sequence and stops at the key,
an empty slot, or fuel exhaustion. -/
def probeLookup (m : ℕ) (h : ℕ → ℕ) (x : ℕ) :
    ℕ → ℕ → (ℕ → Option ℕ) → Bool
  | 0, _, _ => false
  | fuel + 1, off, t =>
      let slot := (h x + off) % m
      match t slot with
      | none => false
      | some y => if y = x then true else probeLookup m h x fuel (off + 1) t

private theorem probeInsert_zero (m : ℕ) (h : ℕ → ℕ) (x off : ℕ)
    (t : ℕ → Option ℕ) : probeInsert m h x 0 off t = none := rfl

private theorem probeInsert_succ (m : ℕ) (h : ℕ → ℕ) (x fuel off : ℕ)
    (t : ℕ → Option ℕ) :
    probeInsert m h x (fuel + 1) off t =
      match t ((h x + off) % m) with
      | none => some (Function.update t ((h x + off) % m) (some x))
      | some y => if y = x then some t else probeInsert m h x fuel (off + 1) t :=
  rfl

private theorem probeLookup_succ (m : ℕ) (h : ℕ → ℕ) (x fuel off : ℕ)
    (t : ℕ → Option ℕ) :
    probeLookup m h x (fuel + 1) off t =
      match t ((h x + off) % m) with
      | none => false
      | some y => if y = x then true else probeLookup m h x fuel (off + 1) t :=
  rfl

private theorem probeInsert_preserves (m : ℕ) (h : ℕ → ℕ) (x : ℕ)
    (fuel off : ℕ) (t t' : ℕ → Option ℕ) (s y : ℕ)
    (hins : probeInsert m h x fuel off t = some t')
    (hocc : t s = some y) : t' s = some y := by
  induction fuel generalizing off t with
  | zero => rw [probeInsert_zero] at hins; cases hins
  | succ fuel ih =>
      cases hts : t ((h x + off) % m) with
      | none =>
          rw [probeInsert_succ] at hins
          simp only [hts, Option.some.injEq] at hins
          subst hins
          by_cases hs : s = (h x + off) % m
          · subst hs; rw [hts] at hocc; cases hocc
          · rw [Function.update_of_ne hs]
            exact hocc
      | some y =>
          rw [probeInsert_succ] at hins
          simp only [hts] at hins
          by_cases hyeq : y = x
          · rw [ite_eq_left hyeq, Option.some.injEq] at hins
            subst hins
            exact hocc
          · rw [ite_eq_right hyeq] at hins
            exact ih _ _ hins hocc

/-- If insertion succeeds into `t'`, the key is stored at a
probed slot: `t'` agrees with `t` except possibly at probe
slots, and `x` is present. Stated as: some probed slot of
the final table holds `x`. -/
theorem probeInsert_stored (m : ℕ) (h : ℕ → ℕ) (x : ℕ)
    (fuel off : ℕ) (t t' : ℕ → Option ℕ)
    (hins : probeInsert m h x fuel off t = some t') :
    ∃ d < fuel, t' ((h x + off + d) % m) = some x := by
  induction fuel generalizing off t with
  | zero => rw [probeInsert_zero] at hins; cases hins
  | succ fuel ih =>
      cases hts : t ((h x + off) % m) with
      | none =>
          rw [probeInsert_succ] at hins
          simp only [hts, Option.some.injEq] at hins
          subst hins
          refine ⟨0, Nat.zero_lt_succ fuel, ?_⟩
          rw [Nat.add_zero]
          exact Function.update_self _ _ _
      | some y =>
          rw [probeInsert_succ] at hins
          simp only [hts] at hins
          by_cases hyeq : y = x
          · rw [ite_eq_left hyeq, Option.some.injEq] at hins
            subst hins
            refine ⟨0, Nat.zero_lt_succ fuel, ?_⟩
            rw [Nat.add_zero, hts, hyeq]
          · rw [ite_eq_right hyeq] at hins
            obtain ⟨d, hdfuel, hstored⟩ := ih _ _ hins
            refine ⟨d + 1, Nat.succ_lt_succ hdfuel, ?_⟩
            have hEq : h x + off + (d + 1) = h x + (off + 1) + d := by omega
            rw [hEq]
            exact hstored

/-- Lookup finds a key that insertion placed, provided the
probe path was not disturbed: if `t'` came from inserting
`x` into `t` and lookup runs with at least as much fuel
from the same offset, it returns true. -/
theorem probeLookup_of_insert (m : ℕ) (h : ℕ → ℕ) (x : ℕ)
    (fuel off : ℕ) (t t' : ℕ → Option ℕ)
    (hins : probeInsert m h x fuel off t = some t') :
    probeLookup m h x fuel off t' = true := by
  induction fuel generalizing off t with
  | zero => rw [probeInsert_zero] at hins; cases hins
  | succ fuel ih =>
      cases hts : t ((h x + off) % m) with
      | none =>
          rw [probeInsert_succ] at hins
          simp only [hts, Option.some.injEq] at hins
          subst hins
          have hsl : Function.update t ((h x + off) % m) (some x) ((h x + off) % m)
              = some x := Function.update_self _ _ _
          rw [probeLookup_succ, hsl]
          exact ite_eq_left rfl
      | some y =>
          rw [probeInsert_succ] at hins
          simp only [hts] at hins
          by_cases hyeq : y = x
          · rw [ite_eq_left hyeq, Option.some.injEq] at hins
            subst hins
            rw [probeLookup_succ, hts]
            show (if y = x then true else probeLookup m h x fuel (off + 1) t) = true
            rw [ite_eq_left hyeq]
          · rw [ite_eq_right hyeq] at hins
            have hts' : t' ((h x + off) % m) = some y :=
              probeInsert_preserves m h x fuel (off + 1) t t' _ _ hins hts
            have ih' : probeLookup m h x fuel (off + 1) t' = true := ih _ _ hins
            rw [probeLookup_succ, hts']
            show (if y = x then true else probeLookup m h x fuel (off + 1) t') = true
            rw [ite_eq_right hyeq]
            exact ih'

end
