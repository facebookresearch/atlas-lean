/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Pi

@[expose] public section

namespace MetaMathlibExt

/-! # Parking functions

This file provides the threshold formulation of partial and ordinary parking
functions. It gives a direct finite decision procedure. In the ordinary case,
the predicate is equivalent to the usual formulation in which the sorted
preferences lie below the identity; for `s` cars and `t` spots, the analogous
partial sorted bound is shifted to `bᵢ ≤ t - s + i`.
-/

/-- **Partial parking function.** Let $s, t \in \mathbb{N}$ and number the $t$ spots
$0, \dots, t-1$. A map $f : \{0, \dots, s-1\} \to \{0, \dots, t-1\}$, giving the preferred spot
of each of $s$ cars, is a partial parking function if for every spot $k \in \{0, \dots, t-1\}$,
at most $t - k$ cars $i$ satisfy $f(i) \ge k$. -/
def IsPartialParkingFunction (s t : ℕ) (f : Fin s → Fin t) : Prop :=
  ∀ k : Fin t,
    (Finset.univ.filter (fun i => k ≤ f i)).card ≤ t - (k : ℕ)

/-- **Parking function.** Let $n \in \mathbb{N}$ and number the $n$ spots $0, \dots, n-1$.
A map $f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$, giving the preferred spot of each of
$n$ cars, is a parking function if it is a partial parking function with $n$ cars and $n$
spots, that is, if for every spot $k$, at most $n - k$ cars $i$ satisfy $f(i) \ge k$. -/
def IsParkingFunction (n : ℕ) (f : Fin n → Fin n) : Prop :=
  IsPartialParkingFunction n n f

instance (s t : ℕ) (f : Fin s → Fin t) :
    Decidable (IsPartialParkingFunction s t f) := by
  unfold IsPartialParkingFunction
  infer_instance

instance (n : ℕ) (f : Fin n → Fin n) : Decidable (IsParkingFunction n f) := by
  unfold IsParkingFunction
  infer_instance

/-- **Lower-tail characterization of parking functions.** Let $n \in \mathbb{N}$, number
the $n$ spots $0, \dots, n-1$, and let $f : \{0, \dots, n-1\} \to \{0, \dots, n-1\}$ give the
preferred spot of each of $n$ cars. Then $f$ is a parking function if and only if, for every
spot $k \in \{0, \dots, n-1\}$, at least $k + 1$ cars $i$ satisfy $f(i) \le k$. -/
theorem isParkingFunction_iff_card_filter_le (n : ℕ) (f : Fin n → Fin n) :
    IsParkingFunction n f ↔
      ∀ k : Fin n,
        k.val + 1 ≤ (Finset.univ.filter (fun i : Fin n ↦ f i ≤ k)).card := by
  constructor
  · intro hf k
    unfold IsParkingFunction IsPartialParkingFunction at hf
    by_cases hk : k.val + 1 < n
    · let l : Fin n := ⟨k.val + 1, hk⟩
      have hl := hf l
      have hpart :
          (Finset.univ.filter (fun i : Fin n ↦ f i ≤ k)).card +
              (Finset.univ.filter (fun i : Fin n ↦ ¬f i ≤ k)).card = n := by
        simpa using
          (Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset (Fin n))) (fun i : Fin n ↦ f i ≤ k))
      have hfilter :
          Finset.univ.filter (fun i : Fin n ↦ ¬f i ≤ k) =
            Finset.univ.filter (fun i : Fin n ↦ l ≤ f i) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        change (¬(f i).val ≤ k.val) ↔ k.val + 1 ≤ (f i).val
        omega
      rw [hfilter] at hpart
      change
        (Finset.univ.filter (fun i : Fin n ↦ l ≤ f i)).card ≤ n - (k.val + 1) at hl
      omega
    · have hfilter :
          Finset.univ.filter (fun i : Fin n ↦ f i ≤ k) = Finset.univ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro
          trivial
        · intro
          change (f i).val ≤ k.val
          omega
      rw [hfilter, Finset.card_univ, Fintype.card_fin]
      omega
  · intro hf
    unfold IsParkingFunction IsPartialParkingFunction
    intro k
    by_cases hk : k.val = 0
    · calc
        (Finset.univ.filter (fun i : Fin n ↦ k ≤ f i)).card ≤
            (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
        _ = n := Fintype.card_fin n
        _ = n - k.val := by omega
    · let p : Fin n := ⟨k.val - 1, by omega⟩
      have hp := hf p
      have hpart :
          (Finset.univ.filter (fun i : Fin n ↦ f i ≤ p)).card +
              (Finset.univ.filter (fun i : Fin n ↦ ¬f i ≤ p)).card = n := by
        simpa using
          (Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset (Fin n))) (fun i : Fin n ↦ f i ≤ p))
      have hfilter :
          Finset.univ.filter (fun i : Fin n ↦ ¬f i ≤ p) =
            Finset.univ.filter (fun i : Fin n ↦ k ≤ f i) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        change (¬(f i).val ≤ k.val - 1) ↔ k.val ≤ (f i).val
        omega
      rw [hfilter] at hpart
      change
        k.val - 1 + 1 ≤
          (Finset.univ.filter (fun i : Fin n ↦ f i ≤ p)).card at hp
      omega

end MetaMathlibExt
