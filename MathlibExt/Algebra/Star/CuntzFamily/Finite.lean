/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.PNat.Basic

/-!
# Finite Cuntz families from a binary family

The singleton family is `1`. Each step splits only the last leaf `u` into
`u * v₀, u * v₁`, retaining every earlier leaf. Both Cuntz laws are proved
over a unital star semiring, including its zero case. No norm, completion,
representation, finite-family outcome assumption or global instance is used.
-/

@[expose] public section

open scoped BigOperators

namespace CuntzFamily

universe u

variable {R : Type u}

/-- The actual binary leaf-splitting family, with positive size `n+1`. -/
def ofBinary [Mul R] [One R] (v : Fin 2 → R) : (n : ℕ) → Fin (n + 1) → R
  | 0 => fun _ => 1
  | n + 1 =>
      let f := ofBinary v n
      let u := f (Fin.last n)
      Fin.snoc (Fin.snoc (fun i : Fin n => f i.castSucc) (u * v 0)) (u * v 1)

/-- The same computed family on an explicitly positive finite index. -/
def ofBinaryPositive [Mul R] [One R] (v : Fin 2 → R) (N : ℕ+) : Fin N → R :=
  ofBinary v N.natPred ∘ (finCongr N.natPred_add_one).symm

/-- Positive size one is the literal singleton family `1`. -/
theorem ofBinaryPositive_one [Mul R] [One R] (v : Fin 2 → R) (i : Fin 1) :
    ofBinaryPositive v 1 i = 1 :=
  rfl

/-- The first split recovers the supplied binary family in its original order. -/
theorem ofBinary_one [MulOneClass R] (v : Fin 2 → R) (i : Fin 2) :
    ofBinary v 1 i = v i := by
  cases i using Fin.lastCases with
  | last =>
      change (Fin.snoc (Fin.snoc (fun _ : Fin 0 => (1 : R)) (1 * v 0) : Fin 1 → R)
        (1 * v 1) : Fin 2 → R) (Fin.last 1) = v (Fin.last 1)
      rw [Fin.snoc_last, one_mul]
      rfl
  | cast i =>
      have hi : i = Fin.last 0 := Subsingleton.elim _ _
      subst i
      change (Fin.snoc (Fin.snoc (fun _ : Fin 0 => (1 : R)) (1 * v 0) : Fin 1 → R)
        (1 * v 1) : Fin 2 → R) ((Fin.last 0).castSucc) = v ((Fin.last 0).castSucc)
      rw [Fin.snoc_castSucc, Fin.snoc_last, one_mul]
      rfl

/-- Positive size two recovers the supplied binary family. -/
theorem ofBinaryPositive_two [MulOneClass R] (v : Fin 2 → R) (i : Fin 2) :
    ofBinaryPositive v 2 i = v i := by
  change ofBinary v 1 i = v i
  exact ofBinary_one v i

/-- Both finite Cuntz laws are preserved by the constructive last-leaf split. -/
theorem ofBinary_relations [Semiring R] [StarRing R] (v : Fin 2 → R)
    (hOrth : ∀ i j : Fin 2, star (v i) * v j = if i = j then 1 else 0)
    (hPartition : v 0 * star (v 0) + v 1 * star (v 1) = 1) (n : ℕ) :
    (∀ i j : Fin (n + 1),
      star (ofBinary v n i) * ofBinary v n j = if i = j then 1 else 0) ∧
    (∑ i : Fin (n + 1), ofBinary v n i * star (ofBinary v n i)) = 1 := by
  induction n with
  | zero =>
      constructor
      · intro i j
        have hij : i = j := by
          have hi : i = 0 := Fin.eq_zero i
          have hj : j = 0 := Fin.eq_zero j
          exact hi.trans hj.symm
        simp [ofBinary, hij]
      · simp [ofBinary]
  | succ n ih =>
      rcases ih with ⟨hGram, hSum⟩
      let f : Fin (n + 1) → R := ofBinary v n
      let u : R := f (Fin.last n)
      let g : Fin (n + 2) → R :=
        Fin.snoc (Fin.snoc (fun i : Fin n => f i.castSucc) (u * v 0)) (u * v 1)
      have hUU : star u * u = 1 := by
        simpa [f, u] using hGram (Fin.last n) (Fin.last n)
      have hOldLast (i : Fin n) : star (f i.castSucc) * u = 0 := by
        simpa [f, u] using hGram i.castSucc (Fin.last n)
      have hLastOld (i : Fin n) : star u * f i.castSucc = 0 := by
        simpa [f, u, Ne.symm (Fin.castSucc_ne_last i)] using
          hGram (Fin.last n) i.castSucc
      have hOldSplit (i : Fin n) (ε : Fin 2) :
          star (f i.castSucc) * (u * v ε) = 0 := by
        calc
          _ = (star (f i.castSucc) * u) * v ε := (mul_assoc _ _ _).symm
          _ = 0 := by rw [hOldLast, zero_mul]
      have hSplitOld (ε : Fin 2) (i : Fin n) :
          star (u * v ε) * f i.castSucc = 0 := by
        rw [star_mul, mul_assoc, hLastOld, mul_zero]
      have hSplitGram (ε δ : Fin 2) :
          star (u * v ε) * (u * v δ) = if ε = δ then 1 else 0 := by
        calc
          _ = star (v ε) * (star u * u) * v δ := by
            simp only [star_mul, mul_assoc]
          _ = star (v ε) * v δ := by rw [hUU, mul_one]
          _ = if ε = δ then 1 else 0 := hOrth ε δ
      have hSplitSum :
          (u * v 0) * star (u * v 0) + (u * v 1) * star (u * v 1) =
            u * star u := by
        calc
          _ = u * (v 0 * star (v 0) + v 1 * star (v 1)) * star u := by
            simp only [star_mul, mul_add, add_mul, mul_assoc]
          _ = u * star u := by rw [hPartition, mul_one]
      have hPrefix :
          (∑ i : Fin n, f i.castSucc * star (f i.castSucc)) + u * star u = 1 := by
        simpa only [f, u, Fin.sum_univ_castSucc] using hSum
      change (∀ i j : Fin (n + 2), star (g i) * g j = if i = j then 1 else 0) ∧
        (∑ i : Fin (n + 2), g i * star (g i)) = 1
      constructor
      · intro i j
        cases i using Fin.lastCases with
        | last =>
            cases j using Fin.lastCases with
            | last => simpa [g] using hSplitGram 1 1
            | cast j =>
                cases j using Fin.lastCases with
                | last =>
                    simpa [g, Ne.symm (Fin.castSucc_ne_last (Fin.last n))] using hSplitGram 1 0
                | cast j =>
                    simpa [g, Ne.symm (Fin.castSucc_ne_last j.castSucc)] using
                      hSplitOld 1 j
        | cast i =>
            cases i using Fin.lastCases with
            | last =>
                cases j using Fin.lastCases with
                | last => simpa [g] using hSplitGram 0 1
                | cast j =>
                    cases j using Fin.lastCases with
                    | last => simpa [g] using hSplitGram 0 0
                    | cast j =>
                        simpa [g, Ne.symm (Fin.castSucc_ne_last j)] using hSplitOld 0 j
            | cast i =>
                cases j using Fin.lastCases with
                | last => simpa [g] using hOldSplit i 1
                | cast j =>
                    cases j using Fin.lastCases with
                    | last => simpa [g] using hOldSplit i 0
                    | cast j => simpa [g] using hGram i.castSucc j.castSucc
      · calc
          (∑ i : Fin (n + 2), g i * star (g i)) =
              ((∑ i : Fin n, f i.castSucc * star (f i.castSucc)) +
                (u * v 0) * star (u * v 0)) + (u * v 1) * star (u * v 1) := by
            simp only [g, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
          _ = (∑ i : Fin n, f i.castSucc * star (f i.castSucc)) + u * star u := by
            rw [add_assoc, hSplitSum]
          _ = 1 := hPrefix

/-- The actual positive-size family has both Cuntz laws, without any output
family assumption. -/
theorem ofBinaryPositive_relations [Semiring R] [StarRing R] (v : Fin 2 → R)
    (hOrth : ∀ i j : Fin 2, star (v i) * v j = if i = j then 1 else 0)
    (hPartition : v 0 * star (v 0) + v 1 * star (v 1) = 1) (N : ℕ+) :
    (∀ i j : Fin N,
      star (ofBinaryPositive v N i) * ofBinaryPositive v N j = if i = j then 1 else 0) ∧
    (∑ i : Fin N, ofBinaryPositive v N i * star (ofBinaryPositive v N i)) = 1 := by
  have h := ofBinary_relations v hOrth hPartition N.natPred
  let e : Fin N ≃ Fin (N.natPred + 1) := (finCongr N.natPred_add_one).symm
  constructor
  · intro i j
    change star (ofBinary v N.natPred (e i)) * ofBinary v N.natPred (e j) =
      if i = j then 1 else 0
    rw [h.1]
    by_cases hij : i = j
    · simp [hij]
    · have heij : e i ≠ e j := fun he => hij (e.injective he)
      simp [hij, heij]
  · change (∑ i : Fin N,
      ofBinary v N.natPred (e i) * star (ofBinary v N.natPred (e i))) = 1
    exact (e.sum_comp (fun j => ofBinary v N.natPred j * star (ofBinary v N.natPred j))).trans
      h.2

end CuntzFamily
