/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Powerset

/-!
# Union bound over witness sets on a finite probability space

On a finite space with nonnegative weights `μ`, suppose every outcome with `K ω ≥ n` has a witness
set `S ⊆ Fin h` of size `n`, and every size-`n` witness event has mass at most `aⁿ`. Then
`μ(K ≥ n) ≤ C(h, n) aⁿ`.

## Main definitions

* `StatMech.Probability.finiteEventMass`: the `μ`-mass of an event on a finite space.

## Main results

* `StatMech.Probability.finiteEventMass_tail_le_choose_mul_pow`.
-/

@[expose] public section

open Finset Set
open scoped BigOperators

namespace StatMech.Probability

/-- The mass `∑_{ω ∈ A} μ ω` of an event on a finite space. -/
noncomputable def finiteEventMass {Omega : Type*} [Fintype Omega]
    (mu : Omega -> Real) (A : Set Omega) : Real := by
  classical
  exact ∑ omega, if omega ∈ A then mu omega else 0

/-- Union bound over witness sets: `μ(K ≥ n) ≤ C(h, n) aⁿ` if every outcome with `K ≥ n` has a
witness set of size `n` and each witness event of size `n` has mass at most `aⁿ`. -/
theorem finiteEventMass_tail_le_choose_mul_pow
    {Omega : Type*} [Fintype Omega]
    (mu : Omega -> Real) (hmu : forall omega, 0 <= mu omega)
    (K : Omega -> Nat) (h n : Nat) (a : Real)
    (Witness : Finset (Fin h) -> Omega -> Prop)
    (hcover : forall omega, n <= K omega ->
      exists S : Finset (Fin h), S.card = n /\ Witness S omega)
    (hmass : forall S : Finset (Fin h), S.card = n ->
      finiteEventMass mu {omega | Witness S omega} <= a ^ n) :
    finiteEventMass mu {omega | n <= K omega} <=
      Nat.choose h n * a ^ n := by
  classical
  let subsets : Finset (Finset (Fin h)) :=
    (Finset.univ : Finset (Fin h)).powersetCard n
  have hpoint (omega : Omega) :
      (if n <= K omega then mu omega else 0) <=
        subsets.sum (fun S => if Witness S omega then mu omega else 0) := by
    by_cases htail : n <= K omega
    · rw [ite_eq_left htail]
      obtain ⟨S, hcard, hW⟩ := hcover omega htail
      have hS : S ∈ subsets := by
        simp [subsets, hcard]
      have hle : (if Witness S omega then mu omega else 0) <=
          subsets.sum (fun T => if Witness T omega then mu omega else 0) := by
        exact Finset.single_le_sum (s := subsets)
          (f := fun T => if Witness T omega then mu omega else 0)
          (fun T _ => by
            by_cases hWT : Witness T omega <;> simp [hWT, hmu omega]) hS
      simpa [hW] using hle
    · rw [ite_eq_right htail]
      exact Finset.sum_nonneg fun S _ => by
        split <;> simp_all [hmu omega]
  calc
    finiteEventMass mu {omega | n <= K omega} =
        ∑ omega, if n <= K omega then mu omega else 0 := by
      unfold finiteEventMass
      apply Finset.sum_congr rfl
      intro omega _
      simp
    _ <= ∑ omega, subsets.sum (fun S =>
        if Witness S omega then mu omega else 0) :=
      Finset.sum_le_sum fun omega _ => hpoint omega
    _ = subsets.sum (fun S =>
        finiteEventMass mu {omega | Witness S omega}) := by
      unfold finiteEventMass
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro omega _
      simp
    _ <= subsets.sum (fun _S => a ^ n) := by
      apply Finset.sum_le_sum
      intro S hS
      apply hmass S
      simpa [subsets] using hS
    _ = Nat.choose h n * a ^ n := by
      simp [subsets]

end StatMech.Probability
