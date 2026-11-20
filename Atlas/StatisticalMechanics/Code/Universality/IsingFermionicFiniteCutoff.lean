/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicFiniteCaccioppoli
import Code.Universality.IsingFermionicPhysicalCheckerboard
import Mathlib.Combinatorics.SimpleGraph.DegreeSum



namespace StatMech.Universality

open Finset SimpleGraph

noncomputable section



theorem isingFiniteGraphDart_card_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) (D : Nat)
    (hdeg : ∀ x, Nat.card (G.neighborSet x) ≤ D) :
    Nat.card G.Dart ≤ Fintype.card V * D := by
  classical
  have hdeg' : ∀ x, G.degree x ≤ D := by
    intro x
    calc
      G.degree x = Fintype.card (G.neighborSet x) :=
        (G.card_neighborSet_eq_degree x).symm
      _ = Nat.card (G.neighborSet x) := Nat.card_eq_fintype_card.symm
      _ ≤ D := hdeg x
  rw [Nat.card_eq_fintype_card, G.dart_card_eq_sum_degrees]
  calc
    (∑ x, G.degree x) ≤ ∑ _x : V, D :=
      sum_le_sum fun x _ ↦ hdeg' x
    _ = Fintype.card V * D := by simp



theorem isingFiniteGraphDartFinset_card_le
    {V : Type*} [Fintype V] (G : SimpleGraph V) (D : Nat)
    (hdeg : ∀ x, Nat.card (G.neighborSet x) ≤ D) (S : Finset G.Dart) :
    S.card ≤ Fintype.card V * D := by
  classical
  exact (Finset.card_le_univ S).trans (by
    simpa only [Nat.card_eq_fintype_card] using
      isingFiniteGraphDart_card_le G D hdeg)



theorem isingFiniteGraphDartSum_cutoffEnergy_le
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (eta : V → Real) (D : Nat) (L : Real)
    (hdeg : ∀ x, Nat.card (G.neighborSet x) ≤ D) (hL : 0 ≤ L)
    (hlip : ∀ d : G.Dart, |eta d.snd - eta d.fst| ≤ L) :
    isingFiniteGraphDartSum G (fun x y ↦ (eta y - eta x) ^ 2) ≤
      (Fintype.card V * D : Nat) * L ^ 2 := by
  classical
  have hcard : Fintype.card G.Dart ≤ Fintype.card V * D := by
    simpa only [Nat.card_eq_fintype_card] using
      isingFiniteGraphDart_card_le G D hdeg
  unfold isingFiniteGraphDartSum
  calc
    (∑ d : G.Dart, (eta d.snd - eta d.fst) ^ 2) ≤
        ∑ _d : G.Dart, L ^ 2 := by
      apply sum_le_sum
      intro d _
      rw [sq_le_sq]
      simpa [abs_of_nonneg hL] using hlip d
    _ = Fintype.card G.Dart * L ^ 2 := by simp
    _ ≤ (Fintype.card V * D : Nat) * L ^ 2 := by
      gcongr

theorem fkIsingSquareRadialPatchPrimalNode_card_le_sq (m : Nat) :
    Fintype.card (FKIsingSquareRadialPatchPrimalNode m) ≤ m ^ 2 := by
  calc
    Fintype.card (FKIsingSquareRadialPatchPrimalNode m) ≤
        Fintype.card (Fin m × Fin m) := Fintype.card_subtype_le _
    _ = m ^ 2 := by simp [pow_two]

theorem fkIsingSquareRadialPatchDualNode_card_le_sq (m : Nat) :
    Fintype.card (FKIsingSquareRadialPatchDualNode m) ≤ m ^ 2 := by
  calc
    Fintype.card (FKIsingSquareRadialPatchDualNode m) ≤
        Fintype.card (Fin m × Fin m) := Fintype.card_subtype_le _
    _ = m ^ 2 := by simp [pow_two]

end

end StatMech.Universality
