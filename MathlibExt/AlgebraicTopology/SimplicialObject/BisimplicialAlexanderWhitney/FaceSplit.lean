/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialAlexanderWhitney.OrdinaryFaces
import Mathlib.Tactic.Ring

/-!
# Bisimplicial Alexander--Whitney face splitting

The horizontal and signed vertical parts of the total differential are split
into ordinary faces and their boundary crossover faces.  The two crossover
summands have the same underlying map and opposite signs, so they cancel.
-/

@[expose] public section

open CategoryTheory Limits Simplicial
open scoped Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.BisimplicialAlexanderWhitney

variable {A : Type u} [Category.{v} A] [Preadditive A]
  [Limits.HasFiniteCoproducts A]
  (B : SimplicialObject (SimplicialObject A))

private lemma zsmul_sum {G : Type*} [AddCommGroup G]
    {J : Type*} [Fintype J] (r : ℤ) (f : J → G) :
    r • (∑ j, f j) = ∑ j, r • f j :=
  map_sum (DistribSMul.toAddMonoidHom G r) f Finset.univ

/-- Split a horizontal boundary into its ordinary faces and last crossover
face. -/
theorem horizontal_face_split (p q n : ℕ) (h : p + q = n) :
    faceToBidegreeOfEq B (p + 1) q (n + 1) (by omega) ≫
        ((AlgebraicTopology.bisimplicialAlternatingBicomplex A B).d
          (p + 1) p).f q ≫
      totalιOfEq B p q n h =
    (∑ j : Fin (p + 1), ((-1 : ℤ) ^ j.val) •
      (faceToBidegreeOfEq B (p + 1) q (n + 1) (by omega) ≫
        (B.δ (Fin.castSucc j)).app (Opposite.op ⦋q⦌) ≫
        totalιOfEq B p q n h)) +
    ((-1 : ℤ) ^ (p + 1)) •
      (faceToBidegreeOfEq B (p + 1) q (n + 1) (by omega) ≫
        (B.δ (⟨p + 1, by omega⟩ : Fin (p + 2))).app
          (Opposite.op ⦋q⦌) ≫
        totalιOfEq B p q n h) := by
  let f := faceToBidegreeOfEq B (p + 1) q (n + 1) (by omega)
  let t := totalιOfEq B p q n h
  rw [AlgebraicTopology.bisimplicialAlternatingBicomplex_horizontal_d_f_eq_sum]
  change f ≫ ((∑ i : Fin (p + 2), ((-1 : ℤ) ^ i.val) •
    (B.δ i).app (Opposite.op ⦋q⦌)) ≫ t) = _
  rw [← Category.assoc, Preadditive.comp_sum, Preadditive.sum_comp]
  simp_rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    Category.assoc]
  rw [Fin.sum_univ_castSucc]
  rfl

/-- Split a signed vertical boundary into its zeroth crossover face and
ordinary successor faces. -/
theorem vertical_face_split (p q n : ℕ) (h : p + q = n) :
    ((-1 : ℤ) ^ p) •
      (faceToBidegreeOfEq B p (q + 1) (n + 1) (by omega) ≫
        ((AlgebraicTopology.bisimplicialAlternatingBicomplex A B).X p).d
          (q + 1) q ≫
        totalιOfEq B p q n h) =
    ((-1 : ℤ) ^ p) •
      (faceToBidegreeOfEq B p (q + 1) (n + 1) (by omega) ≫
        (B.obj (Opposite.op ⦋p⦌)).δ
          (⟨0, by omega⟩ : Fin (q + 2)) ≫
        totalιOfEq B p q n h) +
    ∑ k : Fin (q + 1), ((-1 : ℤ) ^ (p + 1 + k.val)) •
      (faceToBidegreeOfEq B p (q + 1) (n + 1) (by omega) ≫
        (B.obj (Opposite.op ⦋p⦌)).δ (Fin.succ k) ≫
        totalιOfEq B p q n h) := by
  let f := faceToBidegreeOfEq B p (q + 1) (n + 1) (by omega)
  let t := totalιOfEq B p q n h
  rw [AlgebraicTopology.bisimplicialAlternatingBicomplex_vertical_d_eq_sum]
  change ((-1 : ℤ) ^ p) •
    (f ≫ ((∑ i : Fin (q + 2), ((-1 : ℤ) ^ i.val) •
      (B.obj (Opposite.op ⦋p⦌)).δ i) ≫ t)) = _
  rw [← Category.assoc, Preadditive.comp_sum, Preadditive.sum_comp]
  simp_rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp,
    zsmul_sum, smul_smul, Category.assoc]
  rw [Fin.sum_univ_succ]
  congr 1
  · dsimp only [f, t]
    simp only [Fin.val_zero, pow_zero, mul_one]
    have hz : (0 : Fin (q + 2)) = ⟨0, by omega⟩ := by ext; rfl
    rw [hz]
  · apply Finset.sum_congr rfl
    intro k _
    simp only [Fin.val_succ, pow_add, pow_one]
    congr 1
    ring

/-- The horizontal-last and vertical-zero crossover summands cancel. -/
theorem crossover_signed_cancel (p q n : ℕ) (h : p + q = n) :
    ((-1 : ℤ) ^ (p + 1)) •
        (faceToBidegreeOfEq B (p + 1) q (n + 1) (by omega) ≫
          (B.δ (⟨p + 1, by omega⟩ : Fin (p + 2))).app
            (Opposite.op ⦋q⦌) ≫
          totalιOfEq B p q n h) +
      ((-1 : ℤ) ^ p) •
        (faceToBidegreeOfEq B p (q + 1) (n + 1) (by omega) ≫
          (B.obj (Opposite.op ⦋p⦌)).δ
            (⟨0, by omega⟩ : Fin (q + 2)) ≫
          totalιOfEq B p q n h) = 0 := by
  let a := faceToBidegreeOfEq B (p + 1) q (n + 1) (by omega) ≫
    (B.δ (⟨p + 1, by omega⟩ : Fin (p + 2))).app
      (Opposite.op ⦋q⦌) ≫ totalιOfEq B p q n h
  let b := faceToBidegreeOfEq B p (q + 1) (n + 1) (by omega) ≫
    (B.obj (Opposite.op ⦋p⦌)).δ
      (⟨0, by omega⟩ : Fin (q + 2)) ≫ totalιOfEq B p q n h
  have hc := crossover_face_eq B p q n h
  have hc' := hc =≫ totalιOfEq B p q n h
  have hab : a = b := by
    simpa only [a, b, Category.assoc] using hc'
  change ((-1 : ℤ) ^ (p + 1)) • a + ((-1 : ℤ) ^ p) • b = 0
  rw [hab]
  have hsign : ((-1 : ℤ) ^ (p + 1)) = -((-1 : ℤ) ^ p) := by
    rw [pow_succ]
    ring
  rw [hsign, neg_smul, neg_add_cancel]

end AlgebraicTopology.BisimplicialAlexanderWhitney
