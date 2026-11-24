/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Ring.K2.StableElementaryNatural
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.ElementaryRelations

/-! # Natural-index stable elementary relations

Stable elementary relations transferred from the finite level via
`natElementary_fin` at a common finite rank chosen by nested maxima.
-/

@[expose] public section

namespace AlgebraicKTheory

namespace StableE

open scoped commutatorElement

variable {R : Type*} [Ring R]

private theorem natElementary_eq_fin (N : ℕ) (i j : ℕ)
    (hij : i ≠ j) (hi : i < N) (hj : j < N) (a : R) :
    natElementary (R := R) i j hij a =
      StableE.elementary N ⟨i, hi⟩ ⟨j, hj⟩
        (fun h => hij (congrArg Fin.val h)) a := by
  have h :=
    natElementary_fin (R := R) (n := N) (i := ⟨i, hi⟩)
      (j := ⟨j, hj⟩)
      (hij := fun h => hij (congrArg Fin.val h)) a
  simpa using h

theorem natElementary_add (i j : ℕ) (hij : i ≠ j) (a b : R) :
    natElementary (R := R) i j hij a *
      natElementary i j hij b =
      natElementary i j hij (a + b) := by
  let N := max i j + 1
  have hi : i < N := by dsimp [N]; omega
  have hj : j < N := by dsimp [N]; omega
  have hijFin : (⟨i, hi⟩ : Fin N) ≠ (⟨j, hj⟩ : Fin N) :=
    fun h => hij (congrArg Fin.val h)
  let iFin : Fin N := ⟨i, hi⟩
  let jFin : Fin N := ⟨j, hj⟩
  have h1 := natElementary_eq_fin (R := R) (N := N)
    (i := i) (j := j) hij hi hj a
  have h2 := natElementary_eq_fin (R := R) (N := N)
    (i := i) (j := j) hij hi hj b
  have h3 := natElementary_eq_fin (R := R) (N := N)
    (i := i) (j := j) hij hi hj (a + b)
  rw [h1, h2, h3]
  apply Subtype.ext
  calc (↑(StableE.elementary N iFin jFin hijFin a *
        StableE.elementary N iFin jFin hijFin b) :
        StableGL R)
      = (↑(StableE.elementary N iFin jFin hijFin a) :
          StableGL R) *
        (↑(StableE.elementary N iFin jFin hijFin b) :
          StableGL R) := rfl
    _ = StableGL.of
          (Matrix.GeneralLinearGroup.elementary iFin jFin hijFin a) *
        StableGL.of
          (Matrix.GeneralLinearGroup.elementary iFin jFin hijFin b) := by
          simp only [StableE.coe_elementary]
    _ = StableGL.of
          (Matrix.GeneralLinearGroup.elementary iFin jFin hijFin a *
            Matrix.GeneralLinearGroup.elementary iFin jFin hijFin b) := by
          rw [StableGL.of_mul]
    _ = StableGL.of
          (Matrix.GeneralLinearGroup.elementary iFin jFin hijFin (a + b)) := by
          rw [Matrix.GeneralLinearGroup.elementary_mul_same]
    _ = (↑(StableE.elementary N iFin jFin hijFin (a + b) :
          StableE R) : StableGL R) := by
          simp only [StableE.coe_elementary]

theorem natElementary_comm (i j k l : ℕ) (hij : i ≠ j)
    (hkl : k ≠ l) (hil : i ≠ l) (hjk : j ≠ k) (a b : R) :
    ⁅natElementary (R := R) i j hij a,
      natElementary k l hkl b⁆ = 1 := by
  let N := max (max i j) (max k l) + 1
  have hi : i < N := by dsimp [N]; omega
  have hj : j < N := by dsimp [N]; omega
  have hk : k < N := by dsimp [N]; omega
  have hl : l < N := by dsimp [N]; omega
  have hijFin : (⟨i, hi⟩ : Fin N) ≠ (⟨j, hj⟩ : Fin N) :=
    fun h => hij (congrArg Fin.val h)
  have hklFin : (⟨k, hk⟩ : Fin N) ≠ (⟨l, hl⟩ : Fin N) :=
    fun h => hkl (congrArg Fin.val h)
  have hjkFin : (⟨j, hj⟩ : Fin N) ≠ (⟨k, hk⟩ : Fin N) :=
    fun h => hjk (congrArg Fin.val h)
  have hliFin : (⟨l, hl⟩ : Fin N) ≠ (⟨i, hi⟩ : Fin N) :=
    fun h => hil (congrArg Fin.val h).symm
  let iFin : Fin N := ⟨i, hi⟩
  let jFin : Fin N := ⟨j, hj⟩
  let kFin : Fin N := ⟨k, hk⟩
  let lFin : Fin N := ⟨l, hl⟩
  have h1 := natElementary_eq_fin (R := R) (N := N)
    (i := i) (j := j) hij hi hj a
  have h2 := natElementary_eq_fin (R := R) (N := N)
    (i := k) (j := l) hkl hk hl b
  rw [h1, h2]
  apply Subtype.ext
  calc (↑(⁅StableE.elementary N iFin jFin hijFin a,
        StableE.elementary N kFin lFin hklFin b⁆ :
        StableE R) : StableGL R)
      = (↑(StableE.elementary N iFin jFin hijFin a) : StableGL R) *
        (↑(StableE.elementary N kFin lFin hklFin b) : StableGL R) *
        (↑(StableE.elementary N iFin jFin hijFin a) : StableGL R)⁻¹ *
        (↑(StableE.elementary N kFin lFin hklFin b) : StableGL R)⁻¹ := rfl
    _ = StableGL.of
          (Matrix.GeneralLinearGroup.elementary iFin jFin hijFin a) *
        StableGL.of
          (Matrix.GeneralLinearGroup.elementary kFin lFin hklFin b) *
        (StableGL.of
          (Matrix.GeneralLinearGroup.elementary iFin jFin hijFin a))⁻¹ *
        (StableGL.of
          (Matrix.GeneralLinearGroup.elementary kFin lFin hklFin b))⁻¹ := by
          simp only [StableE.coe_elementary]
    _ = ⁅StableGL.of
          (Matrix.GeneralLinearGroup.elementary iFin jFin hijFin a),
          StableGL.of
            (Matrix.GeneralLinearGroup.elementary kFin lFin hklFin b)⁆ := by
          simp only [commutatorElement_def]
    _ = StableGL.of
          ⁅Matrix.GeneralLinearGroup.elementary iFin jFin hijFin a,
            Matrix.GeneralLinearGroup.elementary kFin lFin hklFin b⁆ := by
          rw [StableGL.of_commutator]
    _ = StableGL.of (1 : Matrix.GeneralLinearGroup (Fin N) R) := by
          rw [Matrix.GeneralLinearGroup.commutatorElement_elementary_eq_one
            iFin jFin kFin lFin hijFin hklFin hjkFin hliFin a b]
    _ = (1 : StableGL R) := StableGL.of_one
    _ = (↑(1 : StableE R) : StableGL R) := rfl

theorem natElementary_chev (i j k : ℕ) (hij : i ≠ j)
    (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    ⁅natElementary (R := R) i j hij a,
      natElementary j k hjk b⁆ =
      natElementary i k hik (a * b) := by
  let N := max (max i j) k + 1
  have hi : i < N := by dsimp [N]; omega
  have hj : j < N := by dsimp [N]; omega
  have hk : k < N := by dsimp [N]; omega
  have hijFin : (⟨i, hi⟩ : Fin N) ≠ (⟨j, hj⟩ : Fin N) :=
    fun h => hij (congrArg Fin.val h)
  have hjkFin : (⟨j, hj⟩ : Fin N) ≠ (⟨k, hk⟩ : Fin N) :=
    fun h => hjk (congrArg Fin.val h)
  have hikFin : (⟨i, hi⟩ : Fin N) ≠ (⟨k, hk⟩ : Fin N) :=
    fun h => hik (congrArg Fin.val h)
  let iFin : Fin N := ⟨i, hi⟩
  let jFin : Fin N := ⟨j, hj⟩
  let kFin : Fin N := ⟨k, hk⟩
  have h1 := natElementary_eq_fin (R := R) (N := N)
    (i := i) (j := j) hij hi hj a
  have h2 := natElementary_eq_fin (R := R) (N := N)
    (i := j) (j := k) hjk hj hk b
  have h3 := natElementary_eq_fin (R := R) (N := N)
    (i := i) (j := k) hik hi hk (a * b)
  rw [h1, h2, h3]
  apply Subtype.ext
  calc (↑(⁅StableE.elementary N iFin jFin hijFin a,
        StableE.elementary N jFin kFin hjkFin b⁆ :
        StableE R) : StableGL R)
      = (↑(StableE.elementary N iFin jFin hijFin a) : StableGL R) *
        (↑(StableE.elementary N jFin kFin hjkFin b) : StableGL R) *
        (↑(StableE.elementary N iFin jFin hijFin a) : StableGL R)⁻¹ *
        (↑(StableE.elementary N jFin kFin hjkFin b) : StableGL R)⁻¹ := rfl
    _ = StableGL.of
          (Matrix.GeneralLinearGroup.elementary iFin jFin hijFin a) *
        StableGL.of
          (Matrix.GeneralLinearGroup.elementary jFin kFin hjkFin b) *
        (StableGL.of
          (Matrix.GeneralLinearGroup.elementary iFin jFin hijFin a))⁻¹ *
        (StableGL.of
          (Matrix.GeneralLinearGroup.elementary jFin kFin hjkFin b))⁻¹ := by
          simp only [StableE.coe_elementary]
    _ = ⁅StableGL.of
          (Matrix.GeneralLinearGroup.elementary iFin jFin hijFin a),
          StableGL.of
            (Matrix.GeneralLinearGroup.elementary jFin kFin hjkFin b)⁆ := by
          simp only [commutatorElement_def]
    _ = StableGL.of
          ⁅Matrix.GeneralLinearGroup.elementary iFin jFin hijFin a,
            Matrix.GeneralLinearGroup.elementary jFin kFin hjkFin b⁆ := by
          rw [StableGL.of_commutator]
    _ = StableGL.of
          (Matrix.GeneralLinearGroup.elementary iFin kFin hikFin (a * b)) := by
          rw [Matrix.GeneralLinearGroup.commutatorElement_elementary
            iFin kFin jFin hikFin hijFin hjkFin a b]
    _ = (↑(StableE.elementary N iFin kFin hikFin (a * b) :
          StableE R) : StableGL R) := by
          simp only [StableE.coe_elementary]

end StableE

end AlgebraicKTheory

end
