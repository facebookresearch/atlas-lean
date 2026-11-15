/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Borůvka's algorithm: halving counting

Each Borůvka phase merges every component with another, so
every merged block contains at least two old components. This
module proves the counting consequence: the number of
components at least halves per phase. The MST optimality
argument is not formalized here.
-/

@[expose] public section

/-- Borůvka halving, counting core of DPA-30: if every block of
a merged partition contains at least two old components (the
fibers of the assignment map `f`), the number of blocks at
least halves. -/
theorem card_le_of_forall_fiber_ge {C D : Type*} [Fintype C] [Fintype D] [DecidableEq D]
    (f : C → D) (h2 : ∀ d, 2 ≤ (Finset.univ.filter (fun c => f c = d)).card) :
    2 * Fintype.card D ≤ Fintype.card C := by
  have hmaps : Set.MapsTo f (↑(Finset.univ : Finset C) : Set C)
      (↑(Finset.univ : Finset D) : Set D) :=
    fun _ _ => Finset.mem_univ _
  have hdecomp := Finset.card_eq_sum_card_fiberwise (f := f)
    (s := (Finset.univ : Finset C)) (t := (Finset.univ : Finset D)) hmaps
  rw [Finset.card_univ] at hdecomp
  have hle : ∑ _d ∈ (Finset.univ : Finset D), 2 ≤
      ∑ d ∈ (Finset.univ : Finset D), {a ∈ (Finset.univ : Finset C) | f a = d}.card :=
    Finset.sum_le_sum (fun d _ => h2 d)
  rw [Finset.sum_const, Finset.card_univ] at hle
  simp only [smul_eq_mul] at hle
  rw [mul_comm] at hle
  rw [hdecomp]
  exact hle

/-- Same statement with the strict form used for phases: the
merged component count is at most half the old count (real
form, from the integer form). -/
theorem merged_card_le_half {C D : Type*} [Fintype C] [Fintype D] [DecidableEq D]
    (f : C → D) (h2 : ∀ d, 2 ≤ (Finset.univ.filter (fun c => f c = d)).card) :
    (Fintype.card D : ℝ) ≤ Fintype.card C / 2 := by
  have h := card_le_of_forall_fiber_ge f h2
  have hR : (2 : ℝ) * (Fintype.card D : ℝ) ≤ (Fintype.card C : ℝ) := by
    exact_mod_cast h
  linarith

end
