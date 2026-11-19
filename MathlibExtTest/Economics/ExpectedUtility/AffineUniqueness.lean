/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.ExpectedUtility.AffineUniqueness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open Convexity MathlibExt.Economics.ExpectedUtility

namespace MathlibExtTest.Economics.ExpectedUtility.AffineUniqueness

/-- The expected-utility preference of a Bernoulli utility `u`. -/
def euPref {X : Type*} [Fintype X] (u : X → ℝ) : StdSimplex ℝ X → StdSimplex ℝ X → Prop :=
  fun p q => expectedUtility u q ≤ expectedUtility u p

theorem euPref_self {X : Type*} [Fintype X] (u : X → ℝ) :
    IsExpectedUtilityRepresentation (euPref u) u := by
  intro p q
  rfl

/-- A positive affine transformation `2u + 3` represents the same preference. -/
theorem euPref_affine (u : Fin 3 → ℝ) :
    IsExpectedUtilityRepresentation (euPref u) (fun x => 2 * u x + 3) := by
  intro p q
  show (expectedUtility u q ≤ expectedUtility u p) ↔
    (expectedUtility (fun x => 2 * u x + 3) q ≤ expectedUtility (fun x => 2 * u x + 3) p)
  have hEU : ∀ r : StdSimplex ℝ (Fin 3),
      expectedUtility (fun x => 2 * u x + 3) r = 2 * expectedUtility u r + 3 := by
    intro r
    unfold expectedUtility
    have hsum : ∑ x, r.weights x * (2 * u x + 3)
        = 2 * (∑ x, r.weights x * u x) + 3 * (∑ x, r.weights x) := by
      have h1 : ∀ x : Fin 3, r.weights x * (2 * u x + 3)
          = 2 * (r.weights x * u x) + 3 * r.weights x := by
        intro x
        ring
      simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsum, StdSimplex.total_of_fintype, mul_one]
  rw [hEU q, hEU p]
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- `![0, 1, 4]` is not a positive affine transformation of `![0, 1, 2]` (the gaps `1, 3` are not
proportional to `1, 1`). -/
theorem square_not_affine :
    ¬ ∃ a b : ℝ, 0 < a ∧ ∀ x, (![0, 1, 4] : Fin 3 → ℝ) x = a * (![0, 1, 2] : Fin 3 → ℝ) x + b := by
  rintro ⟨a, b, ha, h⟩
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp at h0 h1 h2
  linarith

/-- Money amounts `0, 1, 2` with risk-neutral utility `u = id`: the increasing nonlinear
transformation `u²` ranks the sure amount `1` strictly below the fair coin on `0` and `2`
(expected utilities `1 < 2`), although `u` ranks them equally, so `u²` is not an
expected-utility representation of the preference of `u`. -/
theorem euPref_square_not_representation :
    ¬ IsExpectedUtilityRepresentation (euPref ![0, 1, 2]) ![0, 1, 4] := by
  intro hrep
  have hself := euPref_self ![0, 1, 2]
  have hex := hself.exists_pos_affine hrep
  exact square_not_affine hex

end MathlibExtTest.Economics.ExpectedUtility.AffineUniqueness
