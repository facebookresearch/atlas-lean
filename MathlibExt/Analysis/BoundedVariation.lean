/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Algebraic closure properties of bounded variation

This file records that functions of bounded variation on a set, with values in a seminormed
additive group, are closed under addition, negation, subtraction and finite sums, and that
constant functions and single jumps have bounded variation.

## Main statements

* `eVariationOn.add_le`: the variation of a sum is at most the sum of the variations.
* `BoundedVariationOn.add`, `BoundedVariationOn.neg`, `BoundedVariationOn.sub`
* `BoundedVariationOn.finsetSum`
* `boundedVariationOn_const`
* `boundedVariationOn_ite_le`: a function with a single jump has bounded variation.
-/

@[expose] public section

open scoped ENNReal

variable {α ι E : Type*} [LinearOrder α] [SeminormedAddCommGroup E]

/-- The variation of a sum is at most the sum of the variations. -/
theorem eVariationOn.add_le (f g : α → E) (s : Set α) :
    eVariationOn (f + g) s ≤ eVariationOn f s + eVariationOn g s := by
  refine iSup_le fun ⟨n, u, hu, us⟩ => ?_
  calc (∑ i ∈ Finset.range n, edist ((f + g) (u (i + 1))) ((f + g) (u i)))
      ≤ ∑ i ∈ Finset.range n,
          (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) :=
        Finset.sum_le_sum fun i _ => edist_add_add_le _ _ _ _
    _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))
          + ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s :=
        add_le_add (eVariationOn.sum_le hu us) (eVariationOn.sum_le hu us)

/-- Negation does not change the variation. -/
@[simp]
theorem eVariationOn.neg (f : α → E) (s : Set α) : eVariationOn (-f) s = eVariationOn f s := by
  simp only [eVariationOn, Pi.neg_apply, edist_neg_neg]

/-- A constant function has bounded variation on every set. -/
theorem boundedVariationOn_const (c : E) (s : Set α) :
    BoundedVariationOn (fun _ : α => c) s := by
  have h : eVariationOn (fun _ : α => c) s = 0 :=
    eVariationOn.constant_on (by rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩; rfl)
  simp [BoundedVariationOn, h]

namespace BoundedVariationOn

variable {f g : α → E} {s : Set α}

/-- A sum of two functions of bounded variation has bounded variation. -/
theorem add (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (f + g) s :=
  ((eVariationOn.add_le f g s).trans_lt (ENNReal.add_lt_top.2 ⟨hf.lt_top, hg.lt_top⟩)).ne

/-- The negation of a function of bounded variation has bounded variation. -/
theorem neg (hf : BoundedVariationOn f s) : BoundedVariationOn (-f) s := by
  simpa [BoundedVariationOn] using hf

/-- A difference of two functions of bounded variation has bounded variation. -/
theorem sub (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (f - g) s := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-- A finite sum of functions of bounded variation has bounded variation. -/
theorem finsetSum {t : Finset ι} {F : ι → α → E}
    (hF : ∀ i ∈ t, BoundedVariationOn (F i) s) :
    BoundedVariationOn (fun x => ∑ i ∈ t, F i x) s := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using boundedVariationOn_const (0 : E) s
  | insert m t hm ih =>
    simp_rw [Finset.sum_insert hm]
    exact (hF m (Finset.mem_insert_self m t)).add
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

end BoundedVariationOn

/-- A function taking one value to the right of a point `a` (inclusive) and another value to
its left has bounded variation on every set: its variation is at most the jump `‖c₁ - c₂‖`. -/
theorem boundedVariationOn_ite_le (a : α) (c₁ c₂ : E) (s : Set α) :
    BoundedVariationOn (fun y : α => if a ≤ y then c₁ else c₂) s := by
  have key : eVariationOn (fun y : α => if a ≤ y then c₁ else c₂) s ≤ ‖c₁ - c₂‖ₑ := by
    refine iSup_le fun ⟨n, u, hu, us⟩ => ?_
    set w : ℕ → ℝ≥0∞ := fun i => if a ≤ u i then ‖c₁ - c₂‖ₑ else 0 with hw
    have hterm : ∀ i : ℕ, w i +
        edist (if a ≤ u (i + 1) then c₁ else c₂) (if a ≤ u i then c₁ else c₂) = w (i + 1) := by
      intro i
      by_cases hi : a ≤ u i
      · have hi' : a ≤ u (i + 1) := hi.trans (hu (Nat.le_succ i))
        simp [hw, hi, hi']
      · by_cases hi' : a ≤ u (i + 1)
        · simp [hw, hi, hi', edist_eq_enorm_sub]
        · simp [hw, hi, hi']
    have htel : ∀ m : ℕ, (∑ i ∈ Finset.range m,
        edist (if a ≤ u (i + 1) then c₁ else c₂) (if a ≤ u i then c₁ else c₂)) + w 0 = w m := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [Finset.sum_range_succ, add_right_comm, ih]; exact hterm m
    calc (∑ i ∈ Finset.range n,
            edist (if a ≤ u (i + 1) then c₁ else c₂) (if a ≤ u i then c₁ else c₂))
        ≤ (∑ i ∈ Finset.range n,
            edist (if a ≤ u (i + 1) then c₁ else c₂) (if a ≤ u i then c₁ else c₂)) + w 0 :=
          le_self_add
      _ = w n := htel n
      _ ≤ ‖c₁ - c₂‖ₑ := by simp only [hw]; split <;> simp
  exact (key.trans_lt enorm_lt_top).ne
