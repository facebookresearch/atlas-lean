/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Order.Filter.Extr
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Tactic.Linarith

/-! # Monotonicity of virtual surplus maximization

A score profile `w` assigns the virtual surplus `dotProduct w x` to allocation `x`. Increasing
just one score orders that coordinate of *every* old optimum against *every* new optimum. If the
score stays flat, a rule that selects on the virtual profile cannot switch optima, but a rule that
selects on raw reports can.

## Reference

J. D. Hartline, *Mechanism Design and Approximation*, ch. 3, p. 66: Lemma 3.3.1 applies a
surplus-maximizing rule to the virtual profile; Definition 3.3.1 uses nondecreasing virtual values.
The strict-score comparison and the flat-score counterexample below distinguish the two roles of
tie-breaking in this argument.
-/

public section

namespace MathlibExt.GameTheory.MechanismDesign

open Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : Set (ι → ℝ)}

/-- Fix a finite set of bidders, one feasible set `X` of real allocation vectors, and the scores
`w` of all bidders other than `i`. If bidder `i`'s score rises strictly from `s` to `t`, every
feasible maximizer `x` of the weighted sum `∑ j, (update w i s) j * x j` has `x i ≤ y i` for
**every** feasible maximizer `y` at `t`. This compares attained maxima on the same `X`; it does
not assert existence, uniqueness, or a strict increase in allocation. No tie policy is needed.
In particular `X` can be any subset of the nonnegative allocations: the comparison uses neither
nonnegativity nor finiteness or convexity of `X`. -/
theorem allocation_le_of_virtualScore_lt (w : ι → ℝ) (i : ι) {s t : ℝ} (hst : s < t)
    {x y : ι → ℝ} (hx : x ∈ X) (hy : y ∈ X)
    (hs : IsMaxOn (dotProduct (update w i s)) X x)
    (ht : IsMaxOn (dotProduct (update w i t)) X y) : x i ≤ y i := by
  have h : 0 ≤ (update w i t - update w i s) ⬝ᵥ (y - x) := by
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub]
    linarith only [isMaxOn_iff.mp hs y hy, isMaxOn_iff.mp ht x hx]
  rw [← update_sub, sub_self] at h
  change 0 ≤ Pi.single i (t - s) ⬝ᵥ (y - x) at h
  rw [single_dotProduct, Pi.sub_apply] at h
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right h (sub_pos.mpr hst))

variable {β : Type*} [PartialOrder β] {φ : β → ℝ}

/-- With the other reports fixed, let `x b` be the allocation chosen at own raw bid `b`, for a
finite set of bidders. At each such bid assume `x b` lies in the same arbitrary feasible set `X`
of real allocations and maximizes the weighted sum with opposing scores fixed at `w` and own
score `φ b`. If `φ` is strictly increasing, bidder `i`'s chosen allocation is nondecreasing in
its bid. The rule `x` may break ties using the raw bid; no uniqueness or general existence of
maximizers is asserted. -/
theorem monotone_allocation_of_strictMono_virtualValue (w : ι → ℝ) (i : ι) (hφ : StrictMono φ)
    (x : β → X) (hmax : ∀ b, IsMaxOn (dotProduct (update w i (φ b))) X (x b)) :
    Monotone fun b ↦ (x b : ι → ℝ) i := by
  intro b c hbc
  rcases hbc.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact allocation_le_of_virtualScore_lt w i (hφ hlt) (x b).property (x c).property
      (hmax b) (hmax c)

/-- **Virtual surplus maximization is monotone.** Fix a bidder `i` in a finite set, fix all
opposing reports (hence their scores `w`), and let `φ` be the bidder's nondecreasing virtual
value. At every own bid `b`, suppose `opt` on the **whole virtual score vector** `update w i (φ b)`
selects a feasible allocation maximizing the sum of score times allocation over the same arbitrary
set `X` of real allocations. Then its allocation to `i` is nondecreasing in the raw bid. A strict
score rise orders all maximizers; on a flat piece the score vectors coincide, so the function
`opt` chooses the same allocation. Optimality is required only at the profiles in question;
no existence or uniqueness of maximizers for general feasible sets is claimed.
See Hartline, *Mechanism Design and Approximation*, ch. 3, Lemma 3.3.1 (p. 66). -/
theorem monotone_allocation_of_monotone_virtualValue (w : ι → ℝ) (i : ι) (hφ : Monotone φ)
    (opt : (ι → ℝ) → X)
    (hmax : ∀ b, IsMaxOn (dotProduct (update w i (φ b))) X (opt (update w i (φ b)))) :
    Monotone fun b ↦ (opt (update w i (φ b)) : ι → ℝ) i := by
  intro b c hbc
  rcases (hφ hbc).eq_or_lt with heq | hlt
  · simp only [heq, le_refl]
  · exact allocation_le_of_virtualScore_lt w i hlt (opt _).property (opt _).property
      (hmax b) (hmax c)

/-- With one bidder, constant zero virtual score, and feasible allocations the zero and one
vectors, there is a rule on **raw** real bid profiles that maximizes virtual surplus at every
report but assigns one unit at bid `0` and none at bid `1`. The bids are strictly ordered and
the virtual vectors identical: a choice among these feasible maximizers need not be monotone
when the choice is allowed to distinguish equal virtual profiles. -/
theorem exists_decreasing_allocation_of_flat_virtualValue :
    ∃ x : (Unit → ℝ) → Unit → ℝ,
      (∀ b, x b ∈ ({0, 1} : Set (Unit → ℝ)) ∧ IsMaxOn (dotProduct 0) {0, 1} (x b)) ∧
      x 0 () = 1 ∧ x 1 () = 0 := by
  let x (b : Unit → ℝ) : Unit → ℝ := if b () = 0 then 1 else 0
  refine ⟨x, fun b ↦ ⟨?_, ?_⟩, ?_, ?_⟩
  · by_cases hb : b () = 0 <;> simp [x, hb]
  · exact isMaxOn_iff.mpr fun y _ ↦ by simp
  · simp [x]
  · simp [x]

end MathlibExt.GameTheory.MechanismDesign
