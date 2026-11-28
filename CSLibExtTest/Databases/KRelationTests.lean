/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Databases.KRelation
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Defs

/-!
# Coefficient checks for K-relations

Two different rows agree on their middle coordinate. Projection therefore adds their tags;
joining on that coordinate multiplies tags only for a compatible pair. The headings use three
names, while the value domain is all of `ℕ`.
-/

namespace Cslib.Databases.KRelationTests

open KRelation

private abbrev Name := Fin 3
private abbrev ab : Finset Name := {0, 1}
private abbrev bc : Finset Name := {1, 2}
private abbrev b : Finset Name := {1}
private abbrev Row (S : Finset Name) := Subtype (Tuple.IsOver (D := ℕ) S)
private def row (S : Finset Name) (v : Name → ℕ) : Row S :=
  ⟨fun i => if i ∈ S then some (v i) else none, fun i => by by_cases hi : i ∈ S <;> simp [hi]⟩

private abbrev first := row ab ![4, 7, 0]
private abbrev second := row ab ![5, 7, 0]
private abbrev key := row b ![0, 7, 0]
private abbrev right := row bc ![0, 7, 9]
private abbrev other := row bc ![0, 8, 9]
private abbrev joined := row (ab ∪ bc) ![4, 7, 9]

private noncomputable abbrev ops (K : Type*) [CommSemiring K] := positiveAlgebra Name ℕ K

variable {K : Type*} [CommSemiring K]

example : first ≠ second := by decide

private theorem two_to_one (x y : K) :
    (ops K).project (show b ⊆ ab by decide) (Finsupp.single first x + Finsupp.single second y)
      key = x + y := by
  change Finsupp.mapDomain (onSubheading (show b ⊆ ab by decide)) _ key = _
  have h₁ : onSubheading (show b ⊆ ab by decide) first = key := by decide
  have h₂ : onSubheading (show b ⊆ ab by decide) second = key := by decide
  simp [Finsupp.mapDomain_add, h₁, h₂]

private theorem matching (x y : K) :
    (ops K).join (Finsupp.single first x) (Finsupp.single right y) joined = x * y := by
  have h₁ : onSubheading (Finset.subset_union_left (s₁ := ab) (s₂ := bc)) joined = first := by
    decide
  have h₂ : onSubheading (Finset.subset_union_right (s₁ := ab) (s₂ := bc)) joined = right := by
    decide
  simp [ops, h₁, h₂]

-- No union-heading tuple can have both 7 and 8 at the shared coordinate.
example (x y : K) : (ops K).join (Finsupp.single first x) (Finsupp.single other y) = 0 := by
  classical
  ext t
  rw [show (ops K).join _ _ t = _ from join_apply _ _ t]
  by_cases hl : onSubheading (Finset.subset_union_left (s₁ := ab) (s₂ := bc)) t = first
  · have hr : onSubheading (Finset.subset_union_right (s₁ := ab) (s₂ := bc)) t ≠ other := by
      intro hr
      have h₇ := congrArg (fun q : Row ab => q.val 1) hl
      have h₈ := congrArg (fun q : Row bc => q.val 1) hr
      simp [onSubheading, row] at h₇ h₈
      simp [h₇] at h₈
    simp [Finsupp.single_apply, Ne.symm hr]
  · simp [Finsupp.single_apply, Ne.symm hl]

-- Bag counts and deletion by a selection predicate.
example : (ops ℕ).project (show b ⊆ ab by decide) (Finsupp.single first 2 + Finsupp.single second 5)
    key = 7 := two_to_one 2 5

example : (ops ℕ).join (Finsupp.single first 2) (Finsupp.single right 5) joined = 10 :=
  matching 2 5

example (n : ℕ) : (ops ℕ).select (fun q => q.val 0 = some 4) (Finsupp.single first n) first = n ∧
    (ops ℕ).select (fun q => q.val 0 = some 4) (Finsupp.single second n) second = 0 := by
  have h₁ : first.val 0 = some 4 := rfl
  have h₂ : second.val 0 ≠ some 4 := by decide
  simp [ops, h₁, h₂]

example : (ops ℕ).empty first = 0 := empty_apply _

-- Swapping the outer names transports (4,7) on {0,1} to (7,4) on {1,2}.
private def swapOuter : ab ≃ bc :=
  (Equiv.swap (0 : Name) 2).subtypeEquiv (p := (· ∈ ab)) (q := (· ∈ bc)) (by decide)

private abbrev renamed := row bc ![0, 7, 4]

example (n : ℕ) : (ops ℕ).rename swapOuter (Finsupp.single first n) renamed = n := by
  have h : relabel swapOuter first = renamed := by decide
  rw [← h, rename_apply, Equiv.symm_apply_apply, Finsupp.single_eq_same]

-- Truth-valued annotations form the OR/AND semiring, not the Boolean ring.
section Boolean

local instance : CommSemiring Bool where
  zero := false
  one := true
  add := (· || ·)
  mul := (· && ·)
  zero_add := by decide
  add_zero := by decide
  add_assoc := by decide
  add_comm := by decide
  zero_mul := by decide
  mul_zero := by decide
  one_mul := by decide
  mul_one := by decide
  mul_assoc := by decide
  mul_comm := by decide
  left_distrib := by decide
  right_distrib := by decide
  nsmul := @nsmulRec Bool ⟨false⟩ ⟨(· || ·)⟩

example (x y : Bool) : (ops Bool).union (Finsupp.single first x) (Finsupp.single first y) first =
    (x || y) := by simp [ops]; rfl

example (x y : Bool) : (ops Bool).join (Finsupp.single first x) (Finsupp.single right y) joined =
    (x && y) := matching x y

example : (ops Bool).project (show b ⊆ ab by decide)
    (Finsupp.single first true + Finsupp.single second true) key = true := two_to_one true true

end Boolean

-- Polynomial alternatives retain different variables; compatible inputs give their monomial.
private abbrev Tags := MvPolynomial Bool ℕ

example : (ops Tags).project (show b ⊆ ab by decide)
    (Finsupp.single first (MvPolynomial.X false) + Finsupp.single second (MvPolynomial.X true))
    key = MvPolynomial.X false + MvPolynomial.X true := two_to_one _ _

example : (ops Tags).join (Finsupp.single first (MvPolynomial.X false))
    (Finsupp.single right (MvPolynomial.X true)) joined =
      MvPolynomial.X false * MvPolynomial.X true :=
  matching _ _

-- Cancellation and zero divisors give strict support bounds, unlike the Boolean example.
example : (ops (ZMod 2)).project (show b ⊆ ab by decide)
    (Finsupp.single first 1 + Finsupp.single second 1) key = 0 := (two_to_one 1 1).trans (by decide)

example : (ops (ZMod 6)).join (Finsupp.single first 2) (Finsupp.single right 3) joined = 0 :=
  (matching 2 3).trans (by decide)

end Cslib.Databases.KRelationTests
