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

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Star.Basic

/-!
# Finite left- and right-generating tuples

Pure algebraic carrier and characteristic laws used by numeric topological
stable rank.  The two orientations remain distinct over a noncommutative
semiring.  This module has no topology dependency.
-/

public section

open scoped BigOperators

universe uR uS uI

/-- A tuple generates the unit as a left ideal: coefficients multiply its
entries on the left.  This is Rieffel's `Lg_n` orientation. -/
@[expose] def IsLeftGeneratingTuple
    {R : Type uR} [Semiring R] {ι : Type uI} [Fintype ι]
    (a : ι → R) : Prop :=
  ∃ b : ι → R, ∑ i, b i * a i = 1

/-- A tuple generates the unit as a right ideal: coefficients multiply its
entries on the right. -/
@[expose] def IsRightGeneratingTuple
    {R : Type uR} [Semiring R] {ι : Type uI} [Fintype ι]
    (a : ι → R) : Prop :=
  ∃ b : ι → R, ∑ i, a i * b i = 1

namespace IsLeftGeneratingTuple

/-- A coefficient ring homomorphism carries a left-generating tuple to a
left-generating tuple. -/
theorem map
    {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
    {ι : Type uI} [Fintype ι]
    {a : ι → R} (ha : IsLeftGeneratingTuple a) (f : R →+* S) :
    IsLeftGeneratingTuple (fun i => f (a i)) := by
  obtain ⟨b, hb⟩ := ha
  refine ⟨fun i => f (b i), ?_⟩
  simpa only [map_sum, map_mul, map_one] using congrArg f hb

/-- Taking stars sends a left-generating tuple to a right-generating tuple;
the coefficient order is reversed exactly once. -/
theorem star
    {R : Type uR} [Semiring R] [StarRing R]
    {ι : Type uI} [Fintype ι]
    {a : ι → R} (ha : IsLeftGeneratingTuple a) :
    IsRightGeneratingTuple (fun i => Star.star (a i)) := by
  obtain ⟨b, hb⟩ := ha
  refine ⟨fun i => Star.star (b i), ?_⟩
  have hstarSum (x : ι → R) :
      Star.star (∑ i, x i) = ∑ i, Star.star (x i) :=
    map_sum (starAddEquiv : R ≃+ R) _ _
  calc
    (∑ i, Star.star (a i) * Star.star (b i)) =
        ∑ i, Star.star (b i * a i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [star_mul]
    _ = Star.star (∑ i, b i * a i) := (hstarSum fun i => b i * a i).symm
    _ = Star.star (1 : R) := congrArg Star.star hb
    _ = 1 := star_one R

end IsLeftGeneratingTuple

namespace IsRightGeneratingTuple

/-- A coefficient ring homomorphism carries a right-generating tuple to a
right-generating tuple. -/
theorem map
    {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
    {ι : Type uI} [Fintype ι]
    {a : ι → R} (ha : IsRightGeneratingTuple a) (f : R →+* S) :
    IsRightGeneratingTuple (fun i => f (a i)) := by
  obtain ⟨b, hb⟩ := ha
  refine ⟨fun i => f (b i), ?_⟩
  simpa only [map_sum, map_mul, map_one] using congrArg f hb

/-- Taking stars sends a right-generating tuple to a left-generating tuple. -/
theorem star
    {R : Type uR} [Semiring R] [StarRing R]
    {ι : Type uI} [Fintype ι]
    {a : ι → R} (ha : IsRightGeneratingTuple a) :
    IsLeftGeneratingTuple (fun i => Star.star (a i)) := by
  obtain ⟨b, hb⟩ := ha
  refine ⟨fun i => Star.star (b i), ?_⟩
  have hstarSum (x : ι → R) :
      Star.star (∑ i, x i) = ∑ i, Star.star (x i) :=
    map_sum (starAddEquiv : R ≃+ R) _ _
  calc
    (∑ i, Star.star (b i) * Star.star (a i)) =
        ∑ i, Star.star (a i * b i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [star_mul]
    _ = Star.star (∑ i, a i * b i) := (hstarSum fun i => a i * b i).symm
    _ = Star.star (1 : R) := congrArg Star.star hb
    _ = 1 := star_one R

end IsRightGeneratingTuple

/-- Over a commutative semiring the left and right generator predicates
coincide. -/
theorem isLeftGeneratingTuple_iff_isRightGeneratingTuple
    {R : Type uR} [CommSemiring R]
    {ι : Type uI} [Fintype ι] (a : ι → R) :
    IsLeftGeneratingTuple a ↔ IsRightGeneratingTuple a := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    calc
      (∑ i, a i * b i) = ∑ i, b i * a i := by
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _
      _ = 1 := hb
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    calc
      (∑ i, b i * a i) = ∑ i, a i * b i := by
        apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _
      _ = 1 := hb
