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

Let R be a semiring, I a finite index type and a:I→R. The tuple is left-generating when
∃c:I→R, ∑i c_i*a_i=1, and right-generating when ∃c:I→R, ∑i a_i*c_i=1. These orientations
differ over a noncommutative semiring; the left equation is Rieffel's Lg_n convention.
Coefficient homomorphisms preserve both, and star reverses their orientation.
-/

public section

open scoped BigOperators

universe uR uS uI

/-- **Tuple generating the unit with left coefficients.**

Let R be a semiring, I a finite index type and a:I→R. The tuple is left-generating when
∃c:I→R, ∑i c_i*a_i=1, and right-generating when ∃c:I→R, ∑i a_i*c_i=1. IsLeftGeneratingTuple a
is the left equation ∑i c_i*a_i=1 for some c.
-/
@[expose] def IsLeftGeneratingTuple
    {R : Type uR} [Semiring R] {ι : Type uI} [Fintype ι]
    (a : ι → R) : Prop :=
  ∃ b : ι → R, ∑ i, b i * a i = 1

/-- **Tuple generating the unit with right coefficients.**

Let R be a semiring, I a finite index type and a:I→R. The tuple is left-generating when
∃c:I→R, ∑i c_i*a_i=1, and right-generating when ∃c:I→R, ∑i a_i*c_i=1. IsRightGeneratingTuple a
is the right equation ∑i a_i*c_i=1 for some c.
-/
@[expose] def IsRightGeneratingTuple
    {R : Type uR} [Semiring R] {ι : Type uI} [Fintype ι]
    (a : ι → R) : Prop :=
  ∃ b : ι → R, ∑ i, a i * b i = 1

namespace IsLeftGeneratingTuple

/-- **Coefficient homomorphisms preserve left-generating tuples.**

Let R be a semiring, I a finite index type and a:I→R. The tuple is left-generating when
∃c:I→R, ∑i c_i*a_i=1, and right-generating when ∃c:I→R, ∑i a_i*c_i=1. For a semiring S and
homomorphism f:R→S, left generation of a implies left generation of (f(a_i))_i, with
coefficients f(c_i).
-/
theorem map
    {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
    {ι : Type uI} [Fintype ι]
    {a : ι → R} (ha : IsLeftGeneratingTuple a) (f : R →+* S) :
    IsLeftGeneratingTuple (fun i => f (a i)) := by
  obtain ⟨b, hb⟩ := ha
  refine ⟨fun i => f (b i), ?_⟩
  simpa only [map_sum, map_mul, map_one] using congrArg f hb

/-- **Star sends left generation to right generation.**

Let R be a semiring, I a finite index type and a:I→R. The tuple is left-generating when
∃c:I→R, ∑i c_i*a_i=1, and right-generating when ∃c:I→R, ∑i a_i*c_i=1. If R is a star ring and
a is left-generating, then (star(a_i))_i is right-generating, using coefficients star(c_i).
-/
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

/-- **Coefficient homomorphisms preserve right-generating tuples.**

Let R be a semiring, I a finite index type and a:I→R. The tuple is left-generating when
∃c:I→R, ∑i c_i*a_i=1, and right-generating when ∃c:I→R, ∑i a_i*c_i=1. For a semiring S and
homomorphism f:R→S, right generation of a implies right generation of (f(a_i))_i.
-/
theorem map
    {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
    {ι : Type uI} [Fintype ι]
    {a : ι → R} (ha : IsRightGeneratingTuple a) (f : R →+* S) :
    IsRightGeneratingTuple (fun i => f (a i)) := by
  obtain ⟨b, hb⟩ := ha
  refine ⟨fun i => f (b i), ?_⟩
  simpa only [map_sum, map_mul, map_one] using congrArg f hb

/-- **Star sends right generation to left generation.**

Let R be a semiring, I a finite index type and a:I→R. The tuple is left-generating when
∃c:I→R, ∑i c_i*a_i=1, and right-generating when ∃c:I→R, ∑i a_i*c_i=1. If R is a star ring and
a is right-generating, then (star(a_i))_i is left-generating.
-/
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

/-- **Left and right generating equations agree in a commutative semiring.**

Let R be a semiring, I a finite index type and a:I→R. The tuple is left-generating when
∃c:I→R, ∑i c_i*a_i=1, and right-generating when ∃c:I→R, ∑i a_i*c_i=1. If R is commutative,
IsLeftGeneratingTuple a↔IsRightGeneratingTuple a.
-/
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
