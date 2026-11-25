/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DedekindDomain.SelmerGroupFinite

@[expose] public section

open IsDedekindDomain

universe u v

-- exactSource consumer, with the original binders.
example {R : Type u} [CommRing R] [IsDedekindDomain R] {K : Type v} [Field K] [Algebra R K]
    [IsFractionRing R K] {S : Set (HeightOneSpectrum R)} {n : ℕ} [Fact (0 < n)]
    [Finite (ClassGroup R)] [Monoid.FG Rˣ] [Finite S] :
    Finite (selmerGroup (R := R) (K := K) (S := S) (n := n)) :=
  IsDedekindDomain.selmerGroup.finite_of_finite_classGroup_of_fg_units

example :
    ∀ {R : Type u} [CommRing R] [IsDedekindDomain R] {K : Type v} [Field K] [Algebra R K]
      [IsFractionRing R K] {S : Set (HeightOneSpectrum R)} {n : ℕ} [Fact (0 < n)]
      [Finite (ClassGroup R)] [Monoid.FG Rˣ] [Finite S],
      Finite (selmerGroup (R := R) (K := K) (S := S) (n := n)) :=
  @IsDedekindDomain.selmerGroup.finite_of_finite_classGroup_of_fg_units

-- Boundary case: the empty set of places is finite, so the same conclusion
-- covers the Selmer group with no allowed ramification.
example {R : Type u} [CommRing R] [IsDedekindDomain R] {K : Type v} [Field K] [Algebra R K]
    [IsFractionRing R K] {n : ℕ} [Fact (0 < n)]
    [Finite (ClassGroup R)] [Monoid.FG Rˣ] :
    Finite (selmerGroup (R := R) (K := K) (S := (∅ : Set (HeightOneSpectrum R))) (n := n)) :=
  IsDedekindDomain.selmerGroup.finite_of_finite_classGroup_of_fg_units
