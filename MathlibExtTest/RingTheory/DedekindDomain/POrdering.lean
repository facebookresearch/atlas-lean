/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DedekindDomain.POrdering

@[expose] public section

/-!
# Tests for the Bhargava p-ordering module
-/

open IsDedekindDomain.HeightOneSpectrum

/-- Stage zero: every candidate has valuation zero. -/
theorem test_val_zero
    {R : Type*} [CommRing R]
    (p : IsDedekindDomain.HeightOneSpectrum R) (a : ℕ → R)
    (x : R) : pOrderingValuation p a 0 x = 0 :=
  pOrderingValuation_zero p a x

/-- Stage zero: the chosen term ties every other candidate. -/
theorem test_val_zero_tie
    {R : Type*} [CommRing R]
    (p : IsDedekindDomain.HeightOneSpectrum R) (a : ℕ → R)
    (x : R) :
    pOrderingValuation p a 0 (a 0) ≤ pOrderingValuation p a 0 x := by
  rw [pOrderingValuation_zero, pOrderingValuation_zero]

/-- The valuation unfolds to the stated prefix product. -/
theorem test_val_unfold
    {R : Type*} [CommRing R]
    (p : IsDedekindDomain.HeightOneSpectrum R) (a : ℕ → R)
    (n : ℕ) (x : R) :
    pOrderingValuation p a n x =
      emultiplicity p.asIdeal
        (Ideal.span {(Finset.range n).prod fun k => x - a k}) :=
  rfl

/-- Exact prefix indexing: the stage `n + 1` product splits. -/
theorem test_prefix_succ
    {R : Type*} [CommRing R]
    (a : ℕ → R) (n : ℕ) (x : R) :
    (Finset.range (n + 1)).prod (fun k => x - a k) =
      ((Finset.range n).prod (fun k => x - a k)) * (x - a n) :=
  Finset.prod_range_succ _ _

/-- Projection: infinitude. -/
theorem test_proj_infinite
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {p : IsDedekindDomain.HeightOneSpectrum R} {S : Set R}
    {a : ℕ → R} (h : IsPOrdering p S a) : S.Infinite :=
  h.infinite

/-- Projection: sequence membership. -/
theorem test_proj_mem
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {p : IsDedekindDomain.HeightOneSpectrum R} {S : Set R}
    {a : ℕ → R} (h : IsPOrdering p S a) (n : ℕ) : a n ∈ S :=
  h.mem n

/-- Projection: minimum property. -/
theorem test_proj_min
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {p : IsDedekindDomain.HeightOneSpectrum R} {S : Set R}
    {a : ℕ → R} (h : IsPOrdering p S a) (n : ℕ) (x : R)
    (hx : x ∈ S) :
    pOrderingValuation p a n (a n) ≤ pOrderingValuation p a n x :=
  h.min_le n x hx

/-- Projection: minimum property as `IsLeast`. -/
theorem test_proj_isLeast
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {p : IsDedekindDomain.HeightOneSpectrum R} {S : Set R}
    {a : ℕ → R} {n : ℕ} (h : IsPOrdering p S a) :
    IsLeast (pOrderingValuation p a n '' S)
      (pOrderingValuation p a n (a n)) :=
  h.isLeast

/-- The constructor rebuilds the predicate. -/
theorem test_constructor
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {p : IsDedekindDomain.HeightOneSpectrum R} {S : Set R}
    {a : ℕ → R} (h : IsPOrdering p S a) :
    IsPOrdering p S a :=
  IsPOrdering.intro h.infinite h.mem (fun n x hx => h.min_le n x hx)

/-- The unfolding characterization fires on a hypothesis. -/
theorem test_unfold_roundtrip
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {p : IsDedekindDomain.HeightOneSpectrum R} {S : Set R}
    {a : ℕ → R} (h : IsPOrdering p S a) :
    S.Infinite ∧ (∀ n, a n ∈ S) ∧
      ∀ n, ∀ x ∈ S,
        pOrderingValuation p a n (a n) ≤
          pOrderingValuation p a n x :=
  isPOrdering_unfold.mp h

/-- Positive-stage characterization, forward direction. -/
theorem test_pos_forward
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {p : IsDedekindDomain.HeightOneSpectrum R} {S : Set R}
    {a : ℕ → R} (h : IsPOrdering p S a) :
    S.Infinite ∧ (∀ n, a n ∈ S) ∧
      ∀ n, 1 ≤ n → ∀ x ∈ S,
        pOrderingValuation p a n (a n) ≤
          pOrderingValuation p a n x :=
  isPOrdering_iff_pos.mp h

/-- Positive-stage characterization, backward direction. -/
theorem test_pos_backward
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {p : IsDedekindDomain.HeightOneSpectrum R} {S : Set R}
    {a : ℕ → R}
    (h : S.Infinite ∧ (∀ n, a n ∈ S) ∧
      ∀ n, 1 ≤ n → ∀ x ∈ S,
        pOrderingValuation p a n (a n) ≤
          pOrderingValuation p a n x) :
    IsPOrdering p S a :=
  isPOrdering_iff_pos.mpr h
