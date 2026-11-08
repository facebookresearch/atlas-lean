/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Places of a number field and residue norms
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

namespace NumberField

/-- The places of a number field: infinite places together with finite
places, using Mathlib's canonical `NumberField.FinitePlace K` API for
the finite places. -/
def Place (K : Type*) [Field K] [NumberField K] : Type _ :=
  InfinitePlace K ⊕ FinitePlace K

namespace Place

/-- An infinite place, viewed as a place. -/
def infinitePlace {K : Type*} [Field K] [NumberField K]
    (v : InfinitePlace K) : Place K :=
  Sum.inl v

/-- A finite place, viewed as a place. -/
def finitePlace {K : Type*} [Field K] [NumberField K]
    (v : FinitePlace K) : Place K :=
  Sum.inr v

end Place

namespace FinitePlace

/-- The residue-field cardinality `N(v)` at a finite place, as a real
number. This is the absolute norm of the corresponding prime ideal. -/
noncomputable def residueNorm {K : Type*} [Field K] [NumberField K]
    (v : FinitePlace K) : ℝ :=
  (Ideal.absNorm v.maximalIdeal.asIdeal : ℝ)

theorem one_le_residueNorm {K : Type*} [Field K] [NumberField K]
    (v : FinitePlace K) :
    1 ≤ v.residueNorm := by
  have hne : Ideal.absNorm v.maximalIdeal.asIdeal ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff]
    exact v.maximalIdeal.ne_bot
  unfold residueNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne

end FinitePlace

end NumberField
