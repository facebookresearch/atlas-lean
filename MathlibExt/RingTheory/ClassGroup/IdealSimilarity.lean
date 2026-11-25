/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Nonzero ideal similarity through the canonical class group

The AlgebraNotes definition says that two nonzero ideals `I`, `J` of a
Dedekind domain are similar when some fraction-field scalar sends `I` to `J`.
This file keeps only the source-facing name for equality under `ClassGroup.mk0`
on Mathlib's nonzero-ideal carrier `(Ideal R)⁰`.

The source formulation is `ClassGroup.mk0_eq_mk0_iff_exists_fraction_ring`;
`ClassGroup.mk0_eq_mk0_iff` gives the equivalent balanced nonzero scalar witnesses.
Equality supplies the relation laws, `map_mul` supplies multiplication, and
`ClassGroup.mk0_eq_one_iff` characterizes the unit class by principality.
No separate relation or relation calculus is defined here.

Source: `v1/Atlas/AlgebraNotes/targets.yaml`, Definition in the section
"Similarity Classes of Ideals", and `code/IdealFactorization.lean`.
-/

@[expose] public section

open scoped nonZeroDivisors

namespace IdealFactorization

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- **Similar ideals.** Let $R$ be a Dedekind domain. Two nonzero ideals $I$ and $J$ of $R$ are
similar when their classes in the ideal class group of $R$ are equal. -/
abbrev IdealsSimilar (I J : (Ideal R)⁰) : Prop := ClassGroup.mk0 I = ClassGroup.mk0 J

end IdealFactorization
