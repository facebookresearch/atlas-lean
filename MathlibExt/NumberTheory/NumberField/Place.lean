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

/-- **Places of a number field.** For a number field $K$, the places of $K$ form the disjoint union
of the infinite places of $K$ (the absolute values coming from complex embeddings of $K$) and the
finite places of $K$ (the absolute values coming from nonzero prime ideals of the ring of
integers $\mathcal{O}_K$). -/
def Place (K : Type*) [Field K] [NumberField K] : Type _ :=
  InfinitePlace K ⊕ FinitePlace K

namespace Place

/-- **Infinite places as places.** For a number field $K$, each infinite place $v$ of $K$ is
regarded as a place of $K$ via the inclusion of the infinite places into the disjoint union of the
infinite and finite places of $K$. -/
def infinitePlace {K : Type*} [Field K] [NumberField K]
    (v : InfinitePlace K) : Place K :=
  Sum.inl v

/-- **Finite places as places.** For a number field $K$, each finite place $v$ of $K$ is regarded
as a place of $K$ via the inclusion of the finite places into the disjoint union of the infinite
and finite places of $K$. -/
def finitePlace {K : Type*} [Field K] [NumberField K]
    (v : FinitePlace K) : Place K :=
  Sum.inr v

end Place

namespace FinitePlace

/-- **Residue norm of a finite place.** Let $v$ be a finite place of a number field $K$ and
$\mathfrak{p}_v$ the corresponding nonzero prime ideal of the ring of integers $\mathcal{O}_K$. The
residue norm $N(v)$ is the absolute norm $|\mathcal{O}_K / \mathfrak{p}_v|$ of $\mathfrak{p}_v$, the
cardinality of the residue field at $v$, regarded as a real number. -/
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
