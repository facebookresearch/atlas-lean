/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Eigenspace.CommonEigenvector

@[expose] public section

/-- exactSource consumer: the original binders apply verbatim. -/
example {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V]
    {ι : Type*} (T : ι → Module.End K V) (hT : Pairwise fun i j ↦ Commute (T i) (T j)) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ c : K, T i v = c • v :=
  Module.End.exists_forall_apply_eq_smul_of_pairwise_commute T hT

/-- Higher-universe consumer: field, space and index type in distinct universes. -/
example {K : Type 1} {V : Type 2} {ι : Type 3} [Field K] [IsAlgClosed K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (T : ι → Module.End K V) (hT : Pairwise fun i j ↦ Commute (T i) (T j)) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, ∃ c : K, T i v = c • v :=
  Module.End.exists_forall_apply_eq_smul_of_pairwise_commute T hT

/-- Boundary: the space must be nontrivial. On the zero space `PUnit` every
vector is `0`, so no family of endomorphisms has a common eigenvector. -/
example {K : Type*} [Field K] {ι : Type*} (T : ι → Module.End K PUnit) :
    ¬ ∃ v : PUnit, v ≠ 0 ∧ ∀ i, ∃ c : K, T i v = c • v := by
  rintro ⟨v, hv, -⟩
  exact hv (Subsingleton.elim _ _)
