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

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
public import Mathlib.Algebra.Group.Center

/-!
# Actual operator centralizers are strongly closed

For each fixed original bounded operator and vector, the commutation
relation is an equality of two continuous vector evaluations. Intersecting
these closed equalizers over the original set and all original vectors
shows its centralizer is closed in the pointwise operator topology. No
closedness or strong-limit commutation certificate is supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Topology

namespace MathlibExt.Analysis.CStarAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- **Strong closedness of an operator centralizer.** For a complex normed vector space `H` and any set
`S` of bounded complex-linear endomorphisms of `H`, the set of bounded operators commuting with
every element of `S` is closed in the strong operator topology, defined by uniform convergence on
finite subsets of `H`. -/
theorem isClosed_strongCentralizer (s : Set (H →L[ℂ] H)) :
    IsClosed {q : H →Lₚₜ[ℂ] H |
      (ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℂ) H
        {t : Set H | Finite t}).symm q ∈ Set.centralizer s} := by
  let P := ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℂ) H {t : Set H | Finite t}
  have hP (q : H →Lₚₜ[ℂ] H) (ξ : H) : P.symm q ξ = q ξ :=
    ContinuousLinearMap.toUniformConvergenceCLM_symm_apply
  have hset : {q : H →Lₚₜ[ℂ] H | P.symm q ∈ Set.centralizer s} =
      ⋂ A : s, ⋂ ξ : H, {q : H →Lₚₜ[ℂ] H | (A : H →L[ℂ] H) (q ξ) = q ((A : H →L[ℂ] H) ξ)} := by
    ext q
    simp only [Set.mem_iInter, mem_ofPred_eq]
    constructor
    · intro h A ξ
      have heq := (Set.mem_centralizer_iff.mp h) (A : H →L[ℂ] H) A.property
      have hvalue := congrArg (fun B : H →L[ℂ] H => B ξ) heq
      simpa only [mul_apply_eq_comp, hP] using hvalue
    · intro h
      apply Set.mem_centralizer_iff.mpr
      intro A hA
      apply ContinuousLinearMap.ext
      intro ξ
      change A (P.symm q ξ) = P.symm q (A ξ)
      simpa only [hP] using h ⟨A, hA⟩ ξ
  change IsClosed {q : H →Lₚₜ[ℂ] H | P.symm q ∈ Set.centralizer s}
  rw [hset]
  apply isClosed_iInter
  intro A
  apply isClosed_iInter
  intro ξ
  exact isClosed_eq
    ((A : H →L[ℂ] H).continuous.comp (continuous_eval_const ξ))
    (continuous_eval_const ((A : H →L[ℂ] H) ξ))

end

end MathlibExt.Analysis.CStarAlgebra
