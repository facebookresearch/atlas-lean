/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Basic
import Mathlib.Analysis.Normed.Ring.Units
import MathlibExt.Analysis.InnerProductSpace.LpShiftOperator

/-!
# Negative answer to Scottish Book Problem 173

On real `ℓ²`, the unilateral shift has an open neighborhood containing no invertible operators.
This refutes the proposed density of invertible operators on every real Banach space.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook173Wanted

/-- **Scottish Book Problem 173.** Eidelheit's claim that for every real Banach space $E$, the
bounded linear operators $E \to E$ that have a bounded linear two-sided inverse are dense, for
the operator norm, in the space of all bounded linear operators on $E$. -/
def ScottishBookProblem173Claim : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E],
    Dense {T : E →L[ℝ] E |
      ∃ S : E →L[ℝ] E,
        ContinuousLinearMap.comp T S = ContinuousLinearMap.id ℝ E ∧
          ContinuousLinearMap.comp S T = ContinuousLinearMap.id ℝ E}

open MathlibExt.Analysis.InnerProductSpace.LpShiftOperator
open scoped lp

/--
**Negative answer to Scottish Book Problem 173.** Eidelheit's claim in Problem 173 is false:
there is a real Banach space $E$ in which the bounded linear operators $E \to E$ that have a
bounded linear two-sided inverse are not dense, for the operator norm, in the space of all
bounded linear operators on $E$.

For instance, in an infinite-dimensional Hilbert space the invertible operators are not dense,
by the Fredholm-index obstruction: the unilateral shift cannot be approximated by invertible
operators.

Source: M. Eidelheit, Problem 173 of the
Scottish Book; see P. Halmos, A Hilbert Space Problem Book, Problem 109.
-/
theorem eidelheit173_refuted : ¬ ScottishBookProblem173Claim := by
  intro hdense
  let B := backwardCLM (𝕜 := ℝ)
  let S := shiftCLM (𝕜 := ℝ)
  have hBS : B * S = 1 := backward_comp_shift
  -- The operators T for which B * T is a unit form an open neighborhood of S.
  have hopen : IsOpen {T | IsUnit (B * T)} :=
    Units.isOpen.preimage (continuous_const.mul continuous_id)
  obtain ⟨T, hT, hBT⟩ := (hdense ℓ²(ℕ, ℝ)).exists_mem_open hopen
    ⟨S, show IsUnit (B * S) from hBS ▸ isUnit_one⟩
  -- If T is a unit there, then B is a unit and S must be its inverse.
  obtain ⟨u, rfl⟩ := isUnit_iff_exists.mpr hT
  obtain ⟨v, hv⟩ := (Units.isUnit_mul_units B u).mp hBT
  have hS : S = ↑v⁻¹ := v.eq_inv_of_mul_eq_one_left (hv.symm ▸ hBS)
  exact not_surjective_shiftCLM (𝕜 := ℝ)
    (show Function.Surjective S from hS ▸ (ContinuousLinearEquiv.ofUnit v⁻¹).surjective)

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook173Wanted
