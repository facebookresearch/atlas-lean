/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Fourier.AddCircle.RiemannLebesgue
import MathlibExt.Analysis.HardySpace
import Mathlib.Analysis.Normed.Module.Complemented
import Mathlib.Tactic.NormNum

/-! # Tests for `MathlibExt.Analysis.HardySpace` -/

namespace MathlibExtTest.Analysis.HardySpace

open MeasureTheory MathlibExt.Analysis.HardySpaceWanted.Analysis

-- Test section: the Hardy space `H1`. The `L¹` class of a character of nonnegative frequency lies
-- in `H1`: its only nonzero Fourier coefficient is at its own frequency.
example : fourierLp (T := 1) 1 2 ∈ H1 := by
  intro k hk
  rw [fourierCoeff_congr_ae (coeFn_fourierLp 1 2), fourierCoeff_fourier, Pi.single_apply,
    ite_eq_right (by omega)]

-- The constant function `1` (the character of frequency `0`) lies in `H1`.
example : fourierLp (T := 1) 1 0 ∈ H1 := by
  intro k hk
  rw [fourierCoeff_congr_ae (coeFn_fourierLp 1 0), fourierCoeff_fourier, Pi.single_apply,
    ite_eq_right (by omega)]

-- A character of negative frequency does not: its coefficient at `-1` is `1`.
example : fourierLp (T := 1) 1 (-1) ∉ H1 := by
  intro h
  have h1 := h (-1) (by norm_num)
  rw [fourierCoeff_congr_ae (coeFn_fourierLp 1 (-1)), fourierCoeff_fourier,
    Pi.single_eq_same] at h1
  exact one_ne_zero h1

-- Each negative Fourier coefficient cuts out a closed kernel in L¹.
example : IsClosed (H1 : Set (Lp ℂ 1 (AddCircle.haarAddCircle (T := 1)))) := by
  let CircleL1 := Lp ℂ 1 (AddCircle.haarAddCircle (T := 1))
  change IsClosed {f : CircleL1 | ∀ n : ℤ, n < 0 → fourierCoeff f n = 0}
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun n => isClosed_iInter fun _ => ?_
  let c : CircleL1 →ₗ[ℂ] ℂ :=
    { toFun := fun f => fourierCoeff f n
      map_add' := fun f g => by
        rw [fourierCoeff_congr_ae (Lp.coeFn_add f g),
          fourierCoeff.add (L1.integrable_coeFn f) (L1.integrable_coeFn g)]
        rfl
      map_smul' := fun a f => by
        rw [fourierCoeff_congr_ae (Lp.coeFn_smul a f), fourierCoeff.const_smul]
        rfl }
  refine isClosed_eq (c.mkContinuous 1 ?_).continuous continuous_const
  intro f
  rw [one_mul, L1.norm_eq_integral_norm]
  exact MathlibExt.Analysis.Fourier.AddCircle.RiemannLebesgue.norm_fourierCoeff_le_integral_norm n

-- Test section: Newman's theorem. No bounded linear operator on `L¹` maps into `H1` and fixes
-- every element of `H1`.
example (P : Lp ℂ 1 (AddCircle.haarAddCircle (T := 1)) →L[ℂ]
      Lp ℂ 1 (AddCircle.haarAddCircle (T := 1)))
    (hP : ∀ f, P f ∈ H1) (hfix : ∀ f ∈ H1, P f = f) : False :=
  H1_not_closedComplemented ⟨P.codRestrict H1 hP, fun x => Subtype.ext (hfix x x.2)⟩

-- Equivalently, by the closed complement criterion in the Banach space `L¹`, `H1` is not a
-- closed subspace with a closed complement.
example : ¬ (IsClosed (H1 : Set (Lp ℂ 1 (AddCircle.haarAddCircle (T := 1)))) ∧
    ∃ q : Submodule ℂ (Lp ℂ 1 (AddCircle.haarAddCircle (T := 1))),
      IsClosed (q : Set (Lp ℂ 1 (AddCircle.haarAddCircle (T := 1)))) ∧ IsCompl H1 q) :=
  Submodule.closedComplemented_iff_isClosed_exists_isClosed_isCompl.not.mp
    H1_not_closedComplemented

end MathlibExtTest.Analysis.HardySpace
