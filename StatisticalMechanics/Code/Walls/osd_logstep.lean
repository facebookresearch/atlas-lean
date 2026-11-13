/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Code.OSSS.Integration

open Real

namespace StatMech.Walls









theorem osd_logStep_le (S f : ℝ) (hS : 0 < S) (hf : 0 ≤ f) :
    Real.log (S + f) - Real.log S ≤ f / S := by
  have hSf : 0 < S + f := by linarith
  rw [← Real.log_div (ne_of_gt hSf) (ne_of_gt hS)]
  have h1 : Real.log ((S + f) / S) ≤ (S + f) / S - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : (S + f) / S - 1 = f / S := by field_simp; ring
  linarith










theorem osd_logStep_telescope (Sig Signext fi : ℝ)
    (hSpos : 0 < Sig) (hfnn : 0 ≤ fi) (hrec : Signext = Sig + fi) :
    Real.log Signext - Real.log Sig ≤ fi / Sig := by
  subst hrec
  exact osd_logStep_le Sig fi hSpos hfnn






theorem osd_logStep_le_eq_integration :
    (@osd_logStep_le) = (@StatMech.OSSS.Integration.logStep_le) := rfl

end StatMech.Walls
