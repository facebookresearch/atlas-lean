/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/














































































import Mathlib
import Code.OSSS.Integration

open scoped BigOperators
open Real Set Finset

set_option linter.style.longLine false

namespace StatMech
namespace Walls







noncomputable def osd_meanLogTerm (fseq : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (1 / Real.log n) * ∑ i ∈ Finset.Ico 1 (n + 1), fseq i x / (i : ℝ)





















theorem osd_logStep_sum_le_sum_deriv (fseq fpseq Sig : ℕ → ℝ) (n : ℕ)
    (hSrec : ∀ i, Sig (i + 1) = Sig i + fseq i)
    (hfnn : ∀ i, 1 ≤ i → 0 ≤ fseq i)
    (hSpos : ∀ i, 1 ≤ i → 0 < Sig i)
    (hdiff : ∀ i : ℕ, 1 ≤ i → ((i : ℝ) / Sig i) * fseq i ≤ fpseq i) :
    Real.log (Sig (n + 1)) - Real.log (Sig 1)
      ≤ ∑ i ∈ Finset.Ico 1 (n + 1), fpseq i / (i : ℝ) := by
  
  have hstep : ∀ i ∈ Finset.Ico 1 (n + 1),
      (Real.log (Sig (i + 1)) - Real.log (Sig i)) ≤ fpseq i / (i : ℝ) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hi1 : 1 ≤ i := hi.1
    have hipos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi1
    have hSi : 0 < Sig i := hSpos i hi1
    have hfi : 0 ≤ fseq i := hfnn i hi1
    
    have hlog : Real.log (Sig (i + 1)) - Real.log (Sig i) ≤ fseq i / Sig i := by
      rw [hSrec i]
      exact StatMech.OSSS.Integration.logStep_le (Sig i) (fseq i) hSi hfi
    
    have hdi : fseq i / Sig i ≤ fpseq i / (i : ℝ) := by
      have hd := hdiff i hi1
      rw [div_mul_eq_mul_div, div_le_iff₀ hSi] at hd
      rw [div_le_div_iff₀ hSi hipos]
      nlinarith [hd]
    linarith
  refine le_trans ?_ (Finset.sum_le_sum hstep)
  
  have htel : ∑ i ∈ Finset.Ico 1 (n + 1), (Real.log (Sig (i + 1)) - Real.log (Sig i))
      = Real.log (Sig (n + 1)) - Real.log (Sig 1) := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    have hcongr : ∀ x ∈ Finset.range n,
        (Real.log (Sig (1 + x + 1)) - Real.log (Sig (1 + x)))
          = (fun j => Real.log (Sig (j + 1 + 1)) - Real.log (Sig (j + 1))) x := by
      intro x _; ring_nf
    rw [Finset.sum_congr rfl hcongr]
    simpa using Finset.sum_range_sub (fun j => Real.log (Sig (j + 1))) n
  rw [htel]









theorem osd_hasDerivAt_meanLogTerm (fseq fpseq : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ)
    (hf : ∀ i x, HasDerivAt (fun x => fseq i x) (fpseq i x) x) :
    HasDerivAt (fun x => osd_meanLogTerm fseq n x)
      ((1 / Real.log n) * ∑ i ∈ Finset.Ico 1 (n + 1), fpseq i x / (i : ℝ)) x := by
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro i _
  exact (hf i x).div_const (i : ℝ)















theorem osd_telescope_deriv_value (fseq fpseq : ℕ → ℝ → ℝ) (Sig : ℕ → ℝ → ℝ)
    (n : ℕ) (x : ℝ) (hlogn : 0 < Real.log n)
    (hSrec : ∀ i, Sig (i + 1) x = Sig i x + fseq i x)
    (hfnn : ∀ i, 1 ≤ i → 0 ≤ fseq i x)
    (hSpos : ∀ i, 1 ≤ i → 0 < Sig i x)
    (hdiff : ∀ i : ℕ, 1 ≤ i → ((i : ℝ) / Sig i x) * fseq i x ≤ fpseq i x) :
    (Real.log (Sig (n + 1) x) - Real.log (Sig 1 x)) / Real.log n
      ≤ (1 / Real.log n) * ∑ i ∈ Finset.Ico 1 (n + 1), fpseq i x / (i : ℝ) := by
  have hnum := osd_logStep_sum_le_sum_deriv (fun i => fseq i x) (fun i => fpseq i x)
    (fun i => Sig i x) n hSrec hfnn hSpos hdiff
  rw [div_eq_inv_mul, one_div]
  exact mul_le_mul_of_nonneg_left hnum (by positivity)



















theorem osd_telescope_deriv (fseq fpseq : ℕ → ℝ → ℝ) (Sig : ℕ → ℝ → ℝ)
    (n : ℕ) (x : ℝ) (hlogn : 0 < Real.log n)
    (hf : ∀ i x, HasDerivAt (fun x => fseq i x) (fpseq i x) x)
    (hSrec : ∀ i, Sig (i + 1) x = Sig i x + fseq i x)
    (hfnn : ∀ i, 1 ≤ i → 0 ≤ fseq i x)
    (hSpos : ∀ i, 1 ≤ i → 0 < Sig i x)
    (hdiff : ∀ i : ℕ, 1 ≤ i → ((i : ℝ) / Sig i x) * fseq i x ≤ fpseq i x) :
    ∃ Tn' : ℝ,
      HasDerivAt (fun y => osd_meanLogTerm fseq n y) Tn' x
        ∧ (Real.log (Sig (n + 1) x) - Real.log (Sig 1 x)) / Real.log n ≤ Tn' := by
  refine ⟨(1 / Real.log n) * ∑ i ∈ Finset.Ico 1 (n + 1), fpseq i x / (i : ℝ), ?_, ?_⟩
  · exact osd_hasDerivAt_meanLogTerm fseq fpseq n x hf
  · exact osd_telescope_deriv_value fseq fpseq Sig n x hlogn hSrec hfnn hSpos hdiff





















example (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y => osd_meanLogTerm (fun i y => (i : ℝ) * y) n y)
      ((1 / Real.log n) * ∑ i ∈ Finset.Ico 1 (n + 1), (i : ℝ) / (i : ℝ)) x :=
  osd_hasDerivAt_meanLogTerm (fun i y => (i : ℝ) * y) (fun i _ => (i : ℝ)) n x
    (fun i y => by simpa using (hasDerivAt_id y).const_mul (i : ℝ))

end Walls
end StatMech
