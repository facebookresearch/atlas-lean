/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.CorrelationLength








namespace StatMech
namespace Exact3D



theorem hasCriticalNu_of_eventually_logSlope_eq {ι : Type*} (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ) (ν : ℝ)
    (h :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        logSlope M correlationLength β = ν) :
    HasCriticalNu M correlationLength ν := by
  unfold HasCriticalNu
  exact Filter.Tendsto.congr' (h.mono fun _ hβ => hβ.symm) tendsto_const_nhds



theorem logSlope_eq_of_exact_power {ι : Type*} (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ) (ν β : ℝ)
    (hβ : M.betaC - β ∈ Set.Ioo (0 : ℝ) 1)
    (hξ :
      correlationLength β =
        Real.exp (-ν * Real.log (M.betaC - β))) :
    logSlope M correlationLength β = ν := by
  have hpos : 0 < M.betaC - β := hβ.1
  have hlt : M.betaC - β < 1 := hβ.2
  have hlog_ne : Real.log (M.betaC - β) ≠ 0 :=
    (Real.log_neg hpos hlt).ne
  simp [logSlope, hξ, hlog_ne]



theorem hasCriticalNu_of_eventually_exact_power {ι : Type*} (M : CriticalModel ι)
    (correlationLength : ℝ → ℝ) (ν : ℝ)
    (hξ :
      ∀ᶠ β in nhdsWithin M.betaC (Set.Iio M.betaC),
        correlationLength β =
          Real.exp (-ν * Real.log (M.betaC - β))) :
    HasCriticalNu M correlationLength ν := by
  refine hasCriticalNu_of_eventually_logSlope_eq M correlationLength ν ?_
  filter_upwards
    [hξ,
      Ioo_mem_nhdsLT (show M.betaC - 1 < M.betaC by linarith)] with β hξβ hβ
  have hdiff : M.betaC - β ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hβ.1, hβ.2]
  exact logSlope_eq_of_exact_power M correlationLength ν β hdiff hξβ

end Exact3D
end StatMech
