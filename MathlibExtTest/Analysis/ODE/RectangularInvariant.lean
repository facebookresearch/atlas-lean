/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import MathlibExt.Analysis.ODE.RectangularInvariant

open Set MathlibExt.Analysis.ODE

-- A box consisting of one point is allowed, with zero rates on both faces.
example (a : ℝ) : ∃ x : ℝ → Fin 1 → ℝ, x a = 0 ∧
    (∀ t ∈ Ici a, x t ∈ Icc 0 0) ∧
    ∀ t ∈ Ici a, HasDerivAt x 0 t := by
  simpa using exists_forward_solution_in_Icc
    (F := fun _ : Fin 1 → ℝ => 0) (lo := 0) (hi := 0)
    (K := 0) (by simp) (LipschitzWith.const _).lipschitzOnWith
    (by simp) a (x₀ := 0) (by simp)

-- Empty coordinate sets do not require a spurious Nonempty assumption.
example (a : ℝ) : ∃ x : ℝ → Fin 0 → ℝ, x a = 0 ∧
    (∀ t ∈ Ici a, x t ∈ Icc 0 0) ∧
    ∀ t ∈ Ici a, HasDerivAt x 0 t := by
  simpa using exists_forward_solution_in_Icc
    (F := fun _ : Fin 0 → ℝ => 0) (lo := 0) (hi := 0)
    (K := 0) (by simp) (LipschitzWith.const _).lipschitzOnWith
    (by simp) a (x₀ := 0) (by simp)

-- Logistic dynamics are smooth but not globally Lipschitz. The finite index
-- type need not be Fin n; rates may vanish on both faces.
example : ∃ x : ℝ → Bool → ℝ, x (-3) = (fun _ => 1 / 2) ∧
    (∀ t ∈ Ici (-3), x t ∈ Icc 0 1) ∧
    ∀ t ∈ Ici (-3), HasDerivAt x (fun i => x t i * (1 - x t i)) t := by
  let F : (Bool → ℝ) → Bool → ℝ := fun y i => y i * (1 - y i)
  have hF : ContDiff ℝ 1 F := by
    dsimp [F]
    fun_prop
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_Icc : IsCompact (Icc (0 : Bool → ℝ) 1))
    hF.locallyLipschitz.locallyLipschitzOn
  exact exists_forward_solution_in_Icc (by intro i; norm_num) hK
    (by intro y hy i; constructor <;> intro h <;> simp [F, h])
    (-3) (by constructor <;> intro i <;> norm_num)

-- Invariance includes a closed endpoint and a singleton time interval.
example {a b : ℝ} {x : ℝ → Bool → ℝ}
    (hx : IsIntegralCurveOn x (fun _ y i => y i * (1 - y i)) (Icc a b))
    (h₀ : x a ∈ Icc 0 1) : MapsTo x (Icc a b) (Icc 0 1) := by
  have hF : ContDiff ℝ 1 (fun y : Bool → ℝ => fun i => y i * (1 - y i)) := by
    fun_prop
  exact mapsTo_Icc_of_inward (by intro i; norm_num) hF.locallyLipschitz
    (by intro y hy i; constructor <;> intro h <;> simp [h]) hx h₀

#print axioms MathlibExt.Analysis.ODE.exists_forward_solution_in_Icc
#print axioms MathlibExt.Analysis.ODE.mapsTo_Icc_of_inward
