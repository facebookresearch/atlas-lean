/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Proof of the simplicity conjecture

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Dynamics.SimplicityConjecture` — annals_simplicity_conjecture (manifest `manifests/problems/annals_simplicity_conjecture.toml`, rev 1, submitter Thomas Browning, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Dynamics.SimplicityConjectureWanted` namespace. Mathematical
statements are unchanged. Source: D. Cristofaro-Gardiner, V. Humilière, and S. Seyfaddini, `Proof of the simplicity conjecture`, Annals of Math, 199 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-199-1-SimplicityConjecture.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Dynamics.FixedPoints.Support
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.Dynamics.SimplicityConjectureWanted
/-!
# Main Statement from Proof of the simplicity conjecture

We formalise the statement of the main result from D. Cristofaro-Gardiner, V. Humilière,
and S. Seyfaddini, `Proof of the simplicity conjecture`, Annals of Math, 199 (1) 2024.
-/

set_option autoImplicit false

namespace SimplicityConjecture

open Function Homeomorph MeasureTheory

/-- `𝔻` is the closed unit disc in `ℝ²`. -/
notation "𝔻" => Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1

/-- `𝔻ᵒ` is the interior of `𝔻`. -/
notation "𝔻ᵒ" => Subtype.val ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1

noncomputable instance : MeasureSpace 𝔻 := Measure.Subtype.measureSpace

/-- Area preserving homeomorphisms of `𝔻` that are the identity near the boundary. -/
def Homeo : Subgroup (𝔻 ≃ₜ 𝔻) where
  carrier := {ϕ | MeasurePreserving ϕ volume volume ∧ fixedSupport ϕ ⊆ 𝔻ᵒ}
  one_mem' := ⟨MeasurePreserving.id _, by simp [one_def, fixedSupport_def]⟩
  inv_mem' {ϕ} := .imp (.symm ϕ.toMeasurableEquiv)
    (by simp [inv_def, fixedSupport_def, ← coe_symm_toEquiv])
  mul_mem' {ϕ ψ} := fun ⟨hϕ1, hϕ2⟩ ⟨hψ1, hψ2⟩ ↦ ⟨hϕ1.comp hψ1, by
    rw [fixedSupport_def] at hϕ2 hψ2 ⊢
    have : fixedPoints ϕ ∩ fixedPoints ψ ⊆ fixedPoints (ϕ * ψ) := inter_subset_fixedPoints_comp
    grw [← this, Set.compl_inter, closure_union, hϕ2, hψ2, Set.union_self]⟩

/--
Statement of Theorem 1.2:

The group `Homeo_c(𝔻, ω)` is not simple.
Source: D. Cristofaro-Gardiner, V. Humilière, and S. Seyfaddini, `Proof of the simplicity conjecture`, Annals of Math, 199 (1) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-199-1-SimplicityConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_simplicity_conjecture`.
-/
public theorem_wanted theorem_1_2 : ¬ IsSimpleGroup Homeo

end SimplicityConjecture

end MathlibExt.Dynamics.SimplicityConjectureWanted
