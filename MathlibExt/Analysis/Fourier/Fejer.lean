/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/FourierConvergence.lean` (leanprover/lean-eval,
https://github.com/leanprover/lean-eval), problem `fourier_dirichlet_fejer`, at commit
38361be884302c7edce1908c4aef8296eb2cb27e (manifest
`manifests/problems/fourier_dirichlet_fejer.toml`, rev 1, submitter Kim Morrison, status
archived): the definitions `fourierPartialSum` and `fourierCesaroMean` and the statement of
`fejer`, with the docstrings and comments they had in the wanted module
`WantedExt/Analysis/FourierConvergenceWanted.lean`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). Changes made: converted each
`@[eval_problem]` theorem into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with `Batteries.Util.ProofWanted`, inlined any
`LeanEval` helper modules, and placed the declarations in the
`MathlibExt.Analysis.FourierConvergenceWanted` namespace. Mathematical statements are unchanged.
Later change (ATLAS, 2026): the `theorem_wanted` `fejer` was proved, and it and the two
definitions moved from `WantedExt/Analysis/FourierConvergenceWanted.lean` to this `MathlibExt`
module with unchanged names, statements and docstrings; the imports of
`Batteries.Util.ProofWanted` and of all of Mathlib were replaced by narrower imports.

The rest of this file is new ATLAS work, not adapted from lean-eval: the proof of `fejer`, the
lemmas it uses, the module documentation and the linter options.
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import MathlibExt.Analysis.Fourier.AddCircle.C1FourierSummable
public import MathlibExt.Analysis.Fourier.AddCircle.CesaroMean
import MathlibExt.Analysis.Fourier.AddCircle.FejerTheorem

/-!
# Fejér's theorem on the real line

For a continuous `2π`-periodic `f : ℝ → ℂ`, the Cesàro means
`σ_N f = (S_0 f + ⋯ + S_N f) / (N + 1)` of the symmetric Fourier partial sums
`S_N f x = ∑_{|n| ≤ N} f̂ₙ e^{inx}` converge to `f` uniformly on `ℝ` (`fejer`; L. Fejér, 1900).
The coefficients `f̂ₙ` are Mathlib's `fourierCoeffOn Real.two_pi_pos f n`.

## Proof

ATLAS proves Fejér's theorem on the circle: `AddCircle.fejer_uniform_convergence` states that the
Cesàro–Fourier means `AddCircle.cesaroFourierMean` of a continuous function on `AddCircle T`
converge to it uniformly. A continuous `2π`-periodic `f` descends to a continuous function `F` on
`AddCircle (2 * π)`
(`MathlibExt.Analysis.Fourier.AddCircle.C1FourierSummable.liftPeriodicContinuousMap`), with
`F x = f x` at every real `x` and the same Fourier coefficients
(`fourierCoeff_liftPeriodicContinuousMap`). The circle character `fourier n` at a real point `x`
is `e^{inx}`, so the real-line partial sums and Cesàro means of `f` are those of `F` at `x`
(`fourierPartialSum_eq_partialFourierSum`, `fourierCesaroMean_eq_cesaroFourierMean`), and the
circle theorem pulls back along `x ↦ (x : AddCircle (2 * π))`.

## Implementation notes

The definitions and the statement keep the full names they had in the wanted module
`WantedExt/Analysis/FourierConvergenceWanted.lean`, so the namespace still reads
`FourierConvergenceWanted` and repeats `Analysis`. Each declaration has a local
`dupNamespace` exception.

## References

* L. Fejér (1900). Listed as §46 in O. Knill, *Some Fundamental Theorems in Mathematics*; this is
  the source cited by problem `fourier_dirichlet_fejer` of the lean-eval benchmark
  (leanprover/lean-eval), from which the definitions and the statement are taken.
-/

@[expose] public section

namespace MathlibExt.Analysis.FourierConvergenceWanted
namespace Analysis

open Filter Topology

set_option linter.dupNamespace false in
/-- The symmetric Fourier partial sum of `f : ℝ → ℂ` on the period `[0, 2π]`:
`S_N(f)(x) = ∑_{n = -N}^{N} f̂_n · e^{inx}`, with `f̂_n = fourierCoeffOn _ f n`. -/
noncomputable def fourierPartialSum (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
    fourierCoeffOn Real.two_pi_pos f n * Complex.exp (Complex.I * (n : ℂ) * (x : ℂ))

set_option linter.dupNamespace false in
/-- The Cesàro mean of the first `N + 1` Fourier partial sums:
`σ_N(f)(x) = (S_0(f)(x) + S_1(f)(x) + ⋯ + S_N(f)(x)) / (N + 1)`. -/
noncomputable def fourierCesaroMean (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  (∑ k ∈ Finset.range (N + 1), fourierPartialSum f k x) / (N + 1 : ℂ)

open MathlibExt.Analysis.Fourier.AddCircle.C1FourierSummable

section Bridge

set_option linter.dupNamespace false in
/-- The circle character `fourier n` at a real point `x` of `AddCircle (2 * π)` is `e^{inx}`. -/
theorem fourier_coe_two_pi (n : ℤ) (x : ℝ) :
    (fourier n (x : AddCircle (2 * Real.pi)) : ℂ) = Complex.exp (Complex.I * n * x) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

variable [Fact (0 < 2 * Real.pi)]
variable {f : ℝ → ℂ} (hper : Function.Periodic f (2 * Real.pi)) (hcont : Continuous f)

set_option linter.dupNamespace false in
/-- A continuous `2π`-periodic function and its descent to `AddCircle (2 * π)` agree at every real
point. -/
theorem liftPeriodicContinuousMap_coe_two_pi (x : ℝ) :
    liftPeriodicContinuousMap hper hcont (x : AddCircle (2 * Real.pi)) = f x := by
  have hmem := toIocMod_mem_Ioc Real.two_pi_pos 0 x
  rw [zero_add] at hmem
  have hcoe : ((toIocMod Real.two_pi_pos 0 x : ℝ) : AddCircle (2 * Real.pi)) = x := by
    rw [← self_sub_toIocDiv_zsmul, AddCircle.coe_sub, AddCircle.coe_zsmul, AddCircle.coe_period,
      smul_zero, sub_zero]
  rw [← hcoe, liftPeriodicContinuousMap_apply hper hcont hmem, ← self_sub_toIocDiv_zsmul]
  exact hper.sub_zsmul_eq _

set_option linter.dupNamespace false in
/-- The real-line partial sum of a continuous `2π`-periodic `f` at `x` is the circle partial
sum of its descent to `AddCircle (2 * π)` at `x`. -/
theorem fourierPartialSum_eq_partialFourierSum (N : ℕ) (x : ℝ) :
    fourierPartialSum f N x =
      AddCircle.partialFourierSum (liftPeriodicContinuousMap hper hcont) N x := by
  unfold fourierPartialSum AddCircle.partialFourierSum
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [fourierCoeff_liftPeriodicContinuousMap Real.two_pi_pos hper hcont n, fourier_coe_two_pi,
    smul_eq_mul]

set_option linter.dupNamespace false in
/-- The real-line Cesàro mean of a continuous `2π`-periodic `f` at `x` is the circle
Cesàro–Fourier mean of its descent to `AddCircle (2 * π)` at `x`. -/
theorem fourierCesaroMean_eq_cesaroFourierMean (N : ℕ) (x : ℝ) :
    fourierCesaroMean f N x =
      AddCircle.cesaroFourierMean (liftPeriodicContinuousMap hper hcont) N x := by
  unfold fourierCesaroMean AddCircle.cesaroFourierMean
  simp_rw [fourierPartialSum_eq_partialFourierSum hper hcont, smul_eq_mul, div_eq_inv_mul]

end Bridge

set_option linter.dupNamespace false in
/- **Fejér's theorem** (§46). For every *continuous* 2π-periodic complex
function `f` — without the `C¹` hypothesis of Dirichlet's theorem — the Cesàro
means `σ_N(f)` of the symmetric Fourier partial sums converge to `f` uniformly
on `ℝ`. -/
/-- Source: P. G. L. Dirichlet (1829) and L. Fejér (1900). Listed as §46 in O. Knill, Some Fundamental Theorems in Mathematics (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `fourier_dirichlet_fejer`. -/
theorem fejer
    {f : ℝ → ℂ} (_hperiod : Function.Periodic f (2 * Real.pi)) (_hcont : Continuous f) :
    TendstoUniformly (fun N : ℕ => fourierCesaroMean f N) f atTop := by
  have : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩
  have h := (AddCircle.fejer_uniform_convergence
    (liftPeriodicContinuousMap _hperiod _hcont)).comp (fun x : ℝ ↦ (x : AddCircle (2 * Real.pi)))
  convert h using 1
  · funext N x
    exact fourierCesaroMean_eq_cesaroFourierMean _hperiod _hcont N x
  · funext x
    exact (liftPeriodicContinuousMap_coe_two_pi _hperiod _hcont x).symm

end Analysis

end MathlibExt.Analysis.FourierConvergenceWanted
