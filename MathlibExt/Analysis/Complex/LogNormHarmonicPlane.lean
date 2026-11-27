/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_50.lean` (openbmb/ma-proofbench at commit
31bab4c78fd1b0c464e767d62e9202163d1e9029, byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench; L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782):
Copyright (c) 2026 OpenBMB.
Licensed under the MIT License:

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Authors (of MA-ProofBench, as listed on arXiv:2606.13782): Lushi Pu, Weiming Zhang, Xinheng Xie,
Zixuan Fu, Bingxiang He, Hongya Lyu, Xin Li, Jie Zhou, Yudong Wang.

The adapted portion is the statement of `harmonicOnNhd_log_norm_euclideanSpace_two` and its
docstring, formerly the `theorem_wanted` of the same name in
`WantedExt/Analysis/Complex/LogNormHarmonicPlaneWanted.lean`, whose notice recorded these changes
from the source: converted `theorem ma_proofbench_l1_50 … := by sorry` into the Batteries
`theorem_wanted` `harmonicOnNhd_log_norm_euclideanSpace_two`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Complex.LogNormHarmonicPlaneWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system. Further changes in this file: the
`theorem_wanted` is now a `theorem` with a proof, `public import Mathlib` is replaced by narrower
imports, and the informal problem statement in the docstring is restated in words (its source
citation is kept); the name, namespace and statement are unchanged.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# The logarithm of the norm is harmonic on the punctured plane

The function `x ↦ log ‖x‖` on the Euclidean plane `EuclideanSpace ℝ (Fin 2)` is harmonic on the
complement of the origin: near every point `x ≠ 0` it is twice continuously differentiable and its
Laplacian vanishes. This is the MA-ProofBench problem `ma_proofbench_l1_50`. More generally, the
same holds in every two-dimensional real inner product space.

## Proof

* The Laplacian commutes with linear isometry equivalences. If `L : E ≃ₗᵢ[ℝ] G` and `(vᵢ)` is an
  orthonormal basis of `E`, then `(L vᵢ)` is an orthonormal basis of `G`, and the second derivative
  of `f ∘ L` at `x` in the direction `vᵢ` is the second derivative of `f` at `L x` in the direction
  `L vᵢ`. Summing over `i` gives `Δ (f ∘ L) x = Δ f (L x)`. Since `L` is a linear homeomorphism, it
  follows that `f ∘ L` is harmonic at `x` exactly when `f` is harmonic at `L x`.
* On `ℂ`, the function `z ↦ log ‖z‖` is harmonic at every `z ≠ 0`: this is Mathlib's
  `AnalyticAt.harmonicAt_log_norm` applied to the identity (near `z`, `log ‖z‖` is the real part
  of a branch of the complex logarithm).
* An orthonormal basis of a two-dimensional real inner product space `E` gives a linear isometry
  equivalence `L : E ≃ₗᵢ[ℝ] ℂ` (`Complex.isometryOfOrthonormal`). It preserves norms, so
  `log ‖x‖ = log ‖L x‖`, and `L x ≠ 0` when `x ≠ 0`. The Euclidean plane has dimension `2`.

## Main results

* `laplacian_comp_linearIsometryEquiv`: `Δ (f ∘ L) = Δ f ∘ L` for a linear isometry equivalence
  `L` between finite-dimensional real inner product spaces.
* `harmonicAt_comp_linearIsometryEquiv_iff`: `f ∘ L` is harmonic at `x` if and only if `f` is
  harmonic at `L x`.
* `harmonicOnNhd_log_norm_of_finrank_eq_two`: in a two-dimensional real inner product space,
  `x ↦ log ‖x‖` is harmonic on the complement of the origin.
* `harmonicOnNhd_log_norm_euclideanSpace_two`: the case of the Euclidean plane
  `EuclideanSpace ℝ (Fin 2)`.

## Implementation notes

The main theorem keeps the name and the namespace it had as a `WantedExt` entry, and the auxiliary
results above share that namespace. The origin must be excluded: `log ‖x‖` tends to `-∞` as `x`
tends to `0`, while Lean's junk value `Real.log 0 = 0` is finite, so the function is not even
continuous at `0`.
-/

public section

open InnerProductSpace Laplacian Module
open scoped Topology

namespace MathlibExt.Analysis.Complex.LogNormHarmonicPlaneWanted

variable {E G F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Let $L : E \to G$ be a linear isometric equivalence between finite-dimensional real inner
product spaces. For every function $f : G \to F$ into a real normed space, the Laplacian
satisfies $\Delta(f \circ L) = (\Delta f) \circ L$. -/
theorem laplacian_comp_linearIsometryEquiv (f : G → F) (L : E ≃ₗᵢ[ℝ] G) :
    Δ (f ∘ L) = Δ f ∘ L := by
  ext x
  -- Compute both sides in an orthonormal basis `v` of `E` and its image `L ∘ v` in `G`.
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ L) (stdOrthonormalBasis ℝ E),
    laplacian_eq_iteratedFDeriv_orthonormalBasis f ((stdOrthonormalBasis ℝ E).map L)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := L.toContinuousLinearEquiv.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ
    (Set.mem_univ (L x)) 2
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at h
  rw [show f ∘ L = f ∘ L.toContinuousLinearEquiv from rfl, h]
  simp only [OrthonormalBasis.map_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  ext j
  fin_cases j <;> rfl

/-- Let $L : E \to G$ be a linear isometric equivalence between finite-dimensional real inner
product spaces, and let $f : G \to F$ take values in a real normed space. For each $x \in E$,
$f \circ L$ is harmonic at $x$ if and only if $f$ is harmonic at $Lx$. -/
theorem harmonicAt_comp_linearIsometryEquiv_iff {f : G → F} (L : E ≃ₗᵢ[ℝ] G) {x : E} :
    HarmonicAt (f ∘ L) x ↔ HarmonicAt f (L x) := by
  refine and_congr ?_ ?_
  · simpa using L.toContinuousLinearEquiv.contDiffAt_comp_iff (f := f) (n := 2) (x := L x)
  · have h : Filter.map L (𝓝 x) = 𝓝 (L x) := L.toHomeomorph.map_nhds_eq x
    rw [laplacian_comp_linearIsometryEquiv, ← h]
    rfl

/-- On `ℂ`, the function `z ↦ log ‖z‖` is harmonic on the complement of the origin. -/
private theorem harmonicOnNhd_log_norm_complex :
    HarmonicOnNhd (fun z : ℂ => Real.log ‖z‖) {0}ᶜ :=
  fun _ hz => analyticAt_id.harmonicAt_log_norm hz

/-- In a two-dimensional real inner product space `E`, the function `x ↦ log ‖x‖` is harmonic on
`E \ {0}`. -/
theorem harmonicOnNhd_log_norm_of_finrank_eq_two (hE : finrank ℝ E = 2) :
    HarmonicOnNhd (fun x : E => Real.log ‖x‖) {0}ᶜ := by
  intro x hx
  let L : E ≃ₗᵢ[ℝ] ℂ :=
    (Complex.isometryOfOrthonormal ((stdOrthonormalBasis ℝ E).reindex (finCongr hE))).symm
  have h : (fun x : E => Real.log ‖x‖) = (fun z : ℂ => Real.log ‖z‖) ∘ L :=
    funext fun y => congrArg Real.log (L.norm_map y).symm
  rw [h, harmonicAt_comp_linearIsometryEquiv_iff]
  exact harmonicOnNhd_log_norm_complex _ (L.map_eq_zero_iff.not.mpr hx)

/-- **The logarithm of the norm is harmonic on the punctured plane.** The function
$g(x) = \log|x|$, where $|x|$ is the Euclidean norm of $x \in \mathbb{R}^2$, is harmonic on
$\mathbb{R}^2 \setminus \{0\}$: near every point $x \ne 0$ it is twice continuously
differentiable and its Laplacian vanishes.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functions of a complex
variable; Geometric function theory), `benchmark/level1/ma_proofbench_l1_50.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem harmonicOnNhd_log_norm_euclideanSpace_two :
    InnerProductSpace.HarmonicOnNhd (fun x : EuclideanSpace ℝ (Fin 2) => Real.log ‖x‖) ({0}ᶜ) :=
  harmonicOnNhd_log_norm_of_finrank_eq_two finrank_euclideanSpace_fin

end MathlibExt.Analysis.Complex.LogNormHarmonicPlaneWanted
