/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Local injectivity from a nonsingular derivative

Mathlib's inverse function theorem already constructs a local inverse from a strict derivative
that is a continuous linear equivalence (`HasStrictFDerivAt.localInverse`, with
`HasStrictFDerivAt.eventually_left_inverse` and `HasStrictFDerivAt.eventually_right_inverse`).
This file names the immediate injectivity consequence: such a map is injective on a neighbourhood
of the base point.

The second theorem is the `C¹` form on finite-dimensional real spaces. It converts `C¹`
hypotheses to strict differentiability with `ContDiffAt.hasStrictFDerivAt'` before applying the
strict form; completeness is automatic in finite dimensions.

## Main results

* `exists_mem_nhds_injOn_of_hasStrictFDerivAt`: local injectivity from a nonsingular strict
  derivative on a complete space.
* `exists_mem_nhds_injOn_of_contDiffAt`: the finite-dimensional real `C¹` form.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace MathlibExt.Analysis.Calculus.LocalInverseBridge

/-- **Local injectivity.** If `f` has a strict Fréchet derivative at `a` that is a continuous
linear equivalence `f' : E ≃L[𝕜] F` and `E` is complete, then `f` is injective on a
neighbourhood of `a`. -/
theorem exists_mem_nhds_injOn_of_hasStrictFDerivAt {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {f' : E ≃L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ∃ s ∈ 𝓝 a, InjOn f s :=
  ⟨(hf.toOpenPartialHomeomorph f).source,
    (hf.toOpenPartialHomeomorph f).open_source.mem_nhds hf.mem_toOpenPartialHomeomorph_source,
    (hf.toOpenPartialHomeomorph f).injOn⟩

/-- **Local injectivity, `C¹` form.** Between finite-dimensional real normed spaces, if `f` is
`Cⁿ` at `a` for some `n ≠ 0` and its derivative at `a` is a continuous linear equivalence, then `f`
is injective on a neighbourhood of `a`. -/
theorem exists_mem_nhds_injOn_of_contDiffAt {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {f : E → F} {f' : E ≃L[ℝ] F} {a : E} {n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f a) (hf' : HasFDerivAt f (f' : E →L[ℝ] F) a) (hn : n ≠ 0) :
    ∃ s ∈ 𝓝 a, InjOn f s :=
  exists_mem_nhds_injOn_of_hasStrictFDerivAt (hf.hasStrictFDerivAt' hf' hn)

end MathlibExt.Analysis.Calculus.LocalInverseBridge
