/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.Completion.FiniteLiesOverInstances
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Local degree bound under finite-place completion

For a number-field extension `L / K` and finite places `v` of `K` and `w`
of `L` with `w` lying over `v`, the local degree is bounded by the global
degree: `finrank Kv Lw ≤ finrank K L`.

## Primary source and ATLAS connection

The mathematical source is MIT 18.785, *Number Theory I*, Lecture 11,
Theorem 11.23(1), page 8:
<https://ocw.mit.edu/courses/18-785-number-theory-i-fall-2021/mit18_785f21_lec11.pdf>.
For a finite separable extension and a prime above the base prime, that theorem
identifies the local degree with the corresponding ramification-index times
residue-degree term; the sum of those terms is the global degree.  The result
below is the number-field specialization of the resulting inequality for one
chosen prime.  It formalizes only this inequality, not the equality of the sum.

ATLAS `NumberTheoryI` item N234 is downstream motivation rather than the
source of this statement.  The bound is a local-degree-control prerequisite
toward replacing part of the admitted completion-identification helpers in
`v1/Atlas/NumberTheoryI/code/LocalGlobal.lean` lines 418--763:
<https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/LocalGlobal.lean#L418-L763>
Root transport and the completion equivalence remain later stages.

Source-to-API map:

* Source finite places `v`, `w` with `w` over `v` are native
  `v : HeightOneSpectrum (𝓞 K)` and `w : HeightOneSpectrum (𝓞 L)` with
  `[w.asIdeal.LiesOver v.asIdeal]`.
* Source completions `Kv`, `Lw` are native `v.adicCompletion K` and
  `w.adicCompletion L`; the source completion embeddings are the scoped
  `Algebra` instance from `FiniteLiesOverInstances` (canonical map
  `adicCompletionMap v w`).
* The Lean proof uses
  `w.denseRange_algebraMap L` for density of the global field in its
  completion, and `Submodule.closed_of_finiteDimensional` for closedness
  of the range of the tensor-product lift.
* The dense-range plus closed finite-dimensional range argument establishing
  surjectivity of that lift adapts the construction used by the pinned Mathlib
  `Module.Finite` instance in
  [`FinitePlace.lean` lines 498--508](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/NumberTheory/NumberField/Completion/FinitePlace.lean#L498-L508).
* The Lean dimension comparison is `LinearMap.finrank_le_finrank_of_surjective`
  applied to the surjection `Kv ⊗[K] L →ₗ[Kv] Lw`, composed with
  `Module.finrank_baseChange` identifying
  `finrank Kv (Kv ⊗[K] L)` with `finrank K L`.

Scope: this module proves only the local/global degree inequality, a
dimension input toward N234; it does not identify completions with local
fields or prove any tensor-product equivalence.
-/

@[expose] public section

namespace IsDedekindDomain.HeightOneSpectrum

open scoped NumberField NumberField.LiesOver TensorProduct Valued

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L]

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- **Local degree is at most the global degree.** Let $L/K$ be an extension of number fields,
let $v$ be a nonzero prime ideal of $\mathcal{O}_K$ (a finite place of $K$) and let $w$ be a
nonzero prime ideal of $\mathcal{O}_L$ lying over $v$. Regard the $w$-adic completion $L_w$ as
an algebra over the $v$-adic completion $K_v$ via the canonical map $K_v \to L_w$. Then the
dimension of $L_w$ over $K_v$ is at most $[L : K]$. -/
theorem finrank_adicCompletion_le :
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) ≤
      Module.finrank K L := by
  let Φ : v.adicCompletion K ⊗[K] L →ₗ[v.adicCompletion K]
      w.adicCompletion L :=
    (Algebra.TensorProduct.lift
      (Algebra.algHom (v.adicCompletion K) (v.adicCompletion K)
        (w.adicCompletion L))
      (Algebra.algHom K L (w.adicCompletion L))
      (fun _ _ => mul_comm ..)).toLinearMap
  have h_dense : DenseRange Φ := by
    apply (w.denseRange_algebraMap L).mono
    rintro _ ⟨l, rfl⟩
    exact ⟨1 ⊗ₜ l, by simp [Φ, Algebra.algHom]⟩
  have h_surjective : Function.Surjective Φ := by
    rw [← Set.range_eq_univ, ← Φ.coe_range,
      ← Φ.range.closed_of_finiteDimensional.closure_eq]
    exact h_dense.closure_range
  calc
    Module.finrank (v.adicCompletion K) (w.adicCompletion L) ≤
        Module.finrank (v.adicCompletion K)
          (v.adicCompletion K ⊗[K] L) :=
      LinearMap.finrank_le_finrank_of_surjective h_surjective
    _ = Module.finrank K L := Module.finrank_baseChange

end IsDedekindDomain.HeightOneSpectrum
