/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_59.lean` (openbmb/ma-proofbench at commit
31bab4c78fd1b0c464e767d62e9202163d1e9029; MA-ProofBench, L. Pu et al., arXiv:2606.13782):
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

Attribution and modification notice: the statement of
`tendsto_apply_iff_tendsto_inner_and_tendsto_inner_adjoint_comp` below is taken from
openbmb/ma-proofbench at commit 31bab4c78fd1b0c464e767d62e9202163d1e9029,
`benchmark/level2/ma_proofbench_l2_59.lean` (MA-ProofBench, L. Pu et al., *MA-ProofBench: A
Two-Tiered Evaluation of LLMs for Theorem Proving in Mathematical Analysis*, arXiv:2606.13782;
byte-identical to the Hugging Face dataset openbmb/MA-ProofBench), distributed under the MIT
License above. Changes made: converted the benchmark theorem `ma_proofbench_l2_59`, whose proof
there is a placeholder, into the Batteries wanted-theorem declaration
`tendsto_apply_iff_tendsto_inner_and_tendsto_inner_adjoint_comp` (a statement without a proof);
moved the informal problem statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.OperatorTheory.StrongOperatorConvergenceIffWeakAndAdjointWanted`; replaced
`import Mathlib` by `public import Mathlib` under the module system. Further changes in this file:
that wanted declaration is now a `theorem` with a proof, and `public import Mathlib` is replaced by
narrower imports; the statement and its docstring are unchanged.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Strong operator convergence through weak operator convergence of `Tₙ` and `Tₙ† Tₙ`

Let `Tₙ` and `T` be bounded operators on a real or complex Hilbert space `H`. Then `Tₙ x → T x`
for every `x`, that is, `Tₙ → T` in the strong operator topology, if and only if
`⟪y, Tₙ x⟫ → ⟪y, T x⟫` and `⟪y, Tₙ† (Tₙ x)⟫ → ⟪y, T† (T x)⟫` for all `x` and `y`, that is,
`Tₙ → T` and `Tₙ† Tₙ → T† T` in the weak operator topology.

Strong convergence gives both weak limits by continuity of the inner product, since
`⟪y, Tₙ† (Tₙ x)⟫ = ⟪Tₙ y, Tₙ x⟫`. Conversely,
`‖Tₙ x - T x‖² = re ⟪Tₙ x, Tₙ x⟫ - 2 re ⟪T x, Tₙ x⟫ + ‖T x‖²`, and both
`⟪Tₙ x, Tₙ x⟫ = ⟪x, Tₙ† (Tₙ x)⟫` and `⟪T x, Tₙ x⟫` tend to `⟪T x, T x⟫ = ‖T x‖²`, so
`‖Tₙ x - T x‖² → 0`.

## Main statements

* `tendsto_apply_iff_tendsto_inner_and_tendsto_inner_adjoint_comp`: the characterization above.
  This is the MA-ProofBench problem `ma_proofbench_l2_59`, formerly a `WantedExt` entry.

## Implementation notes

`Mathlib.Analysis.InnerProductSpace.Adjoint`, which defines `ContinuousLinearMap.adjoint`, is
imported publicly; under it the statement elaborates to the same term as under `import Mathlib`,
where it was first stated.

## References

* L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem Proving in
  Mathematical Analysis*, arXiv:2606.13782, Level II, problem `ma_proofbench_l2_59`.
-/

@[expose] public section

open scoped Topology

namespace MathlibExt.Analysis.OperatorTheory.StrongOperatorConvergenceIffWeakAndAdjointWanted

open Filter in
/-- In an inner product space, `u a → v` as soon as `⟪v, u a⟫ → ⟪v, v⟫` and
`⟪u a, u a⟫ → ⟪v, v⟫`: then `‖u a - v‖² = re ⟪u a, u a⟫ - 2 re ⟪v, u a⟫ + ‖v‖²` tends to
`‖v‖² - 2 ‖v‖² + ‖v‖² = 0`. -/
private theorem tendsto_of_tendsto_inner_of_tendsto_inner_self {𝕜 E α : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {l : Filter α} {u : α → E} {v : E}
    (hw : Tendsto (fun a => inner 𝕜 v (u a)) l (𝓝 (inner 𝕜 v v)))
    (hn : Tendsto (fun a => inner 𝕜 (u a) (u a)) l (𝓝 (inner 𝕜 v v))) :
    Tendsto u l (𝓝 v) := by
  have hsq : Tendsto (fun a => ‖u a - v‖ ^ 2) l (𝓝 0) := by
    have h := (((RCLike.continuous_re.tendsto _).comp hn).sub
      (((RCLike.continuous_re.tendsto _).comp hw).const_mul 2)).add_const (‖v‖ ^ 2)
    rw [inner_self_eq_norm_sq, show ‖v‖ ^ 2 - 2 * ‖v‖ ^ 2 + ‖v‖ ^ 2 = 0 by ring] at h
    refine h.congr fun a => ?_
    simp only [Function.comp_apply]
    rw [@norm_sub_sq 𝕜, inner_self_eq_norm_sq, inner_re_symm]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsq.sqrt

/-- **Strong operator convergence characterized by weak operator convergence.** Let $H$ be a real
or complex Hilbert space with inner product $\langle \cdot, \cdot \rangle$, let
$(T_n)_{n \in \mathbb{N}}$ be a sequence of bounded linear operators on $H$, let $T$ be a bounded
linear operator on $H$, and write $S^*$ for the adjoint of an operator $S$. Then $T_n \to T$ in
the strong operator topology, that is, $T_n x \to T x$ for every $x \in H$, if and only if both
$T_n \to T$ in the weak operator topology, that is, $\langle y, T_n x \rangle \to
\langle y, T x \rangle$ for all $x, y \in H$, and $T_n^* T_n \to T^* T$ in the weak operator
topology, that is, $\langle y, T_n^* T_n x \rangle \to \langle y, T^* T x \rangle$ for all
$x, y \in H$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; General
theory of linear operators), `benchmark/level2/ma_proofbench_l2_59.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem tendsto_apply_iff_tendsto_inner_and_tendsto_inner_adjoint_comp
    {𝕜 H : Type*}
    [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (Tn : ℕ → H →L[𝕜] H)
    (T : H →L[𝕜] H) :
    (∀ x : H, Filter.Tendsto (fun n => Tn n x) Filter.atTop (𝓝 (T x))) ↔
      (∀ x y : H, Filter.Tendsto (fun n => inner 𝕜 y (Tn n x)) Filter.atTop (𝓝 (inner 𝕜 y (T x)))) ∧
        (∀ x y : H, Filter.Tendsto (fun n => inner 𝕜 y (((Tn n).adjoint.comp (Tn n)) x))
            Filter.atTop (𝓝 (inner 𝕜 y ((T.adjoint.comp T) x)))) := by
  -- `⟪y, S† (S x)⟫ = ⟪S y, S x⟫` for every operator `S`.
  have key (S : H →L[𝕜] H) (x y : H) :
      inner 𝕜 y ((S.adjoint.comp S) x) = inner 𝕜 (S y) (S x) :=
    S.adjoint_inner_right y (S x)
  simp only [key]
  exact ⟨fun h => ⟨fun x y => tendsto_const_nhds.inner (h x), fun x y => (h y).inner (h x)⟩,
    fun h x => tendsto_of_tendsto_inner_of_tendsto_inner_self (h.1 x (T x)) (h.2 x x)⟩

end MathlibExt.Analysis.OperatorTheory.StrongOperatorConvergenceIffWeakAndAdjointWanted
