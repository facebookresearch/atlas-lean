/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_04.lean` (openbmb/ma-proofbench at commit
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

Attribution and modification notice: the statement below is taken from openbmb/ma-proofbench at
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_04.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted the
benchmark theorem `ma_proofbench_l1_04`, whose proof there is a placeholder, into the Batteries
wanted-theorem declaration `exists_eqOn_const_of_differentiableOn_conj` (a statement without a
proof); moved the informal problem statement docstring onto it and placed the declarations in
namespace `MathlibExt.Analysis.Complex.HolomorphicConjConstWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system. Further changes in this file: that wanted
declaration is now a `theorem` with a proof, its docstring is restated, and `public import
Mathlib` is replaced by narrower imports; the statement itself is unchanged.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.OpenMapping

/-!
# A holomorphic function with holomorphic conjugate is constant

Let `U ⊆ ℂ` be open and connected. If `f` and its conjugate `z ↦ conj (f z)` are both holomorphic
on `U`, then `f` is constant on `U`.

The proof uses the open mapping theorem twice. The sum `f + conj ∘ f = 2 Re f` is holomorphic on
`U` with imaginary part `0`, so it is constant there (`AnalyticOnNhd.eq_const_of_im_eq_const`).
Hence `f` is holomorphic on `U` with constant real part, so it is constant there
(`AnalyticOnNhd.eq_const_of_re_eq_const`). A proof through the Cauchy–Riemann equations would
instead combine those of `f` and of `conj ∘ f` to get `f' = 0` on `U`.

## Main results

* `exists_eqOn_const_of_differentiableOn_conj`: if `f` and `z ↦ conj (f z)` are holomorphic on
  a connected open set `U ⊆ ℂ`, then `f` is constant on `U`. This is the MA-ProofBench problem
  `ma_proofbench_l1_04`, formerly a `WantedExt` entry.

## Implementation notes

`Mathlib.Analysis.CStarAlgebra.Classes` is imported publicly so that the statement elaborates to
the same term as under `import Mathlib`, where it was first stated: the `TopologicalSpace ℂ`
instance in `IsOpen U` and `IsConnected U` is then found through `CommCStarAlgebra ℂ`.
-/

public section

open scoped ComplexConjugate

namespace MathlibExt.Analysis.Complex.HolomorphicConjConstWanted

/-- **A holomorphic function with holomorphic conjugate is constant.** Let
$U \subseteq \mathbb{C}$ be a connected open set and let $f : \mathbb{C} \to \mathbb{C}$ be
holomorphic on $U$. If the conjugate function $z \mapsto \overline{f(z)}$ is also holomorphic on
$U$, then $f$ is constant on $U$: there is $c \in \mathbb{C}$ with $f(z) = c$ for all $z \in U$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functions of a complex
variable; General properties of functions of one complex variable),
`benchmark/level1/ma_proofbench_l1_04.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem exists_eqOn_const_of_differentiableOn_conj
    {U : Set ℂ} (hUopen : IsOpen U) (hUconn : IsConnected U)
    (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f U)
    (hconj : DifferentiableOn ℂ (fun z => conj (f z)) U) :
    ∃ c : ℂ, Set.EqOn f (fun _ => c) U := by
  -- `f + conj ∘ f = 2 Re f` is holomorphic on `U` with imaginary part `0`, hence constant.
  obtain ⟨c, hc⟩ := ((hf.add hconj).analyticOnNhd hUopen).eq_const_of_im_eq_const (c₀ := 0)
    (fun z _ => by simp) hUopen hUconn
  -- So `Re f = c.re / 2` on `U`, and a holomorphic function with constant real part is constant.
  obtain ⟨d, hd⟩ := (hf.analyticOnNhd hUopen).eq_const_of_re_eq_const (c₀ := c.re / 2)
    (fun z hz => by
      have h := congrArg Complex.re (hc z hz)
      simp only [Pi.add_apply, Complex.add_re, Complex.conj_re] at h
      linarith) hUopen hUconn
  exact ⟨d, fun z hz => hd z hz⟩

end MathlibExt.Analysis.Complex.HolomorphicConjConstWanted
