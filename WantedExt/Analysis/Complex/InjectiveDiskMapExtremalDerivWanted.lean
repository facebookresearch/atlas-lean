/-
# An injective holomorphic Omega->D map fixing 0 maximizes |f'(0)|

Copyright (c) 2026 OpenBMB

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_22.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_22 … := by sorry` into the Batteries `theorem_wanted`
`exists_mem_admissibleFamily_norm_deriv_eq_sSup`; moved the informal problem statement docstring
onto it and placed the declarations in namespace
`MathlibExt.Analysis.Complex.InjectiveDiskMapExtremalDerivWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system; added docstrings to helper definitions.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Complex.InjectiveDiskMapExtremalDerivWanted

/-- **Open unit disc.** The open unit disc is the set of complex numbers $z$ with $|z| < 1$, the
open ball of radius $1$ about $0$ in $\mathbb{C}$. -/
abbrev unitDisk : Set ℂ := Metric.ball (0 : ℂ) 1

/-- **Admissible maps into the unit disc.** For a set $\Omega \subseteq \mathbb{C}$, the
admissible family of $\Omega$ is the set of functions $f : \mathbb{C} \to \mathbb{C}$ that are
complex differentiable on $\Omega$, injective on $\Omega$, satisfy $f(0) = 0$, and map $\Omega$
into the open unit disc $\{z \in \mathbb{C} : |z| < 1\}$. -/
def AdmissibleFamily (Ω : Set ℂ) : Set (ℂ → ℂ) :=
  {f | DifferentiableOn ℂ f Ω ∧ Set.InjOn f Ω ∧ f 0 = 0 ∧ Set.MapsTo f Ω unitDisk}

/-- **Existence of an extremal injective map into the unit disc.** Let $D$ be the open unit disc
$\{z \in \mathbb{C} : |z| < 1\}$, let $\Omega \subseteq D$ be open and connected with
$0 \in \Omega$, and let $F$ be the family of functions $f$ that are holomorphic and injective on
$\Omega$, map $\Omega$ into $D$, and satisfy $f(0) = 0$. Then some $g \in F$ attains the supremum
of $|f'(0)|$ over $F$:

$$|g'(0)| = \sup_{f \in F} |f'(0)|.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functions of a complex
variable; Geometric function theory), `benchmark/level2/ma_proofbench_l2_22.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_mem_admissibleFamily_norm_deriv_eq_sSup
  (Ω : Set ℂ)
  (hΩ_open : IsOpen Ω)
  (hΩ_connected : IsConnected Ω)
  (h0 : (0 : ℂ) ∈ Ω)
  (hΩ_subset : Ω ⊆ unitDisk) :
  ∃ g ∈ AdmissibleFamily Ω,
    ‖deriv g 0‖ = sSup ((fun f : ℂ → ℂ => ‖deriv f 0‖) '' AdmissibleFamily Ω)

end MathlibExt.Analysis.Complex.InjectiveDiskMapExtremalDerivWanted
