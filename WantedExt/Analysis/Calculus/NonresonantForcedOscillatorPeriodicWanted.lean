/-
# Nonresonant forced oscillator: unique periodic solution, all bounded

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_39.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_39 … := by sorry` into the Batteries `theorem_wanted`
`existsUnique_periodic_solution_and_isBounded_of_ne_natCast`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Calculus.NonresonantForcedOscillatorPeriodicWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.Calculus.NonresonantForcedOscillatorPeriodicWanted

/-- **Nonresonant forced oscillator.** Let $\omega > 0$ be a real number that is not an integer,
and let $g : \mathbb{R} \to \mathbb{R}$ be continuous and $2\pi$-periodic. Then the equation
$u'' + \omega^2 u = g$ has exactly one twice continuously differentiable solution
$u : \mathbb{R} \to \mathbb{R}$ that is $2\pi$-periodic, and every twice continuously
differentiable solution $u : \mathbb{R} \to \mathbb{R}$ of this equation is bounded.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; Ordinary
differential operators), `benchmark/level2/ma_proofbench_l2_39.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted existsUnique_periodic_solution_and_isBounded_of_ne_natCast
  (ω : ℝ) (hωpos : 0 < ω) (hω_nonint : ∀ n : ℕ, ω ≠ n)
  (g : ℝ → ℝ) (hg_cont : Continuous g)
  (hper : Function.Periodic g (2 * Real.pi)) :
  (∃! u : ℝ → ℝ, ContDiff ℝ 2 u ∧
  (∀ x : ℝ, deriv (deriv u) x + ω ^ 2 * u x = g x) ∧
  Function.Periodic u (2 * Real.pi)) ∧
  (∀ u : ℝ → ℝ, ContDiff ℝ 2 u →
  (∀ x : ℝ, deriv (deriv u) x + ω ^ 2 * u x = g x) →
  Bornology.IsBounded (Set.range u))

end MathlibExt.Analysis.Calculus.NonresonantForcedOscillatorPeriodicWanted
