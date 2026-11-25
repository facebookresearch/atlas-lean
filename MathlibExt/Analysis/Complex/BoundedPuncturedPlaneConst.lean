/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_84.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029): the theorem statement and its description.
Authors: L. Pu et al. (MA-ProofBench)
MIT License

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
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Bounded holomorphic functions on the punctured plane

A bounded holomorphic function on the punctured plane is constant there. Composing with the
complex exponential gives a bounded entire function to which Liouville's theorem applies.
-/

namespace MathlibExt.Analysis.Complex.BoundedPuncturedPlaneConstWanted

/-- **Bounded holomorphic functions on the punctured plane are constant.** Let
$f : \mathbb{C} \to \mathbb{C}$ be holomorphic on $\mathbb{C} \setminus \{0\}$, and suppose that
there is a real number $C$ with $|f(z)| \le C$ for every $z \ne 0$. Then there is a constant
$c \in \mathbb{C}$ with $f(z) = c$ for every $z \ne 0$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functions of a complex
variable; Entire and meromorphic functions of one complex variable, and related topics),
`benchmark/level1/ma_proofbench_l1_84.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem eqOn_const_of_differentiableOn_compl_zero_of_bounded
    (f : ℂ → ℂ) (hHol : DifferentiableOn ℂ f ({0}ᶜ))
    (hBdd : ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖f z‖ ≤ C) :
    ∃ c : ℂ, Set.EqOn f (fun _ => c) ({0}ᶜ) := by
  obtain ⟨C, hC⟩ := hBdd
  have hEntire : Differentiable ℂ (f ∘ Complex.exp) :=
    differentiableOn_univ.mp (hHol.comp Complex.differentiable_exp.differentiableOn
      (fun z _ => Complex.exp_ne_zero z))
  have hBound : Bornology.IsBounded (Set.range (f ∘ Complex.exp)) := by
    refine isBounded_iff_forall_norm_le.mpr ⟨C, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact hC _ (Complex.exp_ne_zero z)
  obtain ⟨c, hc⟩ := hEntire.exists_const_forall_eq_of_bounded hBound
  refine ⟨c, fun z hz => ?_⟩
  simpa only [Function.comp_apply, Complex.exp_log hz] using hc (Complex.log z)

end MathlibExt.Analysis.Complex.BoundedPuncturedPlaneConstWanted
