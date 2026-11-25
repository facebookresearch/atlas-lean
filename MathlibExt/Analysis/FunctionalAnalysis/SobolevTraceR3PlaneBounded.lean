/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_56.lean` (openbmb/ma-proofbench,
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029): the theorem statement, as presented
in the former wanted module. Authors: L. Pu et al. (MA-ProofBench).
Licensed under the MIT License.

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

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Sobolev trace bound on a plane

The squared trace on the plane `z = 0` has integral at most one for every member of a
sequence with Sobolev energies at most one. The proof integrates the
derivative of the square along vertical half-lines and then applies Fubini's theorem.
-/

open MeasureTheory Set

namespace MathlibExt.Analysis.FunctionalAnalysis.SobolevTraceR3PlaneBoundedWanted

private theorem trace_le_line_energy (f : ℝ × ℝ × ℝ → ℝ) (hf : ContDiff ℝ 1 f) (p : ℝ × ℝ)
    (hint : Integrable fun z : ℝ => ‖f (p.1, p.2, z)‖ ^ 2 + ‖fderiv ℝ f (p.1, p.2, z)‖ ^ 2) :
    ‖f (p.1, p.2, 0)‖ ^ 2 ≤
      ∫ z : ℝ, ‖f (p.1, p.2, z)‖ ^ 2 + ‖fderiv ℝ f (p.1, p.2, z)‖ ^ 2 := by
  let line (z : ℝ) := (p.1, p.2, z)
  let e : ℝ × ℝ × ℝ := (0, 0, 1)
  let E (z : ℝ) := ‖f (line z)‖ ^ 2 + ‖fderiv ℝ f (line z)‖ ^ 2
  let u (z : ℝ) := f (line z) ^ 2
  let du (z : ℝ) := 2 * f (line z) * fderiv ℝ f (line z) e
  have hline (z : ℝ) : HasDerivAt line e z :=
    (hasDerivAt_const z p.1).prodMk ((hasDerivAt_const z p.2).prodMk (hasDerivAt_id z))
  have hderiv (z : ℝ) : HasDerivAt u (du z) z := by
    have h := (hf.differentiable one_ne_zero (line z)).hasFDerivAt.comp_hasDerivAt z (hline z)
    simpa [u, du, Function.comp_def] using h.fun_pow 2
  have hbound (z : ℝ) : ‖du z‖ ≤ E z := by
    have he : ‖fderiv ℝ f (line z) e‖ ≤ ‖fderiv ℝ f (line z)‖ := by
      simpa [e, Prod.norm_def] using (fderiv ℝ f (line z)).le_opNorm e
    calc
      ‖du z‖ = 2 * ‖f (line z)‖ * ‖fderiv ℝ f (line z) e‖ := by simp [du, norm_mul]
      _ ≤ 2 * ‖f (line z)‖ * ‖fderiv ℝ f (line z)‖ := by gcongr
      _ ≤ E z := two_mul_le_add_sq _ _
  have hE : Integrable E := hint
  have hu : Integrable u := by
    have hc : Continuous u := continuous_iff_continuousAt.mpr fun z => (hderiv z).continuousAt
    apply hE.mono' hc.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    simp [u, E, Real.norm_eq_abs]
  have hdu : Integrable du := by
    have hd : deriv u = du := funext fun z => (hderiv z).deriv
    exact hE.mono' (hd ▸ (measurable_deriv u).aestronglyMeasurable) (ae_of_all _ hbound)
  have hlim := tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0)
    (fun z _ => hderiv z) hdu.integrableOn hu.integrableOn
  calc
    ‖f (p.1, p.2, 0)‖ ^ 2 = u 0 - 0 := by simp [u, line, Real.norm_eq_abs]
    _ = ∫ z in Iic 0, du z :=
      (integral_Iic_of_hasDerivAt_of_tendsto' (fun z _ => hderiv z) hdu.integrableOn hlim).symm
    _ ≤ ∫ z in Iic 0, E z := integral_mono hdu.integrableOn hE.integrableOn
      fun z => (le_abs_self _).trans (hbound z)
    _ ≤ ∫ z, E z := setIntegral_le_integral hE (ae_of_all _ fun z => by dsimp [E]; positivity)

/-- **Sobolev trace bound on the plane $z = 0$ in $\mathbb{R}^3$.** Let $(f_n)_{n \in \mathbb{N}}$
be a sequence of continuously differentiable functions $\mathbb{R}^3 \to \mathbb{R}$, where
$\mathbb{R}^3$ has coordinates $(x, y, z)$ and the max norm. For $p \in \mathbb{R}^3$ write
$\|Df_n(p)\|$ for the operator norm of the derivative of $f_n$ at $p$, which equals
$|\partial_x f_n(p)| + |\partial_y f_n(p)| + |\partial_z f_n(p)|$, the sum of the absolute values
of the partial derivatives. Suppose that for every $n$ the function
$p \mapsto |f_n(p)|^2 + \|Df_n(p)\|^2$ is Lebesgue integrable on $\mathbb{R}^3$ with integral at
most $1$. Then there is a constant $C \ge 0$ such that for every $n$ the function
$(x, y) \mapsto |f_n(x, y, 0)|^2$ is Lebesgue integrable on $\mathbb{R}^2$ with integral at most
$C$.

Since $\|Df_n(p)\|$ is at least the Euclidean length $|\nabla f_n(p)|$ of the gradient, the
hypothesis implies the bound $\int_{\mathbb{R}^3} (|\nabla f_n|^2 + |f_n|^2) \le 1$ of the source
problem; conversely, if $f_n$ satisfies that bound, then $f_n / \sqrt{3}$ satisfies the hypothesis.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear
function spaces and their duals), `benchmark/level2/ma_proofbench_l2_56.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem exists_bound_integral_sq_trace_of_integral_sq_add_fderiv_sq_le_one
    (f : ℕ → ℝ × ℝ × ℝ → ℝ)
    (hC1 : ∀ n : ℕ, ContDiff ℝ 1 (f n))
    (henergy : ∀ n : ℕ,
      MeasureTheory.Integrable
      (fun x : ℝ × ℝ × ℝ => ‖f n x‖ ^ 2 + ‖fderiv ℝ (f n) x‖ ^ 2) MeasureTheory.volume ∧
      (∫ x : ℝ × ℝ × ℝ,
        (‖f n x‖ ^ 2 + ‖fderiv ℝ (f n) x‖ ^ 2) ∂MeasureTheory.volume) ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ n : ℕ,
        MeasureTheory.Integrable
        (fun p : ℝ × ℝ => ‖f n (p.1, p.2, 0)‖ ^ 2) MeasureTheory.volume ∧
        (∫ p : ℝ × ℝ, ‖f n (p.1, p.2, 0)‖ ^ 2 ∂MeasureTheory.volume) ≤ C := by
  refine ⟨1, zero_le_one, fun n => ?_⟩
  let energy (x : ℝ × ℝ × ℝ) := ‖f n x‖ ^ 2 + ‖fderiv ℝ (f n) x‖ ^ 2
  let E : (ℝ × ℝ) × ℝ → ℝ := energy ∘ MeasurableEquiv.prodAssoc
  have hE : Integrable E (volume.prod volume) :=
    volume_preserving_prodAssoc.integrable_comp_of_integrable (henergy n).1
  have hbound : ∀ᵐ p : ℝ × ℝ, ‖f n (p.1, p.2, 0)‖ ^ 2 ≤ ∫ z, E (p, z) := by
    filter_upwards [hE.prod_right_ae] with p hp using trace_le_line_energy (f n) (hC1 n) p hp
  have htrace : Integrable fun p : ℝ × ℝ => ‖f n (p.1, p.2, 0)‖ ^ 2 := by
    have hc : Continuous fun p : ℝ × ℝ => ‖f n (p.1, p.2, 0)‖ ^ 2 := by
      fun_prop (disch := exact (hC1 n).continuous)
    apply hE.integral_prod_left.mono' hc.aestronglyMeasurable
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hbound
  refine ⟨htrace, (integral_mono_ae htrace hE.integral_prod_left hbound).trans ?_⟩
  calc
    ∫ p, ∫ z, E (p, z) = ∫ q, E q ∂volume.prod volume := (integral_prod E hE).symm
    _ = ∫ x, energy x := volume_preserving_prodAssoc.integral_comp' energy
    _ ≤ 1 := (henergy n).2

end MathlibExt.Analysis.FunctionalAnalysis.SobolevTraceR3PlaneBoundedWanted
