/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# An injective entire function is affine

The following OpenBMB notice applies to the adapted statement and its documentation.

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_37.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l1_37 … := by sorry` into the Batteries `theorem_wanted`
`exists_affine_of_differentiable_injective`; moved the informal problem statement docstring onto
it and placed the declarations in namespace
`MathlibExt.Analysis.Complex.InjectiveEntireIsAffineWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.OpenMapping
import MathlibExt.Analysis.Complex.CasoratiWeierstrass

/-! # Injective entire functions

The open mapping theorem and injectivity give an open set missed by `z ↦ f z⁻¹` on a punctured
ball, so Casorati–Weierstrass gives meromorphy at zero. The resulting polynomial growth allows
Liouville's theorem to express `f` as a polynomial. An injective polynomial has degree at most
one: at a point where its derivative is nonzero, the corresponding fiber has one simple root.
-/

@[expose] public section

namespace MathlibExt.Analysis.Complex.InjectiveEntireIsAffineWanted

open Filter Set Metric Bornology Asymptotics Polynomial Topology

private theorem meromorphic_inv_of_injective (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hi : Function.Injective f) : MeromorphicAt (fun w : ℂ => f w⁻¹) 0 := by
  have ha : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  have hopen : IsOpenMap f := ha.is_constant_or_isOpenMap.resolve_left (by
    rintro ⟨c, hc⟩
    exact zero_ne_one (hi ((hc 0).trans (hc 1).symm)))
  have hd : DifferentiableOn ℂ (fun w : ℂ => f w⁻¹) (ball (0 : ℂ) 1 \ {0}) := by
    intro w hw
    have hw0 : w ≠ 0 := by simpa only [mem_singleton_iff] using hw.2
    have hinv : DifferentiableAt ℂ (fun x : ℂ => x⁻¹) w := differentiableAt_id.inv hw0
    exact ((hf w⁻¹).comp w hinv).differentiableWithinAt
  by_contra hm
  have hdense := MathlibExt.Analysis.Complex.CasoratiWeierstrass.casoratiWeierstrass
    (show (0 : ℝ) < 1 from zero_lt_one) hd hm
  have hnonempty : (f '' ball (0 : ℂ) 1).Nonempty :=
    ⟨f 0, 0, mem_ball_self zero_lt_one, rfl⟩
  obtain ⟨v, hv, hv'⟩ := hdense.inter_open_nonempty _ (hopen _ isOpen_ball) hnonempty
  obtain ⟨x, hx, hfx⟩ := hv
  obtain ⟨w, hw, hfw⟩ := hv'
  have hxw : x = w⁻¹ := hi (hfx.trans hfw.symm)
  have hw0 : w ≠ 0 := by simpa only [mem_singleton_iff] using hw.2
  have hwlt : ‖w‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hw.1
  have hinvlt : ‖w⁻¹‖ < 1 := by simpa only [hxw, mem_ball, dist_zero_right] using hx
  rw [norm_inv, inv_eq_one_div] at hinvlt
  have hwgt : 1 < ‖w‖ := by
    have hmul := (div_lt_iff₀ (norm_pos_iff.mpr hw0)).mp hinvlt
    simpa only [one_mul] using hmul
  exact (not_lt_of_ge hwgt.le) hwlt

private theorem bigO_pow_of_meromorphic_inv {f : ℂ → ℂ}
    (hm : MeromorphicAt (fun w : ℂ => f w⁻¹) 0) :
    ∃ n : ℕ, f =O[cobounded ℂ] (fun z : ℂ => z ^ n) := by
  obtain ⟨n, hn⟩ := hm
  let g (w : ℂ) := (w - 0) ^ n • f w⁻¹
  have hg : ContinuousAt g 0 := hn.continuousAt
  let K : ℝ := ‖g 0‖ + 1
  have hnear : ∀ᶠ w in 𝓝 (0 : ℂ), ‖g w‖ < K :=
    hg.norm.tendsto.eventually_lt_const (lt_add_of_pos_right _ zero_lt_one)
  have hinv : Tendsto (fun z : ℂ => z⁻¹) (cobounded ℂ) (𝓝 0) := tendsto_inv₀_cobounded
  have hnonzero : ∀ᶠ z : ℂ in cobounded ℂ, z ≠ 0 := by
    filter_upwards [(tendsto_norm_cobounded_atTop (E := ℂ)).eventually_gt_atTop 0] with z hz
    exact norm_pos_iff.mp hz
  refine ⟨n, IsBigO.of_bound K ?_⟩
  filter_upwards [hinv.eventually hnear, hnonzero] with z hb hz
  change ‖(z⁻¹ - 0) ^ n • f ((z⁻¹)⁻¹)‖ < K at hb
  rw [sub_zero, inv_inv, smul_eq_mul, norm_mul, inv_pow, norm_inv] at hb
  have hp : 0 < ‖z ^ n‖ := norm_pos_iff.mpr (pow_ne_zero _ hz)
  calc
    ‖f z‖ = ‖z ^ n‖ * (‖z ^ n‖⁻¹ * ‖f z‖) := by
      rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
    _ ≤ ‖z ^ n‖ * K := mul_le_mul_of_nonneg_left hb.le hp.le
    _ = K * ‖z ^ n‖ := mul_comm _ _

private theorem natDegree_le_one_of_injective_eval (p : ℂ[X])
    (hi : Function.Injective p.eval) : p.natDegree ≤ 1 := by
  by_contra! hlarge
  have hder_ne : p.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr (by omega)
  obtain ⟨a, ha⟩ : ∃ a : ℂ, p.derivative.eval a ≠ 0 := by
    by_contra! h
    apply hder_ne
    apply Polynomial.funext
    intro x
    rw [eval_zero]
    exact h x
  let q := p - C (p.eval a)
  have hqdeg : q.natDegree = p.natDegree := Polynomial.natDegree_sub_C
  have hqex : q.natDegree - 1 ≠ 0 := by omega
  have hcard : q.roots.card = q.natDegree := (IsAlgClosed.splits q).natDegree_eq_card_roots.symm
  have hr : q.roots = Multiset.replicate q.natDegree a := by
    refine Multiset.eq_replicate.mpr ⟨hcard, fun b hb => hi ?_⟩
    exact (Polynomial.mem_roots_sub_C'.mp hb).2
  have hrepr : q = C q.leadingCoeff * (X - C a) ^ q.natDegree := by
    simpa only [hr, Multiset.map_replicate, Multiset.prod_replicate] using
      (Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard).symm
  have heval := congrArg (fun r : ℂ[X] => r.derivative.eval a) hrepr
  apply ha
  calc
    p.derivative.eval a = q.derivative.eval a := by simp [q]
    _ = 0 := by
      rw [heval]
      simp [Polynomial.derivative_mul, Polynomial.derivative_pow, hqex]
/-- **Injective entire functions are affine.** If $f : \mathbb{C} \to \mathbb{C}$ is entire and
injective, then there are $a, b \in \mathbb{C}$ with $a \ne 0$ such that $f(z) = az + b$ for all
$z \in \mathbb{C}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functions of a complex
variable; Geometric function theory), `benchmark/level1/ma_proofbench_l1_37.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem exists_affine_of_differentiable_injective
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hinj : Function.Injective f) :
    ∃ a b : ℂ, a ≠ 0 ∧ ∀ z : ℂ, f z = a * z + b := by
  obtain ⟨n, hn⟩ := bigO_pow_of_meromorphic_inv (meromorphic_inv_of_injective f hf hinj)
  obtain ⟨p, _, hp⟩ := hf.exists_eq_polynomial_eval_of_isBigO_pow hn
  rw [hp] at hinj ⊢
  have hform := Polynomial.eq_X_add_C_of_natDegree_le_one
    (natDegree_le_one_of_injective_eval p hinj)
  have hcoef : p.coeff 1 ≠ 0 := by
    intro hz
    have hconst : p = C (p.coeff 0) := hform.trans (by simp [hz])
    exact zero_ne_one (hinj (show p.eval 0 = p.eval 1 by rw [hconst, eval_C, eval_C]))
  refine ⟨p.coeff 1, p.coeff 0, hcoef, fun z => ?_⟩
  simpa only [eval_add, eval_mul, eval_X, eval_C] using
    congrArg (Polynomial.eval z) hform

end MathlibExt.Analysis.Complex.InjectiveEntireIsAffineWanted
