/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
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

Attribution and modification notice: the statement is adapted from openbmb/ma-proofbench at commit
31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_61.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; also distributed in the Hugging Face dataset
openbmb/MA-ProofBench), under the MIT license above. The ATLAS import converted the statement to
`theorem_wanted`, named and documented it in the namespace below, and used a public module import.
This file preserves the statement and audited docstring, supplies a proof, and narrows the imports.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.Complex.GreatPicard

/-!
# Entire solutions of the Fermat cubic

Dividing by the nowhere-zero sum of the two functions yields an entire function omitting
both roots of a quadratic. Great Picard at infinity and Liouville force this quotient to be
constant. The cubic identity then bounds the original functions.
-/

open Set Bornology
open MathlibExt.Analysis.Complex.GreatPicardWanted

noncomputable section

namespace MathlibExt.Analysis.Complex.EntireFermatCubicConstantWanted

private theorem exists_two_quadratic_roots :
    ∃ a b : ℂ, a ≠ b ∧ a ^ 3 + (1 - a) ^ 3 = 0 ∧ b ^ 3 + (1 - b) ^ 3 = 0 := by
  let k : ℂ := Complex.I / (Real.sqrt 3 : ℝ)
  have hk : k ^ 2 = -(1 / 3 : ℂ) := by
    dsimp only [k]
    rw [div_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))]
    norm_num
  have hk0 : k ≠ 0 := by
    intro h
    norm_num [h] at hk
  let a : ℂ := (1 + k) / 2
  let b : ℂ := (1 - k) / 2
  refine ⟨a, b, ?_, ?_, ?_⟩
  · intro h
    apply hk0
    dsimp only [a, b] at h
    linear_combination h
  · calc
      _ = (1 + 3 * k ^ 2) / 4 := by dsimp only [a]; ring
      _ = 0 := by rw [hk]; norm_num
  · calc
      _ = (1 + 3 * k ^ 2) / 4 := by dsimp only [b]; ring
      _ = 0 := by rw [hk]; norm_num

/-- **Entire solutions of the Fermat cubic are constant.** Let $f$ and $g$ be entire functions
with $f(z)^3 + g(z)^3 = 1$ for every $z \in \mathbb{C}$. Then $f$ and $g$ are constant.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functions of a complex
variable; Entire and meromorphic functions of one complex variable, and related topics),
`benchmark/level2/ma_proofbench_l2_61.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem entire_cube_add_cube_eq_one_const
    (f g : ℂ → ℂ)
    (hf_entire : Differentiable ℂ f)
    (hg_entire : Differentiable ℂ g)
    (hfg : ∀ z : ℂ, f z ^ (3 : ℕ) + g z ^ (3 : ℕ) = 1) :
    ∃ a b : ℂ, (∀ z : ℂ, f z = a) ∧ (∀ z : ℂ, g z = b) := by
  let u (z : ℂ) := f z + g z
  have hU : Differentiable ℂ u := hf_entire.add hg_entire
  have hu (z : ℂ) : u z ≠ 0 := by
    intro h
    change f z + g z = 0 at h
    have hg_entire' : g z = -f z := by linear_combination h
    have hc : f z ^ 3 + g z ^ 3 = 0 := by rw [hg_entire']; ring
    exact zero_ne_one (hc.symm.trans (hfg z))
  let h (z : ℂ) := f z / u z
  have hd : Differentiable ℂ h := hf_entire.div hU hu
  have hf_entire' (z : ℂ) : f z = h z * u z := (div_mul_cancel₀ _ (hu z)).symm
  have hg_entire' (z : ℂ) : g z = (1 - h z) * u z := by
    rw [sub_mul, one_mul, ← hf_entire' z]
    dsimp only [u]
    ring
  have hC (z : ℂ) : (h z ^ 3 + (1 - h z) ^ 3) * u z ^ 3 = 1 := calc
    _ = (h z * u z) ^ 3 + ((1 - h z) * u z) ^ 3 := by ring
    _ = 1 := by rw [← hf_entire' z, ← hg_entire' z]; exact hfg z
  obtain ⟨a, b, hab, ha, hb⟩ := exists_two_quadratic_roots
  have hom (c : ℂ) (hc : c ^ 3 + (1 - c) ^ 3 = 0) (z : ℂ) : h z ≠ c := by
    intro hzc
    have Hz := hC z
    rw [hzc, hc, zero_mul] at Hz
    exact zero_ne_one Hz
  have hconst : ∃ c : ℂ, ∀ z, h z = c := by
    by_contra hnc
    exact hab (littlePicard hd hnc (hom a ha) (hom b hb))
  obtain ⟨c, hc⟩ := hconst
  have hnonzero : c ^ 3 + (1 - c) ^ 3 ≠ 0 := by
    intro heq
    have Hz := hC 0
    rw [hc 0, heq, zero_mul] at Hz
    exact zero_ne_one Hz
  have heq (z : ℂ) : u z ^ 3 = u 0 ^ 3 := by
    apply mul_left_cancel₀ hnonzero
    simpa only [hc z, hc 0] using (hC z).trans (hC 0).symm
  have hbounded : IsBounded (Set.range u) := by
    refine isBounded_iff_forall_norm_le.mpr ⟨‖u 0‖, ?_⟩
    rintro _ ⟨z, rfl⟩
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by decide : (3 : ℕ) ≠ 0)).mp
    simpa only [norm_pow] using le_of_eq (congrArg norm (heq z))
  obtain ⟨u₀, hu₀⟩ := hU.exists_const_forall_eq_of_bounded hbounded
  exact ⟨c * u₀, (1 - c) * u₀, fun z => by rw [hf_entire' z, hc z, hu₀ z],
    fun z => by rw [hg_entire' z, hc z, hu₀ z]⟩

end MathlibExt.Analysis.Complex.EntireFermatCubicConstantWanted
