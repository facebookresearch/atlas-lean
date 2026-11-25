/-
# The graph of a measurable function on R^d is a Lebesgue null set

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_38.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. The statement was imported as
`MathlibExt.MeasureTheory.GraphMeasurableNullWanted.measurableSet_and_volume_eq_zero_graph` with
a source docstring. It keeps that name and statement here, with a proof and narrower imports.
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

/-! # Nullity of the graph of a measurable real function -/

@[expose] public section

open MeasureTheory Set

namespace MathlibExt.MeasureTheory.GraphMeasurableNullWanted

/-- **The graph of a measurable function is a null set.** Let $d \ge 0$ be an integer and let
$f : \mathbb{R}^d \to \mathbb{R}$ be Borel measurable. Identify $\mathbb{R}^d \times \mathbb{R}$
with $\mathbb{R}^{d+1}$ by taking the last coordinate as $y$. Then the graph
$\Gamma = \{(x, y) \in \mathbb{R}^d \times \mathbb{R} : y = f(x)\}$ is a Borel measurable subset
of $\mathbb{R}^{d+1}$ and has Lebesgue measure $0$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Measure and integration;
Classical measure theory), `benchmark/level1/ma_proofbench_l1_38.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem measurableSet_and_volume_eq_zero_graph
    {d : ℕ} (f : (Fin d → ℝ) → ℝ) (Γ : Set (Fin (d + 1) → ℝ))
    (hΓ : Γ = {z : Fin (d + 1) → ℝ | z (Fin.last d) = f (fun i : Fin d => z (Fin.castSucc i))})
    (hf : Measurable f) : MeasurableSet Γ ∧ volume Γ = 0 := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) (Fin.last d)
  let T : Set (ℝ × (Fin d → ℝ)) := {p | p.1 = f p.2}
  have hT : MeasurableSet T := measurableSet_eq_fun measurable_fst (hf.comp measurable_snd)
  have hpre : Γ = e ⁻¹' T := by
    rw [hΓ]
    ext z
    change (z (Fin.last d) = f (fun i => z (Fin.castSucc i))) ↔
      z (Fin.last d) = f (fun i => z ((Fin.last d).succAbove i))
    simp only [Fin.succAbove_last_apply]
  rw [hpre]
  refine ⟨e.measurable hT, ?_⟩
  have he : MeasurePreserving e :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) (Fin.last d)
  rw [he.measure_preimage hT.nullMeasurableSet]
  change ((volume : Measure ℝ).prod volume) T = 0
  rw [Measure.prod_apply_symm hT]
  have hsection (x : Fin d → ℝ) : (fun y : ℝ => (y, x)) ⁻¹' T = {f x} := rfl
  simp only [hsection, measure_singleton, lintegral_zero]

end MathlibExt.MeasureTheory.GraphMeasurableNullWanted
