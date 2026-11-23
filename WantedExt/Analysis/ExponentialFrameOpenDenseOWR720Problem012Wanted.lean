/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Frames of exponentials for open dense sets of finite measure (Oberwolfach Reports 10/2004)

Oberwolfach Mini-Workshop Wavelets and Frames (2004), H. Führ, A reproducing kernel without (?)
discretization: for an open dense `A ⊆ ℝ` of finite measure, does there exist a frame of
exponentials for `L²(A)`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.Analysis.ExponentialFrameOpenDenseOWR720Problem012Wanted

/-!
Source: H. Führ, A reproducing kernel without (?) discretization, in Mini-Workshop: Wavelets and
Frames, Oberwolfach Reports 1 (2004), no. 10, p. 532, Question, DOI 10.4171/OWR/2004/10.
UnsolvedMath record UM-30000044 (`OWR-720-012`), dataset ulamai/UnsolvedMath v1.8.0.

The source asks whether, for `H = H_A`, some `Γ ⊂ ℝ` and `η ∈ H` give a frame of `Γ`-shifts (a tight
frame even?), and notes that the problem 'can also be phrased as follows: Does there exist a frame
of exponentials for `L²(A)`?' The second phrasing is formalized: `{e^{iλt} : λ ∈ Λ}` is a frame in
`L²(A)` when `a ‖f‖² ≤ ∑_λ |∫_A f(t) e^{-iλt} dt|² ≤ b ‖f‖²` for all `f ∈ L²(A)`, with `0 < a ≤ b`
(sums in `[0, ∞]`). The parenthetical tight-frame question is not formalized.
-/

open MeasureTheory

/-- The exponentials `t ↦ e^{iλt}`, `λ ∈ Λ`, form a frame in `L²(A)`: there are `0 < a ≤ b` with
`a ‖f‖² ≤ ∑_{λ ∈ Λ} |⟨f, e_λ⟩|² ≤ b ‖f‖²` for every `f ∈ L²(A)`, where
`⟨f, e_λ⟩ = ∫_A f(t) e^{-iλt} dt` (the sum is taken in `[0, ∞]`). -/
def IsExponentialFrame (A Λ : Set ℝ) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ f : ℝ → ℂ, MemLp f 2 (volume.restrict A) →
    ENNReal.ofReal a * ∫⁻ t in A, (‖f t‖₊ : ENNReal) ^ 2 ≤
        ∑' l : Λ, (‖∫ t in A, f t * Complex.exp (-((l : ℝ) * t * Complex.I))‖₊ : ENNReal) ^ 2 ∧
      ∑' l : Λ, (‖∫ t in A, f t * Complex.exp (-((l : ℝ) * t * Complex.I))‖₊ : ENNReal) ^ 2 ≤
        ENNReal.ofReal b * ∫⁻ t in A, (‖f t‖₊ : ENNReal) ^ 2

/-- Führ's question (Oberwolfach Report 10/2004, p. 532), in its exponential-frame form: for every
open dense set `A ⊆ ℝ` of finite measure, `L²(A)` admits a frame of exponentials. -/
def openDenseExponentialFrame : Prop :=
  ∀ A : Set ℝ, IsOpen A → Dense A → volume A < ⊤ → ∃ Λ : Set ℝ, IsExponentialFrame A Λ

/--
Resolved true: Nitzan, Olevskii and Ulanovskii (Theorem 1) prove that `L²(S)` has a frame of
exponentials `{e^{iλt} : λ ∈ Λ}`, `Λ` discrete, for every set `S ⊆ ℝ` of finite measure, in
particular for every open dense `A` of finite measure. Source: H. Führ, A reproducing kernel without
(?) discretization, in Mini-Workshop: Wavelets and Frames, Oberwolfach Reports 1 (2004), no. 10, p.
532, Question, DOI 10.4171/OWR/2004/10; resolution: S. Nitzan, A. Olevskii and A. Ulanovskii,
Exponential frames on unbounded sets, Proc. Amer. Math. Soc. 144 (2016), no. 1, 109-118, DOI
10.1090/proc/12868, arXiv:1410.5693, Theorem 1: there are positive constants c, C such that for
every set S ⊂ ℝ of finite measure there is a discrete set Λ ⊂ ℝ such that {exp(iλt), λ ∈ Λ} is a
frame in L²(S) with frame bounds c|S| and C|S|, https://arxiv.org/abs/1410.5693.
-/
public theorem_wanted openDenseExponentialFrame_holds : openDenseExponentialFrame

end MathlibExt.Analysis.ExponentialFrameOpenDenseOWR720Problem012Wanted
