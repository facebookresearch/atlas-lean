/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RandomWalkTailMeasurability

/-!
# Tests for tail measurability of random-walk asymptotic events

Restatements of the public signatures in
`MathlibExt.Probability.RandomWalkTailMeasurability`, plus concrete
checks on constant sequences: for `X ≡ 1` the drift-to-`+∞` event is
the whole space, for `X ≡ 0` it is empty and the finite-convergence
event is the whole space.
-/

@[expose] public section

open MeasureTheory Filter Finset Topology
open MathlibExt.Probability.RandomWalkTailMeasurability

namespace MathlibExtTest.Probability.RandomWalkTailMeasurability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The drift-to-`+∞` event is tail-measurable, with the exact public signature. -/
example (X : ℕ → Ω → ℝ) :
    @MeasurableSet _ (tailMeasurableSpaceOfFun X)
      {ω | Tendsto (fun m => randomWalkPartialSum X m ω) atTop atTop} :=
  measurableSet_driftsToTop X

/-- The drift-to-`-∞` event is tail-measurable, with the exact public signature. -/
example (X : ℕ → Ω → ℝ) :
    @MeasurableSet _ (tailMeasurableSpaceOfFun X)
      {ω | Tendsto (fun m => randomWalkPartialSum X m ω) atTop atBot} :=
  measurableSet_driftsToBot X

/-- The oscillation event is tail-measurable, with the exact public signature. -/
example (X : ℕ → Ω → ℝ) :
    @MeasurableSet _ (tailMeasurableSpaceOfFun X)
      {ω | limsup (fun m => ((randomWalkPartialSum X m ω : ℝ) : EReal)) atTop = ⊤ ∧
           liminf (fun m => ((randomWalkPartialSum X m ω : ℝ) : EReal)) atTop = ⊥} :=
  measurableSet_oscillates X

/-- The finite-convergence event is tail-measurable, with the exact public signature. -/
example (X : ℕ → Ω → ℝ) :
    @MeasurableSet _ (tailMeasurableSpaceOfFun X)
      {ω | ∃ l : ℝ, Tendsto (fun m => randomWalkPartialSum X m ω) atTop (𝓝 l)} :=
  measurableSet_convergesFinite X

/-- Each coordinate `Xᵢ` is measurable w.r.t. `σ(Xₙ, Xₙ₊₁, …)` for `n ≤ i`. -/
example (X : ℕ → Ω → ℝ) (n i : ℕ) (h : n ≤ i) :
    @Measurable _ _ (tailMeasurableSpaceFrom (sigmaAlg X) n) _ (X i) :=
  meas_Xi X n i h

/-- For the constant sequence `X ≡ 1`, the partial sums are `Sₘ = m`,
so the drift-to-`+∞` event is the whole space. -/
example :
    {ω : Ω | Tendsto (fun m => randomWalkPartialSum (fun _ _ => (1 : ℝ)) m ω)
      atTop atTop} = Set.univ := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  have hsum : (fun m => randomWalkPartialSum (fun _ _ => (1 : ℝ)) m ω) =
      fun m : ℕ => (m : ℝ) := by
    funext m
    simp [randomWalkPartialSum]
  rw [hsum, tendsto_atTop_atTop]
  intro b
  exact ⟨⌈b⌉₊, fun m hm => (Nat.le_ceil b).trans (Nat.cast_le.mpr hm)⟩

/-- For the constant sequence `X ≡ 0`, the partial sums are identically `0`,
so the drift-to-`+∞` event is empty. -/
example :
    {ω : Ω | Tendsto (fun m => randomWalkPartialSum (fun _ _ => (0 : ℝ)) m ω)
      atTop atTop} = ∅ := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro h
  have h0 : (fun m => randomWalkPartialSum (fun _ _ => (0 : ℝ)) m ω) =
      fun _ => (0 : ℝ) := by
    funext m
    simp [randomWalkPartialSum]
  rw [h0] at h
  obtain ⟨i, hi⟩ := tendsto_atTop_atTop.mp h 1
  have hm := hi i (le_refl i)
  norm_num at hm

/-- For the constant sequence `X ≡ 0`, the partial sums are identically `0`,
so the finite-convergence event is the whole space. -/
example :
    {ω : Ω | ∃ l : ℝ, Tendsto (fun m => randomWalkPartialSum (fun _ _ => (0 : ℝ)) m ω)
      atTop (𝓝 l)} = Set.univ := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  refine ⟨0, ?_⟩
  have h0 : (fun m => randomWalkPartialSum (fun _ _ => (0 : ℝ)) m ω) =
      fun _ => (0 : ℝ) := by
    funext m
    simp [randomWalkPartialSum]
  rw [h0]
  exact tendsto_const_nhds

end MathlibExtTest.Probability.RandomWalkTailMeasurability
