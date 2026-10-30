/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.Analysis.Convex.Continuous

/-!
# Convex and concave functions of martingales

If `X` is a martingale and `φ : ℝ → ℝ` is convex with `E|φ(Xₙ)| < ∞` for
all `n`, then `φ ∘ X` is a submartingale. The proof is conditional Jensen's
inequality together with the martingale property `E[Xⱼ | ℱᵢ] = Xᵢ`. Two
companions follow the same proof: a convex nondecreasing `φ` sends a
submartingale to a submartingale, and a concave `φ` sends a martingale to a
supermartingale.

## Source

This formalizes the target "Claim" (Lecture 26 / Lecture 27, Martingale
observations) of `v1/Atlas/TheoryOfProbability/targets.yaml`: "If `Xₙ` is a
martingale w.r.t. `ℱₙ` and `φ` is convex with `E|φ(Xₙ)| < ∞` then `φ(Xₙ)`
is a submartingale", whose v1 formalization is
`v1/Atlas/TheoryOfProbability/code/ConvexSubmartingale.lean`
(`MeasureTheory.convex_comp_martingale_is_submartingale`). The statement is
ported unchanged (modulo namespacing/naming). The two companions are not in
v1; they are the same one-step conditional-Jensen argument.

## Main results

* `MeasureTheory.Martingale.submartingale_comp_convex`: a convex function
  of a martingale is a submartingale.
* `MeasureTheory.Submartingale.comp_convex_of_monotoneOn`: a convex
  nondecreasing function of a submartingale is a submartingale.
* `MeasureTheory.Martingale.supermartingale_comp_concave`: a concave
  function of a martingale is a supermartingale.
-/

@[expose] public section

open MeasureTheory Filter

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- A convex function of a martingale is a submartingale (Lecture 26/27):
if `X` is a martingale and `φ` is convex with `φ ∘ Xₙ` integrable for all
`n`, then `φ ∘ X` is a submartingale. -/
theorem Martingale.submartingale_comp_convex
    [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ}
    (hmart : Martingale X ℱ μ)
    {φ : ℝ → ℝ} (hφ_convex : ConvexOn ℝ Set.univ φ)
    (hφ_int : ∀ n, Integrable (fun ω => φ (X n ω)) μ) :
    Submartingale (fun n ω => φ (X n ω)) ℱ μ := by
  have hφ_cont : Continuous φ :=
    continuousOn_univ.1 (hφ_convex.continuousOn isOpen_univ)
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact hφ_cont.comp_stronglyMeasurable (hmart.stronglyMeasurable n)
  · intro i j hij
    have hJensen : (φ ∘ μ[X j | ℱ i]) ≤ᵐ[μ] μ[φ ∘ X j | ℱ i] :=
      hφ_convex.map_condExp_le_of_finiteDimensional (ℱ.le i)
        (hmart.integrable j) (hφ_int j)
    have hcondexp : μ[X j | ℱ i] =ᵐ[μ] X i := hmart.condExp_ae_eq hij
    have hcomp : (fun ω => φ (X i ω)) =ᵐ[μ] (φ ∘ μ[X j | ℱ i]) := by
      filter_upwards [hcondexp] with ω hω
      simp [Function.comp, hω]
    exact hcomp.le.trans hJensen
  · exact hφ_int

/-- A convex nondecreasing function of a submartingale is a submartingale:
if `X` is a submartingale, `φ` is convex and nondecreasing, and `φ ∘ Xₙ`
is integrable for all `n`, then `φ ∘ X` is a submartingale. Monotonicity
is needed: a convex function of a submartingale need not be a
submartingale in general (for example `φ = fun x => (x - 4) ^ 2` applied
to the submartingale with `Xᵢ = 2` and `Xⱼ = 3` a.s., where
`φ(Xᵢ) = 4 > 1 = φ(Xⱼ)`). -/
theorem Submartingale.comp_convex_of_monotoneOn
    [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ}
    (hsub : Submartingale X ℱ μ)
    {φ : ℝ → ℝ} (hφ_convex : ConvexOn ℝ Set.univ φ)
    (hφ_mono : MonotoneOn φ Set.univ)
    (hφ_int : ∀ n, Integrable (fun ω => φ (X n ω)) μ) :
    Submartingale (fun n ω => φ (X n ω)) ℱ μ := by
  have hφ_cont : Continuous φ :=
    continuousOn_univ.1 (hφ_convex.continuousOn isOpen_univ)
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact hφ_cont.comp_stronglyMeasurable (hsub.stronglyMeasurable n)
  · intro i j hij
    have hJensen : (φ ∘ μ[X j | ℱ i]) ≤ᵐ[μ] μ[φ ∘ X j | ℱ i] :=
      hφ_convex.map_condExp_le_of_finiteDimensional (ℱ.le i)
        (hsub.integrable j) (hφ_int j)
    have hsub_cond : X i ≤ᵐ[μ] μ[X j | ℱ i] := hsub.2.1 i j hij
    have hcomp : (fun ω => φ (X i ω)) ≤ᵐ[μ] (φ ∘ μ[X j | ℱ i]) := by
      filter_upwards [hsub_cond] with ω hω
      exact hφ_mono (Set.mem_univ _) (Set.mem_univ _) hω
    exact hcomp.trans hJensen
  · exact hφ_int

/-- A concave function of a martingale is a supermartingale: if `X` is a
martingale and `φ` is concave with `φ ∘ Xₙ` integrable for all `n`, then
`φ ∘ X` is a supermartingale. -/
theorem Martingale.supermartingale_comp_concave
    [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ}
    (hmart : Martingale X ℱ μ)
    {φ : ℝ → ℝ} (hφ_concave : ConcaveOn ℝ Set.univ φ)
    (hφ_int : ∀ n, Integrable (fun ω => φ (X n ω)) μ) :
    Supermartingale (fun n ω => φ (X n ω)) ℱ μ := by
  have hφ_cont : Continuous φ :=
    continuousOn_univ.1 (hφ_concave.continuousOn isOpen_univ)
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact hφ_cont.comp_stronglyMeasurable (hmart.stronglyMeasurable n)
  · intro i j hij
    have hJensen : μ[φ ∘ X j | ℱ i] ≤ᵐ[μ] (φ ∘ μ[X j | ℱ i]) :=
      hφ_concave.condExp_map_le_of_finiteDimensional (ℱ.le i)
        (hmart.integrable j) (hφ_int j)
    have hcondexp : μ[X j | ℱ i] =ᵐ[μ] X i := hmart.condExp_ae_eq hij
    have hcomp : (φ ∘ μ[X j | ℱ i]) =ᵐ[μ] (fun ω => φ (X i ω)) := by
      filter_upwards [hcondexp] with ω hω
      simp [Function.comp, hω]
    exact hJensen.trans hcomp.le
  · exact hφ_int

end MeasureTheory
