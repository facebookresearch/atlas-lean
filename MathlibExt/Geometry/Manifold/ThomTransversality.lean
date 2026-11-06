/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import Mathlib.Geometry.Manifold.Sheaf.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import MathlibExt.Geometry.Manifold.Sard

@[expose] public section

section
noncomputable section

open scoped Manifold

namespace MathlibExt.Geometry.Manifold.ThomTransversalityWanted

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  [T2Space M] [CompactSpace M] [SecondCountableTopology M]

omit [CompactSpace M] in
/-- Sard's theorem for `M`: the set of critical values has volume zero (from the repository
proof of Sard's theorem). -/
private theorem sard_critical_values_null
    (n : ℕ)
    (f : M → EuclideanSpace ℝ (Fin n))
    (hf : ContMDiff I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) f) :
    MeasureTheory.volume
      (f '' {x | ¬ Function.Surjective (mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) f x)}) = 0 := by
  have h := _root_.MathlibExt.Geometry.Manifold.SardWanted.sard_theorem f hf
  unfold _root_.MathlibExt.Geometry.Manifold.SardWanted.criticalValues
    _root_.MathlibExt.Geometry.Manifold.SardWanted.criticalSet at h
  exact h

omit [CompactSpace M] in
/-- A small regular value exists: some `c` with `‖c‖ < ε` whose fibre sees only surjective
derivatives. -/
private theorem exists_small_regular_value
    (n : ℕ)
    (f : M → EuclideanSpace ℝ (Fin n))
    (hf : ContMDiff I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : EuclideanSpace ℝ (Fin n), ‖c‖ < ε ∧
      ∀ x : M, f x = c →
        Function.Surjective (mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) f x) := by
  have hS := sard_critical_values_null n f hf
  have hball : ¬ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) ε ⊆
      f '' {x | ¬ Function.Surjective (mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) f x)} := by
    intro hsub
    have hnull := MeasureTheory.measure_mono_null hsub hS
    have hpos := Metric.measure_ball_pos MeasureTheory.volume
      (0 : EuclideanSpace ℝ (Fin n)) hε
    rw [hnull] at hpos
    exact lt_irrefl 0 hpos
  rw [Set.not_subset] at hball
  obtain ⟨c, hcball, hcS⟩ := hball
  refine ⟨c, mem_ball_zero_iff.mp hcball, ?_⟩
  intro x hx
  by_contra hns
  apply hcS
  rw [← hx]
  exact Set.mem_image_of_mem f hns

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I (⊤ : ℕ∞) M]
  [T2Space M] [CompactSpace M] [SecondCountableTopology M] in
/-- Subtracting a constant does not change the manifold derivative. -/
private theorem mfderiv_sub_const_eq
    (n : ℕ)
    (f : M → EuclideanSpace ℝ (Fin n))
    (hf : ContMDiff I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) f)
    (c : EuclideanSpace ℝ (Fin n))
    (x : M) :
    mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (fun y => f y - c) x =
      mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) f x := by
  have hdiff : MDifferentiableAt I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) f x :=
    hf.mdifferentiableAt (by simp)
  have h1 := hdiff.hasMFDerivAt
  have h2 : HasMFDerivAt I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (fun _ => c) x 0 :=
    hasMFDerivAt_const c x
  have hsub := h1.sub h2
  have heq := hsub.mfderiv
  exact heq.trans (sub_zero _)

omit [CompactSpace M] in
/-- **Approximation by maps having zero as a regular value.** Let $M$ be a Hausdorff,
second-countable smooth manifold without boundary modelled on a finite-dimensional real normed
space, let $f : M \to \mathbb{R}^n$ be $C^\infty$, and let $\varepsilon > 0$. Then there is a
$C^\infty$ map $g : M \to \mathbb{R}^n$ such that $\lVert f(x) - g(x) \rVert < \varepsilon$ for
every $x \in M$ (Euclidean norm) and $0$ is a regular value of $g$, that is, the manifold
derivative of $g$ at $x$ is surjective for every $x \in M$ with $g(x) = 0$.

No compactness is needed. -/
theorem thom_transversality_uniform_approx_regular_value_zero
    {n : ℕ}
    (f : M → EuclideanSpace ℝ (Fin n))
    (hf : ContMDiff I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : M → EuclideanSpace ℝ (Fin n)),
      ContMDiff I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) g ∧
        (∀ x : M, ‖f x - g x‖ < ε) ∧
        (∀ x : M, g x = 0 →
          Function.Surjective (mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) g x)) := by
  obtain ⟨c, hc_norm, hc_reg⟩ := exists_small_regular_value n f hf ε hε
  refine ⟨fun x => f x - c, hf.sub contMDiff_const, ?_, ?_⟩
  · intro x
    have h : f x - (f x - c) = c := sub_sub_cancel _ _
    rw [h]
    exact hc_norm
  · intro x hx
    have hfc : f x = c := sub_eq_zero.mp hx
    have hsurj := hc_reg x hfc
    have heq := mfderiv_sub_const_eq n f hf c x
    rw [heq]
    exact hsurj

/--
**Approximation by maps having zero as a regular value, compact case.** Let $M$ be a compact,
Hausdorff, second-countable smooth manifold without boundary modelled on a finite-dimensional real
normed space, let $f : M \to \mathbb{R}^n$ be $C^\infty$, and let $\varepsilon > 0$. Then there is
a $C^\infty$ map $g : M \to \mathbb{R}^n$ such that $\lVert f(x) - g(x) \rVert < \varepsilon$ for
every $x \in M$ (Euclidean norm) and $0$ is a regular value of $g$, that is, the manifold
derivative of $g$ at $x$ is surjective for every $x \in M$ with $g(x) = 0$.

Proves `Wanted` entry `thom_transversality_compact_source_uniform_approx_regular_value_zero`.

Source: R. Thom, Comment. Math. Helv. 28 (1954) 17–86
transversality; M. Hirsch, Differential Topology; Guillemin-Pollack, Differential Topology; J.
Lee, ISMs; Lean states compact-source uniform-approx regular-value-zero corollary.
-/
theorem thom_transversality_compact_source_uniform_approx_regular_value_zero
    {n : ℕ}
    (f : M → EuclideanSpace ℝ (Fin n))
    (hf : ContMDiff I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : M → EuclideanSpace ℝ (Fin n)),
      ContMDiff I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (⊤ : ℕ∞) g ∧
        (∀ x : M, ‖f x - g x‖ < ε) ∧
        (∀ x : M, g x = 0 →
          Function.Surjective (mfderiv I (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) g x)) := by
  exact thom_transversality_uniform_approx_regular_value_zero f hf ε hε

end MathlibExt.Geometry.Manifold.ThomTransversalityWanted
end
end
