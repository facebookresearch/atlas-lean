/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Probability.CramerWold

@[expose] public section

section
open MeasureTheory ProbabilityTheory
open scoped Topology

namespace MathlibExt.Probability.CramerWoldWanted

/-!
# Cramér–Wold device

If every linear projection `⟪t, X n⟫` of a sequence of random vectors in `ℝ^d` converges in
distribution to `⟪t, Z⟫`, then `X n` converges in distribution to `Z`.
-/

/--
**Cramér–Wold device.** Let $d$ be a natural number, let $(\Omega, \mu)$ and $(\Omega', \mu')$
be probability spaces, and let $X_n : \Omega \to \mathbb{R}^d$ for $n \in \mathbb{N}$ and
$Z : \Omega' \to \mathbb{R}^d$ be maps, where $\mathbb{R}^d$ carries the Euclidean inner product.
If for every $t \in \mathbb{R}^d$ the real-valued maps $\langle t, X_n \rangle$ converge in
distribution to $\langle t, Z \rangle$ as $n \to \infty$, then $X_n$ converges in distribution
to $Z$ as $n \to \infty$.

Here convergence in distribution means that every $X_n$ and the limit are almost everywhere
measurable and their laws converge weakly as probability measures.

Proves `Wanted` entry `cramer_wold_device`.

Source: H. Cramér and H. Wold, "Some Theorems on Distribution Functions", Journal of the London
Mathematical Society s1-11 (1936), 290–294, DOI 10.1112/jlms/s1-11.4.290.
-/
theorem cramer_wold_device
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    (X : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (Z : Ω' → EuclideanSpace ℝ (Fin d))
    (h : ∀ t : EuclideanSpace ℝ (Fin d),
      TendstoInDistribution
        (fun n (ω : Ω) => @inner ℝ (EuclideanSpace ℝ (Fin d)) _ t (X n ω))
        Filter.atTop
        (fun ω' => @inner ℝ (EuclideanSpace ℝ (Fin d)) _ t (Z ω'))
        (fun _ => μ) μ') :
    TendstoInDistribution X Filter.atTop Z (fun _ => μ) μ' := by
  have hZ : AEMeasurable Z μ' := by
    have hcoord : ∀ i, AEMeasurable (fun ω' => Z ω' i) μ' := by
      intro i
      have hlim := (h (EuclideanSpace.single i 1)).aemeasurable_limit
      have heq : (fun ω' => Z ω' i)
          = (fun ω' => @inner ℝ (EuclideanSpace ℝ (Fin d)) _
              (EuclideanSpace.single i 1) (Z ω')) := by
        funext ω'
        rw [EuclideanSpace.inner_single_left]
        simp
      rw [heq]
      exact hlim
    have hpi : AEMeasurable (fun x => (Z x).ofLp) μ' :=
      (aemeasurable_pi_iff (δ := Fin d) (X := fun _ => ℝ)).mpr hcoord
    have heq : Z = (WithLp.toLp 2) ∘ (fun x => (Z x).ofLp) := rfl
    rw [heq]
    exact (WithLp.measurable_toLp 2 _).comp_aemeasurable hpi
  have hX : ∀ n, AEMeasurable (X n) μ := by
    intro n
    have hcoord : ∀ i, AEMeasurable (fun ω => (X n ω) i) μ := by
      intro i
      have hni := ((h (EuclideanSpace.single i 1)).forall_aemeasurable n)
      have heq : (fun ω => (X n ω) i)
          = (fun ω => @inner ℝ (EuclideanSpace ℝ (Fin d)) _
              (EuclideanSpace.single i 1) (X n ω)) := by
        funext ω
        rw [EuclideanSpace.inner_single_left]
        simp
      rw [heq]
      exact hni
    have hpi : AEMeasurable (fun x => ((X n x)).ofLp) μ :=
      (aemeasurable_pi_iff (δ := Fin d) (X := fun _ => ℝ)).mpr hcoord
    have heq : X n = (WithLp.toLp 2) ∘ (fun x => ((X n x)).ofLp) := rfl
    rw [heq]
    exact (WithLp.measurable_toLp 2 _).comp_aemeasurable hpi
  refine TendstoInDistribution.of_inner hZ hX fun t => ?_
  have ht := h t
  refine ht.congr
    (fun n => Filter.Eventually.of_forall (fun ω => real_inner_comm (X n ω) t))
    (Filter.Eventually.of_forall (fun ω' => real_inner_comm (Z ω') t))

end MathlibExt.Probability.CramerWoldWanted
