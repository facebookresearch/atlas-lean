/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import MathlibExt.Combinatorics.SimpleGraph.GraphLimits.Graphon
public import MathlibExt.Combinatorics.FinitelyForcibleGraphons
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.Variance

/-!
# Sidorenko's conjecture

We prove the four-cycle inequality for graphons using the second moments of degrees and codegrees.

Sidorenko's conjecture states that among all graphons of a given edge density, the constant one
minimizes the density of every bipartite graph. The finite weighted-graph case for the four-cycle
is proved in `MathlibExt.Combinatorics.SimpleGraph.GraphLimits.SidorenkoFourCycle`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.SidorenkoConjectureWanted

open MathlibExt.Combinatorics.SimpleGraph.GraphLimits
open MathlibExt.Combinatorics.FinitelyForcibleOptimumOWR4212Problem011Wanted (IsGraphon)

/-- **Sidorenko's conjecture** (open). For every bipartite simple graph `F` and every graphon `W`
(symmetric, values in `[0, 1]`), `t(F, W) ≥ t(K₂, W) ^ |E(F)|`. This is the graph form
`t(F, G) ≥ t(K₂, G) ^ |E(F)|` of Lovász, *Subgraph densities in signed graphons and the local
Sidorenko conjecture*, Electron. J. Combin. 18 (2011), §1, extended to graphons, which are limits of
graphs. Sidorenko's analytic form, inequality (1) there, is more general: it allows bounded
measurable `W ≥ 0` that need not be symmetric, and it implies the form stated here. Known cases
listed there include trees, bigraphs with a colour class of at most four nodes, and cubes. -/
def SidorenkoConjecture : Prop :=
  ∀ (k : ℕ) (F : SimpleGraph (Fin k)) [DecidableRel F.Adj], F.IsBipartite →
    ∀ W : ℝ → ℝ → ℝ, IsGraphon W →
      graphonHomDensity (⊤ : SimpleGraph (Fin 2)) W ^ F.edgeFinset.card ≤ graphonHomDensity F W

open MeasureTheory

-- The product of the weights of two edges sharing their second endpoint.
private def pairWeight {α β : Type*} (f : α × β → ℝ) (z : β × (α × α)) : ℝ :=
  f (z.2.1, z.1) * f (z.2.2, z.1)

private lemma measurable_pairWeight {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {f : α × β → ℝ} (hf : Measurable f) : Measurable (pairWeight f) := by
  unfold pairWeight
  fun_prop

private lemma norm_pairWeight_le_one {α β : Type*} {f : α × β → ℝ} (hb : ∀ z, ‖f z‖ ≤ 1)
    (z : β × (α × α)) : ‖pairWeight f z‖ ≤ 1 := by
  simpa [pairWeight, norm_mul] using
    mul_le_mul (hb (z.2.1, z.1)) (hb (z.2.2, z.1)) (norm_nonneg _) zero_le_one

-- Duplicate one side of a bipartite integral. For each fixed y the two copies
-- integrate independently, giving the square of the integral over x.
private theorem sq_integral_le_pair {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α × β → ℝ) (hf : Measurable f) (hb : ∀ z, ‖f z‖ ≤ 1) :
    (∫ z, f z ∂μ.prod ν) ^ 2 ≤
      ∫ z, pairWeight f z ∂ν.prod (μ.prod μ) := by
  let d (y : β) := ∫ x, f (x, y) ∂μ
  have hd : MemLp d 2 ν := by
    refine MemLp.of_bound hf.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable 1 ?_
    exact .of_forall fun y => by
      simpa [d] using norm_integral_le_of_norm_le_const (μ := μ) (.of_forall fun x => hb (x, y))
  have hint : Integrable f (μ.prod ν) := memLp_one_iff_integrable.mp
    (MemLp.of_bound hf.aestronglyMeasurable 1 (.of_forall hb))
  have hg : Integrable (pairWeight f) (ν.prod (μ.prod μ)) := memLp_one_iff_integrable.mp
    (MemLp.of_bound (measurable_pairWeight hf).aestronglyMeasurable 1
      (.of_forall (norm_pairWeight_le_one hb)))
  calc
    (∫ z, f z ∂μ.prod ν) ^ 2 = (∫ y, d y ∂ν) ^ 2 := by rw [integral_prod_symm _ hint]
    _ ≤ ∫ y, d y ^ 2 ∂ν := by
      have h := ProbabilityTheory.variance_nonneg d ν
      rw [ProbabilityTheory.variance_eq_sub hd] at h
      exact sub_nonneg.mp h
    _ = ∫ z, pairWeight f z ∂ν.prod (μ.prod μ) := by
      rw [integral_prod _ hg]
      refine integral_congr_ae (.of_forall fun y => ?_)
      exact (sq (d y)).trans (integral_prod_mul (fun x => f (x, y)) (fun x => f (x, y))).symm

-- Order the coordinates by the two colour classes of the four-cycle.
private theorem measurePreserving_cyclePairs (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun x : Fin 4 → ℝ => ((x 0, x 2), (x 1, x 3)))
      (Measure.pi fun _ => μ) ((μ.prod μ).prod (μ.prod μ)) := by
  have h₄ := measurePreserving_piFinSuccAbove (fun _ : Fin 4 => μ) 0
  have h₃ := measurePreserving_piFinSuccAbove (fun _ : Fin 3 => μ) 1
  have h₂ := measurePreserving_finTwoArrow μ
  have h := (MeasurePreserving.id μ).prod h₂ |>.comp h₃
  exact (measurePreserving_prodAssoc μ μ (μ.prod μ)).symm.comp
    (((MeasurePreserving.id μ).prod h).comp h₄)

/-- **Sidorenko's inequality for the four-cycle, graphon form.** For every graphon `W`,
`t(C₄, W) ≥ t(K₂, W) ^ 4` (Lovász, *Subgraph densities in signed graphons and the local Sidorenko
conjecture*, Electron. J. Combin. 18 (2011), §1: Sidorenko proved inequality (1) for bigraphs with
a colour class of at most four nodes, a class containing `C₄ = K_{2,2}`). The finite weighted-graph
case is `homDensity_cycleGraph_four_ge`. -/
theorem graphonHomDensity_cycleGraph_four_ge {W : ℝ → ℝ → ℝ} (hW : IsGraphon W) :
    graphonHomDensity (⊤ : SimpleGraph (Fin 2)) W ^ 4 ≤
      graphonHomDensity (SimpleGraph.cycleGraph 4) W := by
  let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
  have : IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Icc]⟩
  let f := Function.uncurry W
  have hf : Measurable f := hW.1
  have hb (z : ℝ × ℝ) : ‖f z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, show f z = W z.1 z.2 from rfl, abs_of_nonneg (hW.2.2 z.1 z.2).1]
    exact (hW.2.2 z.1 z.2).2
  let cycle := pairWeight (pairWeight f)
  have hedge : graphonHomDensity (⊤ : SimpleGraph (Fin 2)) W = ∫ z, f z ∂μ.prod μ := by
    unfold graphonHomDensity
    rw [volume_pi, Measure.restrict_pi_pi]
    convert (measurePreserving_finTwoArrow μ).integral_comp' f using 1
    congr 1
    funext x
    simp (config := { decide := true }) only [Fin.prod_univ_two, ↓reduceIte, mul_one, one_mul]
    rfl
  have hcycle : graphonHomDensity (SimpleGraph.cycleGraph 4) W =
      ∫ z, cycle z ∂(μ.prod μ).prod (μ.prod μ) := by
    unfold graphonHomDensity
    rw [volume_pi, Measure.restrict_pi_pi]
    let e := fun x : Fin 4 → ℝ => ((x 0, x 2), (x 1, x 3))
    have he := measurePreserving_cyclePairs μ
    calc
      _ = ∫ x, cycle (e x) ∂Measure.pi fun _ => μ := by
        congr 1
        funext x
        simp (config := { decide := true }) only [Fin.prod_univ_four, ↓reduceIte, mul_one, one_mul]
        dsimp [cycle, e, pairWeight, f, Function.uncurry]
        rw [hW.2.1 (x 1) (x 2)]
        ring
      _ = _ := by
        conv_rhs => rw [← he.map_eq]
        exact (integral_map he.measurable.aemeasurable
          (measurable_pairWeight (measurable_pairWeight hf)).aestronglyMeasurable).symm
  -- Duplicate one endpoint of the edge to get a two-edge path, then its centre to get C₄.
  rw [hedge, hcycle, show 4 = 2 * 2 by decide, pow_mul]
  exact (pow_le_pow_left₀ (sq_nonneg _) (sq_integral_le_pair μ μ f hf hb) 2).trans
    (sq_integral_le_pair μ (μ.prod μ) _ (measurable_pairWeight hf) (norm_pairWeight_le_one hb))

end MathlibExt.Combinatorics.SimpleGraph.SidorenkoConjectureWanted
