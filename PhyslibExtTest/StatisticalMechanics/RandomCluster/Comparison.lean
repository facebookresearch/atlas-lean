/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.Comparison

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Comparison`

On the one-edge graph `⊤ : SimpleGraph (Fin 2)`:
* `kerLap`: the constant function lies in the kernel for every configuration, and the indicator
  of vertex `0` lies in it when the edge is closed but not when it is open;
* `numClusters_eq_finrank`: the cluster count is the dimension of `kerLap`;
* `edgeFactor_cross` at `p₁ = 1/4 ≤ p₂ = 3/4`;
* the headline `fkProb_stochastically_increasing` at `p₁ = 1/4 ≤ p₂ = 3/4`, `q = 2`, applied to
  the increasing event "the edge `{0, 1}` is open";
* `fkProb_cross` at the same parameters.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Comparison

open _root_.StatMech _root_.StatMech.FK

/-- The configuration with every coordinate open. -/
def allOpen : ConfigSpace (Sym2 (Fin 2)) := fun _ => true

/-- The configuration with every coordinate closed. -/
def allClosed : ConfigSpace (Sym2 (Fin 2)) := fun _ => false

/-- The event "the edge `{0, 1}` is open". -/
def edgeOpen : Set (ConfigSpace (Sym2 (Fin 2))) := {ω | ω s(0, 1) = true}

/-- "The edge `{0, 1}` is open" is an increasing event. -/
theorem edgeOpen_isIncreasing : IsIncreasing edgeOpen := by
  intro x y hxy hx
  have h := hxy s(0, 1)
  simp only [edgeOpen, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

-- Constant functions are harmonic for every configuration.
example (ω : ConfigSpace (Sym2 (Fin 2))) :
    (fun _ => (1 : ℝ)) ∈ kerLap (⊤ : SimpleGraph (Fin 2)) ω :=
  (mem_kerLap _ ω _).mpr fun _ _ _ => rfl

-- With the edge closed, the indicator of vertex `0` lies in the kernel.
example : (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) ∈
    kerLap (⊤ : SimpleGraph (Fin 2)) allClosed := by
  rw [mem_kerLap]
  intro i j h
  simp [allClosed] at h

-- With the edge open, the indicator of vertex `0` is not in the kernel.
example : (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) ∉
    kerLap (⊤ : SimpleGraph (Fin 2)) allOpen := by
  rw [mem_kerLap]
  intro h
  have := h 0 1 (by simp [allOpen])
  simp at this

-- The number of clusters is the dimension of the kernel of the Laplacian.
example (ω : ConfigSpace (Sym2 (Fin 2))) :
    numClusters (⊤ : SimpleGraph (Fin 2)) ω = Module.finrank ℝ (kerLap ⊤ ω) :=
  numClusters_eq_finrank _ ω

-- The edge factor cross inequality at `p₁ = 1/4 ≤ p₂ = 3/4`, for the edge open under `p₁` and
-- closed under `p₂`: `p₁ (1 - p₂) ≤ (1 - p₁) p₂`.
example : (1 / 4 : ℝ) * (1 - 3 / 4) ≤ (1 - 1 / 4) * (3 / 4) := by
  have h := edgeFactor_cross (1 / 4 : ℝ) (3 / 4) (by norm_num) true false
  simpa using h

-- The headline: increasing events are more likely at the larger `p` (`1/4 ≤ 3/4`, `q = 2`).
example : (∑ ω, edgeOpen.indicator (fun _ => (1 : ℝ)) ω * fkProb ⊤ (1 / 4) 2 ω)
    ≤ ∑ ω, edgeOpen.indicator (fun _ => (1 : ℝ)) ω * fkProb ⊤ (3 / 4) 2 ω :=
  fkProb_stochastically_increasing (⊤ : SimpleGraph (Fin 2)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) edgeOpen_isIncreasing

-- The cross inequality for the normalized measures at `p₁ = 1/4`, `p₂ = 3/4`, `q = 2`.
example (a b : ConfigSpace (Sym2 (Fin 2))) :
    fkProb ⊤ (1 / 4) 2 a * fkProb ⊤ (3 / 4) 2 b
      ≤ fkProb ⊤ (1 / 4) 2 (a ⊓ b) * fkProb ⊤ (3 / 4) 2 (a ⊔ b) :=
  fkProb_cross (⊤ : SimpleGraph (Fin 2)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) a b

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Comparison
