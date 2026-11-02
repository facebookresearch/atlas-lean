/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.ComparisonHolley

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.ComparisonHolley`

On the one-edge graph `⊤ : SimpleGraph (Fin 2)` at `p = 1/2`, `q = 2`:
* `chOpenCount` is `1` with the edge open and `0` with it closed;
* `reducedDensity (1/2) 2 = 1/3`, in `(0, 1)`, and `reducedDensity p 1 = p`;
* the headline `fk_bernoulli_sandwich` (comparison inequalities): `Bernoulli(1/3) ≼ φ_{1/2,2} ≼
  Bernoulli(1/2)`, and its consequence for the increasing event "the edge `{0, 1}` is open";
* `fk_monotone_in_p` at `1/4 ≤ 3/4`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.ComparisonHolley

open MeasureTheory _root_.StatMech _root_.StatMech.FK

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

/-- The edge set of `⊤ : SimpleGraph (Fin 2)` is the single edge `s(0, 1)`. -/
theorem edgeFinset_top_fin2 : (⊤ : SimpleGraph (Fin 2)).edgeFinset = {s(0, 1)} := by
  ext e
  induction e with
  | _ x y => fin_cases x <;> fin_cases y <;> simp

-- One open edge.
example : chOpenCount (⊤ : SimpleGraph (Fin 2)) allOpen = 1 := by
  rw [chOpenCount, edgeFinset_top_fin2]
  simp [allOpen]

-- No open edge.
example : chOpenCount (⊤ : SimpleGraph (Fin 2)) allClosed = 0 := by
  rw [chOpenCount, edgeFinset_top_fin2]
  simp [allClosed]

-- The reduced density at `p = 1/2`, `q = 2` is `1/3`.
example : reducedDensity (1 / 2) 2 = 1 / 3 := by norm_num [reducedDensity]

-- At `q = 1` the reduced density is `p`.
example (p : ℝ) (hp : 0 < p) : reducedDensity p 1 = p := by
  rw [reducedDensity]; field_simp; ring

-- The reduced density lies in `(0, 1)`.
example : 0 < reducedDensity (1 / 2) 2 ∧ reducedDensity (1 / 2) 2 < 1 :=
  reducedDensity_mem_Ioo (by norm_num) (by norm_num) (by norm_num)

-- The headline at `p = 1/2`, `q = 2`.
example : measOfMass (fkProb (⊤ : SimpleGraph (Fin 2)) (reducedDensity (1 / 2) 2) 1)
      ≼ measOfMass (fkProb (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
    ∧ measOfMass (fkProb (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
      ≼ measOfMass (fkProb (⊤ : SimpleGraph (Fin 2)) (1 / 2) 1) :=
  fk_bernoulli_sandwich _ (by norm_num) (by norm_num) (by norm_num)

-- Consequence: the edge is open with FK probability between the Bernoulli values at `1/3` and
-- `1/2`.
example : (measOfMass (fkProb (⊤ : SimpleGraph (Fin 2)) (1 / 3) 1)).real edgeOpen
      ≤ (measOfMass (fkProb (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)).real edgeOpen
    ∧ (measOfMass (fkProb (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)).real edgeOpen
      ≤ (measOfMass (fkProb (⊤ : SimpleGraph (Fin 2)) (1 / 2) 1)).real edgeOpen := by
  obtain ⟨h1, h2⟩ := fk_bernoulli_sandwich (⊤ : SimpleGraph (Fin 2)) (p := 1 / 2) (q := 2)
    (by norm_num) (by norm_num) (by norm_num)
  have hr : reducedDensity (1 / 2) 2 = 1 / 3 := by norm_num [reducedDensity]
  rw [hr] at h1
  have hm : MeasurableSet edgeOpen := (Set.toFinite _).measurableSet
  exact ⟨h1 _ hm edgeOpen_isIncreasing, h2 _ hm edgeOpen_isIncreasing⟩

-- Monotonicity in `p` at `q = 2`.
example : measOfMass (fkProb (⊤ : SimpleGraph (Fin 2)) (1 / 4) 2)
    ≼ measOfMass (fkProb (⊤ : SimpleGraph (Fin 2)) (3 / 4) 2) :=
  fk_monotone_in_p _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.ComparisonHolley
