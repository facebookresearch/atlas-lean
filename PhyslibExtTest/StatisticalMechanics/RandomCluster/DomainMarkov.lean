/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.DomainMarkov

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.DomainMarkov`

On the triangle `⊤ : SimpleGraph (Fin 3)` at `p = 1/2`, `q = 2`, conditioning on the edges outside
`F = {s(0, 1)}`:
* `AgreesOff`: the all-closed configuration and the one with only `{0, 1}` open agree off `F`,
  while the all-open configuration does not agree with the all-closed one off `F`;
* `condFibre` contains the boundary condition and the configuration differing on `F`, but not the
  all-open configuration;
* the headline `condFkProb_eq_inducedFkProb` (domain Markov property): the conditional measure
  equals the normalized FK weight restricted to the fibre;
* the conditional and induced measures are positive and sum to `1` over the fibre.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.DomainMarkov

open _root_.StatMech _root_.StatMech.FK

/-- The configuration with every coordinate closed. -/
def allClosed : ConfigSpace (Sym2 (Fin 3)) := fun _ => false

/-- The configuration with every coordinate open. -/
def allOpen : ConfigSpace (Sym2 (Fin 3)) := fun _ => true

/-- The configuration with only `{0, 1}` open. -/
def only01 : ConfigSpace (Sym2 (Fin 3)) := fun e => decide (e = s(0, 1))

/-- The set of conditioned edges. -/
def F : Finset (Sym2 (Fin 3)) := {s(0, 1)}

-- `only01` agrees with `allClosed` off `F`.
example : AgreesOff F allClosed only01 := by
  intro e he
  simp only [F, Finset.mem_singleton] at he
  simp [only01, allClosed, he]

-- `allOpen` does not agree with `allClosed` off `F` (it differs at `{1, 2}`).
example : ¬ AgreesOff F allClosed allOpen := by
  intro h
  have := h s(1, 2) (by simp [F])
  simp [allOpen, allClosed] at this

-- The fibre contains the boundary condition itself.
example : allClosed ∈ condFibre F allClosed := self_mem_condFibre F allClosed

-- The fibre contains `only01`, which differs from the boundary condition only on `F`.
example : only01 ∈ condFibre F allClosed := by
  rw [mem_condFibre]
  intro e he
  simp only [F, Finset.mem_singleton] at he
  simp [only01, allClosed, he]

-- The fibre does not contain the all-open configuration.
example : allOpen ∉ condFibre F allClosed := by
  rw [mem_condFibre]
  intro h
  have := h s(1, 2) (by simp [F])
  simp [allOpen, allClosed] at this

-- The headline (domain Markov property) at `p = 1/2`, `q = 2`.
example (ω : ConfigSpace (Sym2 (Fin 3))) :
    condFkProb (⊤ : SimpleGraph (Fin 3)) (1 / 2) 2 F allClosed ω
      = inducedFkProb ⊤ (1 / 2) 2 F allClosed ω :=
  condFkProb_eq_inducedFkProb _ (by norm_num) (by norm_num) (by norm_num) F allClosed ω

-- Consequence: the conditional probability of `only01` given the boundary is positive.
example : 0 < condFkProb (⊤ : SimpleGraph (Fin 3)) (1 / 2) 2 F allClosed only01 := by
  rw [condFkProb_eq_inducedFkProb _ (by norm_num) (by norm_num) (by norm_num)]
  exact inducedFkProb_pos _ (by norm_num) (by norm_num) (by norm_num) F allClosed only01

-- The conditional measure is normalized on the fibre.
example : ∑ ω ∈ condFibre F allClosed,
    condFkProb (⊤ : SimpleGraph (Fin 3)) (1 / 2) 2 F allClosed ω = 1 :=
  condFkProb_sum_eq_one _ (by norm_num) (by norm_num) (by norm_num) F allClosed

-- The induced measure is normalized on the fibre.
example : ∑ ω ∈ condFibre F allClosed,
    inducedFkProb (⊤ : SimpleGraph (Fin 3)) (1 / 2) 2 F allClosed ω = 1 :=
  inducedFkProb_sum_eq_one _ (by norm_num) (by norm_num) (by norm_num) F allClosed

end PhyslibExtTest.StatisticalMechanics.RandomCluster.DomainMarkov
