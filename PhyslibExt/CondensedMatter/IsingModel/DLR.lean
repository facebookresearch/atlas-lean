/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Configuration.CondDistribution
public import PhyslibExt.CondensedMatter.IsingModel.InfiniteVolume

/-!
# DLR states of the Ising model on ℤ^d

The Dobrushin–Lanford–Ruelle (DLR) condition for infinite-volume Ising states on the hypercubic
lattice.

## i. Overview

A probability measure `μ` on spin configurations of `ℤ^d` is a DLR state at inverse temperature `β`
and field `h` if, for every box `Λ_n = [-n, n]^d`, the conditional distribution of `μ` given the
spins outside `Λ_n` is, for `μ`-almost every boundary condition `η`, the finite-volume Gibbs measure
in `Λ_n` with boundary condition `η` (all bonds touching `Λ_n` included).

## ii. Key results

- `StatMech.Ising.IsDLRState` : the DLR condition on boxes

## iii. Table of contents

- A. The DLR condition

## iv. References

- H.-O. Georgii, *Gibbs Measures and Phase Transitions*, de Gruyter (1988; 2nd ed. 2011), Chapter 2
- S. Friedli and Y. Velenik, *Statistical Mechanics of Lattice Systems: A Concrete Mathematical
  Introduction*, Cambridge University Press (2017), Chapter 6
- R. L. Dobrushin, *The description of a random field by means of conditional probabilities and
  conditions of its regularity*, Theory Probab. Appl. 13 (1968) 197–224
- O. E. Lanford and D. Ruelle, *Observables at infinity and states with short range correlations in
  statistical mechanics*, Comm. Math. Phys. 13 (1969) 194–215
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}

/-! ## A. The DLR condition -/

/-- The DLR condition: for every `n`, the conditional distribution of `μ` given the spins outside
the box `Λ_n` equals, for `μ`-almost every `η`, the finite-volume Gibbs measure `fvMeasure η n
(bondFinsetTouch d n) β h` with boundary condition `η`. -/
def IsDLRState (d : ℕ) (β h : ℝ) (μ : Measure (ConfigSpace (Site d)))
    [IsFiniteMeasure μ] : Prop :=
  ∀ n : ℕ, ∀ᵐ η ∂μ,
    (gibbsConditional μ (box d n)) η = fvMeasure η n (bondFinsetTouch d n) β h

end Ising

end StatMech
