/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.PeierlsSquareLattice
public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.BoxMagnetization
public import PhyslibExt.StatisticalMechanics.RandomCluster.PcLtOnePeierls
public import PhyslibExt.StatisticalMechanics.RandomCluster.ThetaZeroBelowPc

/-!
# Spontaneous magnetization of the two-dimensional Ising model

Peierls' theorem: the two-dimensional Ising model has positive spontaneous magnetization at low
temperature.

## i. Overview

For large `β` the Peierls contour bound shows that, uniformly in `n`, the probability that the
origin carries a minus spin under the plus-boundary measure on `Λ_n` is at most `c(β) < 1/2`, so
`⟨σ_0⟩⁺_n ≥ 1 - 2c(β) > 0`. The spontaneous magnetization is a subsequential limit of these
finite-volume magnetizations, hence also positive. This is the input used to show that the FK
critical point `p_c(2, 2)` is less than one.

## ii. Key results

- `pup_exists_uniform_fvMagnetization` : a uniform positive lower bound on `⟨σ_0⟩⁺_n` for some
  `β > 0`.
- `pup_exists_positive_magnetization` : Peierls' theorem, `m*(β) > 0` for some `β > 0` in
  `d = 2`.

## iii. Table of contents

- A. Uniform lower bound in finite volume
- B. Positive spontaneous magnetization

## iv. References

- R. Peierls, *On Ising's model of ferromagnetism*, Proc. Cambridge Philos. Soc. 32 (1936)
  477–481.
- R. B. Griffiths, *Peierls proof of spontaneous magnetization in a two-dimensional Ising
  ferromagnet*, Phys. Rev. 136 (1964) A437–A439.
- S. Friedli and Y. Velenik, *Statistical Mechanics of Lattice Systems*, Cambridge University
  Press (2017), Section 3.7.2.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace StatMech
namespace IsingFK

open StatMech.Ising StatMech.FK

/-! ## A. Uniform lower bound in finite volume -/

lemma pup_fvMagnetization_eq_fvMagOrigin (n : ℕ) (β : ℝ) :
    fvMagnetization 2 β n =
      fvMagOrigin (plusField 2) n (bondFinsetTouch 2 n) β 0 := by
  rw [fvMagnetization, fvMagOrigin_plus_eq_integral]
  rfl

lemma pup_exists_uniform_fvMagnetization :
    ∃ β > 0, ∃ c > 0, ∀ n, c ≤ fvMagnetization 2 β n := by
  obtain ⟨β₂, hβ₂⟩ := pcl_exists_beta_ratio_lt_one 2
  obtain ⟨β₃, hβ₃⟩ := poc_exists_beta_two_peierlsBound_lt_half 2
  let β := max (max β₂ β₃) 1
  have hβpos : 0 < β := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hβ₂le : β₂ ≤ β := le_trans (le_max_left _ _) (le_max_left _ _)
  have hβ₃le : β₃ ≤ β := le_trans (le_max_right _ _) (le_max_left _ _)
  have hratio : peierlsRatio 2 β < 1 := hβ₂ β hβ₂le
  have hboundlt : twoPeierlsBound 2 β < 1 / 2 := hβ₃ β hβ₃le
  let c := 1 - 2 * twoPeierlsBound 2 β
  have hcpos : 0 < c := by dsimp [c]; linarith
  refine ⟨β, hβpos, c, hcpos, fun n => ?_⟩
  have hprob : probOriginMinus (plusField 2) n (bondFinsetTouch 2 n) β 0 ≤
      twoPeierlsBound 2 β :=
    outerProbOriginMinus_le_two_peierls n β hratio
      (spinCompatibleFill_outerContourWinding n)
  rw [pup_fvMagnetization_eq_fvMagOrigin,
    fvMagOrigin_eq_one_sub_two_mul_probOriginMinus]
  dsimp [c]
  linarith

/-! ## B. Positive spontaneous magnetization -/

/-- **Peierls' theorem.** The two-dimensional Ising model has positive spontaneous magnetization at
some inverse temperature (Peierls, *On Ising's model of ferromagnetism*, 1936; Griffiths, Phys.
Rev. 136 (1964)). -/
theorem pup_exists_positive_magnetization :
    ∃ β > 0, 0 < magnetization 2 β := by
  obtain ⟨β, hβ, c, hc, hfinite⟩ := pup_exists_uniform_fvMagnetization
  obtain ⟨φ, _hφ, hlim⟩ := magnetization_eq_limit 2 β
  have hclim : c ≤ magnetization 2 β :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall (fun n => hfinite (φ n)))
  exact ⟨β, hβ, lt_of_lt_of_le hc hclim⟩

end IsingFK
end StatMech
