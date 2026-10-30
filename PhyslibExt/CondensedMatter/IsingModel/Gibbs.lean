/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Configuration.ConfigSpace

/-!
# The finite-volume Ising Gibbs measure

Spins, the Ising Hamiltonian, and the Gibbs distribution of the ferromagnetic Ising model on a
finite graph.

## i. Overview

A configuration `s : ConfigSpace V` assigns `true` (spin `+1`) or `false` (spin `-1`) to every
vertex. On a finite simple graph `G` with uniform coupling `1` and external field `h`, the
Hamiltonian is `H(s) = -∑_{xy ∈ E(G)} σ_x σ_y - h ∑_x σ_x`, summed over unordered edges. At inverse
temperature `β` the Gibbs weight of `s` is `exp (-β H(s))`, the partition function `Z` is the sum of
the weights, and the Gibbs probability of `s` is its weight divided by `Z`.

The Hamiltonian is Physlib's `CondensedMatter.IsingModel.energy` for `J = 1`, and `isingZ` and
`isingProb` are Physlib's canonical-ensemble partition function and probability; the bridge lemmas
are in `PhyslibExt.CondensedMatter.IsingModel.PhyslibBridge`.

## ii. Key results

- `StatMech.Ising.hamiltonian` : the Ising Hamiltonian on a finite graph
- `StatMech.Ising.isingZ` : the partition function
- `StatMech.Ising.isingProb` : the Gibbs probability of a configuration
- `StatMech.Ising.isingProb_sum_eq_one` : the Gibbs probabilities sum to one
- `StatMech.Ising.isingPMF` : the Gibbs distribution as a probability mass function

## iii. Table of contents

- A. Spins and bonds
- B. The Hamiltonian and the partition function
- C. The Gibbs distribution

## iv. References

- S. Friedli and Y. Velenik, *Statistical Mechanics of Lattice Systems: A Concrete Mathematical
  Introduction*, Cambridge University Press (2017), Chapter 3
- E. Ising, *Beitrag zur Theorie des Ferromagnetismus*, Z. Phys. 31 (1925) 253–258
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace StatMech

namespace Ising

section Spins

variable {V : Type*}

/-! ## A. Spins and bonds -/

/-- The spin `σ_x ∈ {1, -1}` of the configuration `s` at `x`: `1` for `true`, `-1` for `false`. -/
def spin (s : ConfigSpace V) (x : V) : ℝ := if s x then 1 else -1

@[simp] lemma spin_true (s : ConfigSpace V) {x : V} (hx : s x = true) : spin s x = 1 := by
  simp [spin, hx]

@[simp] lemma spin_false (s : ConfigSpace V) {x : V} (hx : s x = false) : spin s x = -1 := by
  simp [spin, hx]

lemma spin_sq (s : ConfigSpace V) (x : V) : spin s x * spin s x = 1 := by
  unfold spin; by_cases hx : s x <;> simp [hx]

lemma abs_spin_le_one (s : ConfigSpace V) (x : V) : |spin s x| ≤ 1 := by
  unfold spin; by_cases hx : s x <;> simp [hx]

/-- The bond variable `σ_x σ_y` of an unordered pair `e = {x, y}`. -/
def bond (s : ConfigSpace V) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun x y => spin s x * spin s y, fun _ _ => mul_comm _ _⟩ e

@[simp] lemma bond_mk (s : ConfigSpace V) (x y : V) :
    bond s s(x, y) = spin s x * spin s y := rfl

/-- A bond variable is `1` or `-1`. -/
lemma bond_eq_pm (s : ConfigSpace V) (e : Sym2 V) : bond s e = 1 ∨ bond s e = -1 := by
  induction e with
  | h x y =>
    rw [bond_mk]; unfold spin
    by_cases hx : s x <;> by_cases hy : s y <;> simp [hx, hy]

end Spins

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## B. The Hamiltonian and the partition function -/

/-- The Ising Hamiltonian `H(s) = -∑_{xy ∈ E(G)} σ_x σ_y - h ∑_x σ_x` on a finite graph `G` with
unit coupling and external field `h`. See also `CondensedMatter.IsingModel.energy` and
`StatMech.Ising.hamiltonian_eq_energy`. -/
def hamiltonian (h : ℝ) (s : ConfigSpace V) : ℝ :=
  - (∑ e ∈ G.edgeFinset, bond s e) - h * ∑ x, spin s x

/-- The Boltzmann weight `exp (-β H(s))` of a configuration at inverse temperature `β`. -/
noncomputable def isingWeight (β h : ℝ) (s : ConfigSpace V) : ℝ :=
  Real.exp (-β * hamiltonian G h s)

omit [DecidableEq V] in
lemma isingWeight_pos (β h : ℝ) (s : ConfigSpace V) : 0 < isingWeight G β h s :=
  Real.exp_pos _

omit [DecidableEq V] in
lemma isingWeight_nonneg (β h : ℝ) (s : ConfigSpace V) : 0 ≤ isingWeight G β h s :=
  (isingWeight_pos G β h s).le

/-- The partition function `Z = ∑_s exp (-β H(s))`. See also
`CanonicalEnsemble.mathematicalPartitionFunction` and
`StatMech.Ising.isingZ_eq_mathematicalPartitionFunction`. -/
noncomputable def isingZ (β h : ℝ) : ℝ := ∑ s : ConfigSpace V, isingWeight G β h s

/-- The partition function is positive. -/
lemma isingZ_pos (β h : ℝ) : 0 < isingZ G β h := by
  unfold isingZ
  apply Finset.sum_pos
  · intro s _; exact isingWeight_pos G β h s
  · exact Finset.univ_nonempty

lemma isingZ_ne_zero (β h : ℝ) : isingZ G β h ≠ 0 := (isingZ_pos G β h).ne'

/-! ## C. The Gibbs distribution -/

/-- The Gibbs probability `exp (-β H(s)) / Z` of a configuration. See also
`CanonicalEnsemble.probability` and `StatMech.Ising.isingProb_eq_probability`. -/
noncomputable def isingProb (β h : ℝ) (s : ConfigSpace V) : ℝ :=
  isingWeight G β h s / isingZ G β h

lemma isingProb_nonneg (β h : ℝ) (s : ConfigSpace V) : 0 ≤ isingProb G β h s :=
  div_nonneg (isingWeight_nonneg G β h s) (isingZ_pos G β h).le

lemma isingProb_pos (β h : ℝ) (s : ConfigSpace V) : 0 < isingProb G β h s :=
  div_pos (isingWeight_pos G β h s) (isingZ_pos G β h)

/-- The Gibbs probabilities sum to one. -/
lemma isingProb_sum_eq_one (β h : ℝ) : ∑ s : ConfigSpace V, isingProb G β h s = 1 := by
  unfold isingProb
  rw [← Finset.sum_div, div_eq_one_iff_eq (isingZ_ne_zero G β h)]
  rfl

/-- The finite-volume Ising Gibbs distribution as a probability mass function on configurations. -/
noncomputable def isingPMF (β h : ℝ) : PMF (ConfigSpace V) :=
  PMF.ofFintype (fun s => ENNReal.ofReal (isingProb G β h s)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => isingProb_nonneg G β h s),
      isingProb_sum_eq_one G β h]
    simp)

@[simp] lemma isingPMF_apply (β h : ℝ) (s : ConfigSpace V) :
    isingPMF G β h s = ENNReal.ofReal (isingProb G β h s) := rfl

end Ising

end StatMech
