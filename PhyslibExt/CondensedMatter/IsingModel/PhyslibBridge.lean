/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.GKS
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import PhyslibAlpha.CondensedMatter.IsingModel.Basic
public import PhyslibAlpha.CondensedMatter.Crystal.Examples.Basic
public import Physlib.StatisticalMechanics.CanonicalEnsemble.Finite

/-!
# Bridges between the StatMech Ising model and Physlib

The finite-volume Ising model of `StatMech.Ising` agrees with Physlib's Ising energy and
canonical ensemble.

## i. Overview

`StatMech.Ising.hamiltonian G h` is the energy `-∑_{xy ∈ E} σ_x σ_y - h ∑_x σ_x` of a spin
configuration on a finite graph `G`, summed over unordered edges. Physlib's
`CondensedMatter.IsingModel.energy` writes the same energy, with coupling `J` and field `h`, as half
of a sum over ordered adjacent pairs of a finite region. For `J = 1` and the region of all vertices
the two agree.

The Gibbs weights `exp (-β H)` of `StatMech.Ising` then form the finite canonical ensemble with
energy `hamiltonian G h` and counting measure on configurations: at a temperature `T`, the partition
function `isingZ G T.β h` is Physlib's `mathematicalPartitionFunction` and `isingProb G T.β h` is
Physlib's `probability`.

Finally, the nearest-neighbour graph `hypercubicLattice d` on `ℤ^d` is isomorphic to the bond graph
of Physlib's hypercubic crystal `CondensedMatter.Crystal.hypercubicGraph d`.

## ii. Key results

- `StatMech.Ising.spinB_eq_isingModelSpin` : the Boolean spin value is Physlib's.
- `StatMech.Ising.hamiltonian_eq_energy` : the Hamiltonian is Physlib's Ising energy with `J = 1`.
- `StatMech.Ising.canonicalEnsemble` : the finite canonical ensemble of the Ising model.
- `StatMech.Ising.isingZ_eq_mathematicalPartitionFunction` : the partition functions agree.
- `StatMech.Ising.isingProb_eq_probability` : the Gibbs probabilities agree.
- `StatMech.hypercubicLatticeIsoCrystal` : `hypercubicLattice d` is Physlib's hypercubic bond graph.

## iii. Table of contents

- A. The Hamiltonian as Physlib's Ising energy
- B. The finite canonical ensemble
- C. The hypercubic lattice as a crystal graph

## iv. References

- S. Friedli and Y. Velenik, *Statistical Mechanics of Lattice Systems: A Concrete Mathematical
  Introduction*, Cambridge University Press (2017), Chapter 3.
-/

@[expose] public section

open Finset

namespace StatMech

namespace Ising

/-! ## A. The Hamiltonian as Physlib's Ising energy -/

section Energy

/-- The Boolean spin value `spinB` is Physlib's `CondensedMatter.IsingModel.spin`. -/
lemma spinB_eq_isingModelSpin : spinB = CondensedMatter.IsingModel.spin := rfl

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The edge sum of `bond s` is half the sum of `σ_x σ_y` over ordered adjacent pairs. -/
lemma two_mul_sum_bond (s : ConfigSpace V) :
    2 * ∑ e ∈ G.edgeFinset, bond s e =
      ∑ x, ∑ y, if G.Adj x y then spin s x * spin s y else 0 := by
  classical
  -- Both sides are the sum of `σ_x σ_y` over the darts `(x, y)` of `G`.
  have hdart : ∑ d : G.Dart, bond s d.edge = 2 * ∑ e ∈ G.edgeFinset, bond s e := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := G.edgeFinset)
      (g := SimpleGraph.Dart.edge) (fun d _ => G.mem_edgeFinset.2 d.edge_mem), Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [Finset.sum_congr rfl (g := fun _ => bond s e) (fun d hd => by rw [(mem_filter.1 hd).2]),
      sum_const, nsmul_eq_mul, G.dart_edge_fiber_card e (G.mem_edgeFinset.1 he)]
    norm_num
  rw [← hdart]
  have hprod : ∑ x, ∑ y, (if G.Adj x y then spin s x * spin s y else 0) =
      ∑ p ∈ (univ : Finset (V × V)).filter (fun p => G.Adj p.1 p.2), spin s p.1 * spin s p.2 := by
    rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  rw [hprod]
  refine Finset.sum_bij' (fun d _ => d.toProd) (fun p hp => ⟨p, (mem_filter.1 hp).2⟩)
    (fun d _ => mem_filter.2 ⟨mem_univ _, d.adj⟩) (fun _ _ => mem_univ _)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun d _ => ?_)
  obtain ⟨⟨x, y⟩, _⟩ := d
  rfl

open scoped Classical in
/-- The Hamiltonian `hamiltonian G h` is Physlib's Ising energy
`CondensedMatter.IsingModel.energy` of the model with coupling `J = 1` and field `h`, on the region
of all vertices. -/
lemma hamiltonian_eq_energy (h : ℝ) (s : ConfigSpace V) :
    hamiltonian G h s = (⟨1, h⟩ : CondensedMatter.IsingModel G).energy Finset.univ s := by
  have hpair : ∀ x y, (⟨1, h⟩ : CondensedMatter.IsingModel G).pairSpin s x y =
      if G.Adj x y then spin s x * spin s y else 0 := fun x y => by
    simp only [CondensedMatter.IsingModel.pairSpin, CondensedMatter.IsingModel.spin, spin]
    congr
  simp only [hamiltonian, CondensedMatter.IsingModel.energy, hpair]
  rw [← two_mul_sum_bond G s]
  have hspin : ∀ x, CondensedMatter.IsingModel.spin (s x) = spin s x := fun _ => rfl
  simp only [hspin]
  ring

end Energy

/-! ## B. The finite canonical ensemble -/

section Ensemble

variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The Ising model on a finite graph `G` with field `h`, as Physlib's finite canonical ensemble:
microstates are spin configurations, the energy is `hamiltonian G h`, and the measure is the
counting measure. -/
noncomputable def canonicalEnsemble (h : ℝ) : CanonicalEnsemble (ConfigSpace V) where
  energy := hamiltonian G h
  dof := 0
  energy_measurable := measurable_of_finite _
  μ := MeasureTheory.Measure.count

/-- The Ising canonical ensemble is finite: counting measure, no degrees of freedom, and unit
phase-space unit. -/
instance (h : ℝ) : (canonicalEnsemble G h).IsFinite where
  μ_eq_count := rfl
  dof_eq_zero := rfl
  phase_space_unit_eq_one := rfl

/-- The Ising partition function at inverse temperature `T.β` is Physlib's mathematical partition
function of `canonicalEnsemble G h` at temperature `T`. -/
lemma isingZ_eq_mathematicalPartitionFunction (h : ℝ) (T : Temperature) :
    isingZ G T.β h = (canonicalEnsemble G h).mathematicalPartitionFunction T := by
  rw [CanonicalEnsemble.mathematicalPartitionFunction_of_fintype]
  rfl

/-- The Ising Gibbs probability at inverse temperature `T.β` is Physlib's canonical probability of
`canonicalEnsemble G h` at temperature `T`. -/
lemma isingProb_eq_probability (h : ℝ) (T : Temperature) (s : ConfigSpace V) :
    isingProb G T.β h s = (canonicalEnsemble G h).probability T s := by
  rw [CanonicalEnsemble.probability, ← isingZ_eq_mathematicalPartitionFunction]
  rfl

end Ensemble

end Ising

/-! ## C. The hypercubic lattice as a crystal graph -/

section Hypercubic

open CondensedMatter.Crystal StatMech.Lattice

/-- Two sites of `ℤ^d` are at `ℓ¹` distance one exactly when they differ by a unit vector. -/
lemma natAbs_sum_eq_one_iff {d : ℕ} (x y : Fin d → ℤ) :
    (∑ i, (x i - y i).natAbs) = 1 ↔
      ∃ j, y = x + Pi.single j 1 ∨ x = y + Pi.single j 1 := by
  constructor
  · intro hsum
    obtain ⟨j, hj⟩ : ∃ j, (x j - y j).natAbs ≠ 0 := by
      by_contra hne
      push Not at hne
      simp [hne] at hsum
    rw [← Finset.add_sum_erase _ _ (mem_univ j)] at hsum
    have hj1 : (x j - y j).natAbs = 1 := by omega
    have hrest : ∀ i ∈ univ.erase j, (x i - y i).natAbs = 0 :=
      Finset.sum_eq_zero_iff.1 (by omega)
    have hoff : ∀ i, i ≠ j → x i = y i := fun i hi => by
      have := hrest i (mem_erase.2 ⟨hi, mem_univ i⟩)
      omega
    refine ⟨j, ?_⟩
    rcases Int.natAbs_eq_iff.1 hj1 with h | h
    · right
      funext i
      by_cases hi : i = j
      · subst hi; simp; omega
      · simp [hi, hoff i hi]
    · left
      funext i
      by_cases hi : i = j
      · subst hi; simp; omega
      · simp [hi, hoff i hi]
  · rintro ⟨j, h | h⟩ <;> subst h <;>
      rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi])
        (fun h => absurd (mem_univ j) h)] <;> simp

/-- The nearest-neighbour graph `hypercubicLattice d` on `ℤ^d` is isomorphic to the bond graph of
Physlib's hypercubic crystal `CondensedMatter.Crystal.hypercubicGraph d`, by sending `x` to the
site in cell `x`. -/
def hypercubicLatticeIsoCrystal (d : ℕ) :
    hypercubicLattice d ≃g (hypercubicGraph d).toSimpleGraph where
  toFun x := ⟨x, ()⟩
  invFun p := p.cell
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' {x y} := by
    change ((⟨x, ()⟩ : CellSite (Fin d → ℤ) Unit) ≠ ⟨y, ()⟩ ∧ ∃ b ∈ hypercubicBonds d,
      b.Links ⟨x, ()⟩ ⟨y, ()⟩ ∨ b.Links ⟨y, ()⟩ ⟨x, ()⟩) ↔ (hypercubicLattice d).Adj x y
    rw [hypercubicLattice_adj, natAbs_sum_eq_one_iff]
    simp only [hypercubicBonds, List.mem_ofFn, Bond.Links]
    constructor
    · rintro ⟨-, b, ⟨j, rfl⟩, h⟩
      exact ⟨j, by simpa using h⟩
    · rintro ⟨j, h⟩
      refine ⟨?_, _, ⟨j, rfl⟩, by simpa using h⟩
      intro hxy
      have hxy' : x = y := congrArg CellSite.cell hxy
      subst hxy'
      rcases h with h | h <;>
        simpa using congrFun (add_eq_left.1 h.symm) j

end Hypercubic

end StatMech
