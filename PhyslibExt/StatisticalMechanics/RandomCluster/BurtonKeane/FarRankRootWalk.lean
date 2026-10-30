/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Probability.Percolation.InfiniteClusterCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.SingleCutSeparation
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmReachComponent
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestPeel
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.PrivateFarForest
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmForestRooting
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutAcyclic
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutSpanning
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmCutFunnel
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmRootSide
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootwardAvoidingWalk
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.RootParentWard

/-!
# Far-witness ranks

A three-valued rank separates three trifurcations; with a far parent, root-ward root-parent geometry
fails for all ranks and parents, while geometry-consistent root-ward walks always hold.

## i. Overview

`bc44_farWitnessRank y₀ z₀` ranks `y₀` above `z₀` above everything else; it is injective on three
trifurcations. When a trifurcation has a far parent, root-ward root-parent geometry fails for every
rank and parent. Labelled chains on `Fin 3` show the far clauses are consistent. The condition
`bc44_GeometryConsistentRootWard` holds for every rank and parent.

## ii. Key results

- `bc44_rootWardRootParent_allRankPar_false_of_farParent` : root-parent geometry fails with a far
  parent.
- `bc44_geometryConsistentRootWard_true` : geometry-consistent root-ward walks always hold.

## iii. Table of contents

- A. Far-witness ranks
- B. Labelled chains
- C. Geometry-consistent root-ward walks

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Far-witness ranks -/

/-- Rank `2` for `y₀`, `1` for `z₀` and `0` otherwise. -/
def bc44_farWitnessRank (y₀ z₀ : Site d) : Site d → ℕ ×ₗ ℕ :=
  fun w => toLex (if w = y₀ then (2 : ℕ) else if w = z₀ then 1 else 0, (0 : ℕ))

set_option linter.unusedSimpArgs false in
lemma bc44_farWitnessRank_distinct {x₀ y₀ z₀ : Site d}
    (hxy : x₀ ≠ y₀) (hxz : x₀ ≠ z₀) (hyz : y₀ ≠ z₀) {a b : Site d}
    (ha : a = x₀ ∨ a = y₀ ∨ a = z₀) (hb : b = x₀ ∨ b = y₀ ∨ b = z₀) (hab : a ≠ b) :
    bc44_farWitnessRank y₀ z₀ a ≠ bc44_farWitnessRank y₀ z₀ b := by
  intro heq
  have hab' : (if a = y₀ then (2 : ℕ) else if a = z₀ then 1 else 0)
      = (if b = y₀ then (2 : ℕ) else if b = z₀ then 1 else 0) := by
    have := congrArg (fun p => (ofLex p).1) heq
    simpa [bc44_farWitnessRank] using this
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hab
    | (simp only [↓reduceIte, ite_eq_right hxy, ite_eq_right hxz, ite_eq_right hyz,
        ite_eq_right (Ne.symm hxy),
        ite_eq_right (Ne.symm hxz), ite_eq_right (Ne.symm hyz)] at hab'; omega)

lemma bc44_farWitness_rank_injective (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ z₀ : Site d} (hxy : x₀ ≠ y₀) (hxz : x₀ ≠ z₀) (hyz : y₀ ≠ z₀)
    (hexhaust : ∀ a, a ∈ box d n → IsTrifurcation d ω a → a = x₀ ∨ a = y₀ ∨ a = z₀) :
    ∀ a, a ∈ box d n → IsTrifurcation d ω a → ∀ b, b ∈ box d n → IsTrifurcation d ω b →
      a ≠ b → Connected d ω a b →
      bc44_farWitnessRank y₀ z₀ a ≠ bc44_farWitnessRank y₀ z₀ b := by
  intro a habox htria b hbbox htrib hab _hconn
  exact bc44_farWitnessRank_distinct hxy hxz hyz
    (hexhaust a habox htria) (hexhaust b hbbox htrib) hab

lemma bc44_rootWardRootParent_allRankPar_false_of_farParent
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ z₀ : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hy0box : y₀ ∈ box d n) (htriy0 : IsTrifurcation d ω y₀)
    (hz0box : z₀ ∈ box d n) (htriz0 : IsTrifurcation d ω z₀)
    (hxy : x₀ ≠ y₀) (hxz : x₀ ≠ z₀) (hyz : y₀ ≠ z₀)
    (hexhaust : ∀ a, a ∈ box d n → IsTrifurcation d ω a → a = x₀ ∨ a = y₀ ∨ a = z₀)
    (hconn : Connected d ω x₀ y₀)
    (hadj : bc37_ArmAdjacent ω n y₀ z₀)
    (hfar : ¬ Connected d (removeSite y₀ ω) x₀ z₀) :
    ¬ ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
        bc43_RootWardRootParent ω n rank par := by
  intro hwalk
  set rank : Site d → ℕ ×ₗ ℕ := bc44_farWitnessRank y₀ z₀ with hrank
  set par : Site d → Site d := fun _ => z₀ with hpar
  have hrx : rank x₀ = toLex ((0 : ℕ), (0 : ℕ)) := by
    simp only [hrank, bc44_farWitnessRank, ite_eq_right hxy, ite_eq_right hxz]
  have hry : rank y₀ = toLex ((2 : ℕ), (0 : ℕ)) := by
    simp only [hrank, bc44_farWitnessRank, ↓reduceIte]
  have hrz : rank z₀ = toLex ((1 : ℕ), (0 : ℕ)) := by
    simp only [hrank, bc44_farWitnessRank, ite_eq_right (Ne.symm hyz), ↓reduceIte]
  have hinj : ∀ a, a ∈ box d n → IsTrifurcation d ω a → ∀ b, b ∈ box d n → IsTrifurcation d ω b →
      a ≠ b → Connected d ω a b → rank a ≠ rank b :=
    bc44_farWitness_rank_injective ω n hxy hxz hyz hexhaust
  have hlt : rank x₀ < rank y₀ := by rw [hrx, hry]; exact stt_lex_lt_fst (by norm_num)
  have hxpar : x₀ ≠ par y₀ := by simpa [hpar] using hxz
  have hprank : rank (par y₀) < rank y₀ := by
    simp only [hpar]; rw [hrz, hry]; exact stt_lex_lt_fst (by norm_num)
  have hadj' : bc37_ArmAdjacent ω n y₀ (par y₀) := by simpa [hpar] using hadj
  obtain ⟨p, hp⟩ :=
    hwalk rank par hinj x₀ hx0box htri0 y₀ hy0box htriy0 hxy hconn hlt hxpar
      (by simpa [hpar] using hz0box) (by simpa [hpar] using htriz0) hadj' hprank
  have hconn_cut : Connected d (removeSite y₀ ω) x₀ (par y₀) :=
    (bc42_avoidingWalk_iff_connected_removeSite ω hxy).mp ⟨p, hp⟩
  simp only [hpar] at hconn_cut
  exact hfar hconn_cut

/-! ## B. Labelled chains -/

/-- Component labels for a chain on `Fin 3`. -/
def bc44_chainLab (c v : Fin 3) : ℕ :=
  if c = 2 then 7
  else if c = 1 then
    (if v = 1 then 101 else if v = 0 then 0 else 2)
  else
    (if v = 0 then 100 else 1)

lemma bc44_chainFar_consistent :
    ∃ (x₀ y₀ z₀ : Fin 3) (R : Fin 3 → Fin 3 → Fin 3 → Prop),
      (∀ c u v, R c u v ↔ bc44_chainLab c u = bc44_chainLab c v) ∧
      x₀ ≠ y₀ ∧ x₀ ≠ z₀ ∧ y₀ ≠ z₀ ∧
      R 2 x₀ y₀ ∧
      R 2 x₀ z₀ ∧
      R 0 y₀ z₀ ∧
      ¬ R 1 x₀ z₀ := by
  refine ⟨0, 1, 2, (fun c u v => bc44_chainLab c u = bc44_chainLab c v),
    fun _ _ _ => Iff.rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## C. Geometry-consistent root-ward walks -/

/-- Geometry-consistent root-ward walks: for connected trifurcations of different rank, an open walk
from the lower one to the parent of the higher one avoiding the higher one whenever the parent is on
the root side. -/
def bc44_GeometryConsistentRootWard (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d) : Prop :=
  (∀ a, a ∈ box d n → IsTrifurcation d ω a → ∀ b, b ∈ box d n → IsTrifurcation d ω b →
      a ≠ b → Connected d ω a b → rank a ≠ rank b) →
  ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
    x ≠ y → Connected d ω x y → rank x < rank y → x ≠ par y →
    par y ∈ box d n → IsTrifurcation d ω (par y) →
    bc37_ArmAdjacent ω n y (par y) → rank (par y) < rank y →
    Connected d (removeSite y ω) x (par y) →
    ∃ p : (openSubgraph d ω).Walk x (par y), ∀ v ∈ p.support, v ≠ y

lemma bc44_geometryConsistentRootWard_true (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d) :
    bc44_GeometryConsistentRootWard ω n rank par := by
  intro _hinj x _hxbox _htri y _hybox _htriy hxy _hconn _hlt _hxpar _hpbox _hptri _hadj _hprank hgeo
  exact (bc42_avoidingWalk_iff_connected_removeSite ω hxy).mpr hgeo

end StatMech.Walls
