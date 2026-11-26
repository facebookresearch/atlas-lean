/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.MeanfieldTargetReassembly
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABFiniteGraph

/-!
# The mean-field inequality on the graph with a ghost vertex

For bond percolation with field `h` on a finite graph `G` (edges of `G` open with probability
`1 - e^{-βJ_e}`, ghost edges with probability `1 - e^{-h}`): `m (1 - M) ≤ β ∂_β M`, where `M` is the
probability that `o` reaches a target set and `m` bounds `φ(S)` from below.

## i. Overview

The reassembly `mtr_meanfield_reassembly` with `D` the edges of `G` (ghost edges excluded) bounds
`m (1 - M)` by `β ∑_e J_e P(e closed pivotal)`, and the `β`-derivative formula of `ABPhysicalDeriv`
identifies the latter sum with `β ∂_β M`. `abmg_meanfield_target_finite` treats a general target
set `B`, `abmg_meanfield_finite` the ghost target `{none}`. Both are proved; their content-carrying
hypothesis is the lower bound `hm : m ≤ φ(S)` for every possible surface `S`.

## ii. Key results

- `abmgPhi`, `abmgTargetPhi` : `φ(S)` over the edges of `G`
- `abmgTargetMag` : the probability that `o` reaches the target set
- `abmg_meanfield_target_finite` : `m (1 - M_B) ≤ β ∂_β M_B`
- `abmg_meanfield_finite` : the same with the ghost as target

## iii. Table of contents

- A. Magnetization and `φ` with a ghost
- B. The mean-field inequality

## iv. References

- M. Aizenman, D. J. Barsky, "Sharpness of the phase transition in percolation models",
  Comm. Math. Phys. 108 (1987) 489–526
- H. Duminil-Copin, V. Tassion, "A new proof of the sharpness of the phase transition for Bernoulli
  percolation and the Ising model", Comm. Math. Phys. 343 (2016) 725–745
-/

@[expose] public section

open Finset Set SimpleGraph

namespace StatMech
namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Magnetization and `φ` with a ghost -/

/-- `φ(S)` on the ghost graph, counting only edges of `G` (not ghost edges). -/
noncomputable def abmgPhi (J : Sym2 V -> Real) (o : V)
    (beta h : Real) (S : Finset (Option V)) : Real :=
  mtrPhi (withGhost G) (abfaParams G J beta h)
    (FieldGhostDict.origEdges G) (some o) S

/-- The probability `M_B(β, h)` that `o` is connected to the target set `B` in the ghost graph. -/
noncomputable def abmgTargetMag (J : Sym2 V -> Real) (o : V)
    (B : Set (Option V)) (beta h : Real) : Real :=
  probV (abfaParams G J beta h)
    (connEvent (withGhost G) Set.univ (some o) B)

/-- `φ(S)` for the target problem; it does not depend on `B` and equals `abmgPhi`. -/
noncomputable def abmgTargetPhi (J : Sym2 V -> Real) (o : V)
    (_B : Set (Option V)) (beta h : Real) (S : Finset (Option V)) : Real :=
  mtrPhi (withGhost G) (abfaParams G J beta h)
    (FieldGhostDict.origEdges G) (some o) S

/-! ## B. The mean-field inequality -/

/-- Mean-field inequality with a target set: if `m ≤ φ(S)` for every possible surface `S ∋ o`, then
`m (1 - M_B) ≤ β ∂_β M_B`. -/
theorem abmg_meanfield_target_finite (J : Sym2 V -> Real) (o : V)
    (B : Set (Option V)) (beta h m : Real)
    (hJ : ∀ e ∈ G.edgeFinset, 0 <= J e)
    (hbeta : 0 <= beta) (hh : 0 <= h)
    (hm : ∀ S : Finset (Option V), some o ∈ S ->
      (mpiSurfaceEvent (withGhost G) B S).Nonempty ->
        m <= abmgTargetPhi G J o B beta h S) :
    m * (1 - abmgTargetMag G J o B beta h) <=
      beta * deriv (fun b => abmgTargetMag G J o B b h) beta := by
  let p := abfaParams G J beta h
  let c := abfaLiftCoupling G J
  let D := FieldGhostDict.origEdges G
  have hp : ∀ e, 0 <= p e ∧ p e <= 1 :=
    abfaParams_mem G J hJ beta h hbeta hh
  have hc : ∀ e ∈ D, 0 <= c e := by
    intro e he
    exact abfaLiftCoupling_nonneg G J hJ e
  have hpc : ∀ e ∈ D, p e <= beta * c e := by
    intro e he
    have hghost : e ∉ FieldGhostDict.ghostEdges V := by
      intro hg
      exact (Finset.disjoint_left.mp (FieldGhostDict.disjoint_orig_ghost G)) he hg
    change abfaParams G J beta h e <= beta * abfaLiftCoupling G J e
    simp only [abfaParams, abpdBetaFieldParams, paramOn, hghost, ite_false]
    exact shr_pBeta_le_betaJ _ _
  have hre := mtr_meanfield_reassembly (withGhost G) p c hp D beta m hbeta
    hc hpc (some o) B (by
      intro S hoS hocc
      exact hm S hoS hocc)
  change m * (1 - abmgTargetMag G J o B beta h) <= _
  calc
    m * (1 - abmgTargetMag G J o B beta h) <=
        beta * ∑ e ∈ D, c e *
          probV p (abgiClosedPivotal e
            (mpiCrossingEvent (withGhost G) (some o) B)) := hre
    _ = beta * deriv (fun b => abmgTargetMag G J o B b h) beta := by
      change beta * ∑ e ∈ FieldGhostDict.origEdges G,
          abfaLiftCoupling G J e *
            probV (abfaParams G J beta h)
              (abgiClosedPivotal e
                (connEvent (withGhost G) Set.univ (some o) B)) =
        beta * deriv (fun b => probV (abfaParams G J b h)
          (connEvent (withGhost G) Set.univ (some o) B)) beta
      rw [abfa_deriv_beta_connTarget_eq_origEdges G J o B beta h]

/-- Mean-field inequality for the magnetization: if `m ≤ φ(S)` for every possible surface `S ∋ o`,
then `m (1 - M) ≤ β ∂_β M`, where `M` is the probability that `o` reaches the ghost. -/
theorem abmg_meanfield_finite (J : Sym2 V -> Real) (o : V)
    (beta h m : Real) (hJ : ∀ e ∈ G.edgeFinset, 0 <= J e)
    (hbeta : 0 <= beta) (hh : 0 <= h)
    (hm : ∀ S : Finset (Option V), some o ∈ S ->
      (mpiSurfaceEvent (withGhost G) {none} S).Nonempty ->
        m <= abmgPhi G J o beta h S) :
    m * (1 - abfaMag G J o beta h) <=
      beta * deriv (fun b => abfaMag G J o b h) beta := by
  let p := abfaParams G J beta h
  let c := abfaLiftCoupling G J
  let D := FieldGhostDict.origEdges G
  have hp : ∀ e, 0 <= p e ∧ p e <= 1 :=
    abfaParams_mem G J hJ beta h hbeta hh
  have hc : ∀ e ∈ D, 0 <= c e := by
    intro e he
    exact abfaLiftCoupling_nonneg G J hJ e
  have hpc : ∀ e ∈ D, p e <= beta * c e := by
    intro e he
    have hghost : e ∉ FieldGhostDict.ghostEdges V := by
      intro hg
      exact (Finset.disjoint_left.mp (FieldGhostDict.disjoint_orig_ghost G)) he hg
    change abfaParams G J beta h e <= beta * abfaLiftCoupling G J e
    simp only [abfaParams, abpdBetaFieldParams, paramOn, hghost, ite_false]
    exact shr_pBeta_le_betaJ _ _
  have hre := mtr_meanfield_reassembly (withGhost G) p c hp D beta m hbeta
    hc hpc (some o) {none} (by
      intro S hoS hocc
      exact hm S hoS hocc)
  change m * (1 - abfaMag G J o beta h) <= _
  calc
    m * (1 - abfaMag G J o beta h) <=
        beta * ∑ e ∈ D, c e *
          probV p (abgiClosedPivotal e
            (mpiCrossingEvent (withGhost G) (some o) {none})) := hre
    _ = beta * deriv (fun b => abfaMag G J o b h) beta := by
      rw [abfa_deriv_beta_eq_origEdges G J o beta h]
      rfl

end Sharpness
end StatMech
