/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Sharpness.MeanfieldTargetReassembly
import Code.Sharpness.ABFiniteAssembly

open Finset Set SimpleGraph

namespace StatMech
namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]



noncomputable def abmgPhi (J : Sym2 V -> Real) (o : V)
    (beta h : Real) (S : Finset (Option V)) : Real :=
  mtrPhi (withGhost G) (abfaParams G J beta h)
    (FieldGhostDict.origEdges G) (some o) S



noncomputable def abmgTargetMag (J : Sym2 V -> Real) (o : V)
    (B : Set (Option V)) (beta h : Real) : Real :=
  probV (abfaParams G J beta h)
    (connEvent (withGhost G) Set.univ (some o) B)



noncomputable def abmgTargetPhi (J : Sym2 V -> Real) (o : V)
    (B : Set (Option V)) (beta h : Real) (S : Finset (Option V)) : Real :=
  mtrPhi (withGhost G) (abfaParams G J beta h)
    (FieldGhostDict.origEdges G) (some o) S



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
    simp only [abfaParams, abpdBetaFieldParams, paramOn, hghost, if_false]
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
    simp only [abfaParams, abpdBetaFieldParams, paramOn, hghost, if_false]
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
