/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ExitDartsOrbit
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Umlaufsatz

/-!
# The far-exit-heads condition for the exit darts of a finite cluster

For a finite open cluster `C` of the origin in `ℤ²`, `StatMech.Percolation.pcFar_ExitHeadsFar`
says that for some `R`, `C ⊆ [-R, R]²` and the heads of the right and left exit darts lie outside
`[-R, R]²`. Under this condition and `InterfaceConnected C`, the two exit darts lie on one
boundary orbit, and with `OrbitFaceSimple` the exit cycle visits a face in the left half-plane.

The condition is restrictive: it forces both exit indices to equal `R`
(`StatMech.Percolation.outC_pcFarExitHeadsFar_forces_eq`), and it fails for the two-site cluster
`{(0, 0), (0, 1)}` (`StatMech.Percolation.not_forall_pcFar_ExitHeadsFar`). It cannot serve as a
hypothesis about all configurations.

## Main definitions

* `StatMech.Percolation.pcFar_ExitHeadsFar`: the far-exit-heads condition.

## Main results

* `StatMech.Percolation.pcFar_exitDartsSameOrbit_of_far`: the condition and interface
  connectivity put the exit darts on one boundary orbit.
* `StatMech.Percolation.pcFar_cycleHasLeftFace`,
  `StatMech.Percolation.pcFar_cycleHasLeftFace_of_noPinch`: the exit cycle has a face with first
  coordinate at most `0`.
-/

@[expose] public section

open Finset Set SimpleGraph Function

namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {ω : ConfigSpace (Sym2 (Site 2))}

/-- For some `R`, the origin cluster lies in `[-R, R]²` and the heads of both exit darts lie
outside `[-R, R]²`. This forces both exit indices to equal `R`; it fails for some finite clusters
(`not_forall_pcFar_ExitHeadsFar`). -/
def pcFar_ExitHeadsFar (ω : ConfigSpace (Sym2 (Site 2)))
    (hfin : (cluster 2 ω (origin 2)).Finite) : Prop :=
  ∃ R : ℕ, cluster 2 ω (origin 2) ⊆ box 2 R ∧
    (exitDart (ω := ω) hfin).head ∈ exterior 2 R ∧
    (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R

/-- Under `pcFar_ExitHeadsFar` and interface connectivity, the left exit dart lies in the
boundary orbit of the right exit dart. This is
`StatMech.Lattice.exitDart_sameOrbit_of_far` with the hypotheses packaged. -/
theorem pcFar_exitDartsSameOrbit_of_far (hfin : (cluster 2 ω (origin 2)).Finite)
    (hInt : InterfaceConnected (cluster 2 ω (origin 2)))
    (hfar : pcFar_ExitHeadsFar ω hfin) :
    ExitDartsSameOrbit ω hfin := by
  obtain ⟨R, hR, hr, hl⟩ := hfar
  exact exitDart_sameOrbit_of_far (ω := ω) hfin hInt R hR hr hl

/-- Under `OrbitFaceSimple`, interface connectivity and `pcFar_ExitHeadsFar`, some cycle of the
face-boundary graph based at the upper exit face visits a face with first coordinate `≤ 0`. -/
theorem pcFar_cycleHasLeftFace (hfin : (cluster 2 ω (origin 2)).Finite)
    (hsimple : OrbitFaceSimple ω hfin)
    (hInt : InterfaceConnected (cluster 2 ω (origin 2)))
    (hfar : pcFar_ExitHeadsFar ω hfin) :
    CycleHasLeftFace ω hfin :=
  cycleHasLeftFace_of_orbitFaceSimple (ω := ω) hfin hsimple
    (pcFar_exitDartsSameOrbit_of_far (ω := ω) hfin hInt hfar)

/-- `pcFar_cycleHasLeftFace` with `OrbitFaceSimple` replaced by an orbit of period at least `3`
with no pinched face. -/
theorem pcFar_cycleHasLeftFace_of_noPinch (hfin : (cluster 2 ω (origin 2)).Finite)
    (hp : 3 ≤ dartOrbitPeriod (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hnoPinch : OrbitFaceNoPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin))
    (hInt : InterfaceConnected (cluster 2 ω (origin 2)))
    (hfar : pcFar_ExitHeadsFar ω hfin) :
    CycleHasLeftFace ω hfin :=
  pcFar_cycleHasLeftFace (ω := ω) hfin
    ⟨hp, orbitFace_injOn_of_noPinch (cluster 2 ω (origin 2)) (exitBaseSub (ω := ω) hfin) hnoPinch⟩
    hInt hfar

end Percolation

end StatMech
