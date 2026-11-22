/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.MagPercoIdBox
public import PhyslibExt.StatisticalMechanics.RandomCluster.TwoPointInfinite

/-!
# Box-boundary connection probabilities for the wired `q = 2` measure

The event that the origin is connected to the boundary of the box `Λ_n`, its basic properties,
and its relation to the box-boundary connection profile of the Ising FK representation.

## i. Overview

`boxBdryConnEvent d n` is the event, on configurations of `ℤ^d`, that the origin of `Λ_n` is
joined to `∂Λ_n` by open edges of `Λ_n`. It is clopen and increasing. Under the wired finite-volume
measure on `Λ_n` with `q = 2` its probability equals the wired connection-to-boundary probability
of the box graph, which is the box-boundary connection profile used in the Ising FK
representation. If these probabilities converge to `θ(p, 2)` along the diagonal, the profile
converges to `θ(p, 2)` as well.

## ii. Key results

- `isIncreasing_boxBdryConnEvent`, `isClopen_boxBdryConnEvent` : regularity of the event.
- `wiredFiniteMeasure_real_boxBdryConnEvent` : its wired probability is the connection-to-boundary
  probability of the box graph.
- `boxBoundaryConnProfile_tendsto_of_diag` : convergence of the Ising box-boundary profile to
  `θ(p, 2)`.

## iii. Table of contents

- A. The box-boundary connection event
- B. Wired probabilities and the Ising profile

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), §5.1.
-/

@[expose] public section

open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK StatMech.Percolation

variable {d : ℕ}

/-! ## A. The box-boundary connection event -/

/-- The event that the origin of the box `Λ_n` is connected to the boundary `∂Λ_n` by open edges of
`Λ_n`.
-/
def boxBdryConnEvent (d n : ℕ) : Set (ConfigSpace (Sym2 (Site d))) :=
  boxRestrict d n ⁻¹'
    {ω' : ConfigSpace (Sym2 (boxVerts d n)) |
      ConnToBdry (boxGraph d n) (boxBoundary d n) ω' (IsingFK.boxOrigin d n)}

lemma boxBdryConnEvent_eq_iUnion (d n : ℕ) :
    boxBdryConnEvent d n
      = ⋃ v ∈ {v : boxVerts d n | boxBoundary d n v},
          boxConnEvent d n (IsingFK.boxOrigin d n) v := by
  ext ω
  simp only [boxBdryConnEvent, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_iUnion,
    boxConnEvent, ConnToBdry]
  constructor
  · rintro ⟨v, hv, hconn⟩
    exact ⟨v, hv, hconn⟩
  · rintro ⟨v, hv, hconn⟩
    exact ⟨v, hv, hconn⟩

lemma isClopen_boxBdryConnEvent (d n : ℕ) : IsClopen (boxBdryConnEvent d n) := by
  rw [boxBdryConnEvent_eq_iUnion]
  refine Set.Finite.isClopen_biUnion (Set.toFinite _) ?_
  exact fun v _ => isClopen_boxConnEvent d n (IsingFK.boxOrigin d n) v

lemma measurableSet_boxBdryConnEvent (d n : ℕ) :
    MeasurableSet (boxBdryConnEvent d n) :=
  (isClopen_boxBdryConnEvent d n).isOpen.measurableSet

lemma isIncreasing_boxBdryConnEvent (d n : ℕ) :
    IsIncreasing (boxBdryConnEvent d n) := by
  rw [boxBdryConnEvent_eq_iUnion]
  exact isUpperSet_iUnion₂ (fun v _ => isIncreasing_boxConnEvent d n (IsingFK.boxOrigin d n) v)

lemma extendEdge_preimage_boxBdryConnEvent (d n : ℕ) :
    extendEdge d n ⁻¹' (boxBdryConnEvent d n)
      = {ω : ConfigSpace (Sym2 (boxVerts d n)) |
          ConnToBdry (boxGraph d n) (boxBoundary d n) ω (IsingFK.boxOrigin d n)} := by
  ext ω
  simp only [boxBdryConnEvent, Set.mem_preimage, Set.mem_ofPred_eq, boxRestrict_extendEdge]

/-! ## B. Wired probabilities and the Ising profile -/

lemma wiredFiniteMeasure_real_boxBdryConnEvent (d n : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    (wiredFiniteMeasure d n hp hp1 (by norm_num : (0 : ℝ) < 2)
        : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n)
      = wiredConnToBdryProb (boxGraph d n) (boxBoundary d n) p (IsingFK.boxOrigin d n) := by
  classical
  have hA : MeasurableSet (boxBdryConnEvent d n) := measurableSet_boxBdryConnEvent d n
  have hw : (wiredFiniteMeasure d n hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure _).real
        (boxBdryConnEvent d n)
      = ((wiredFkPMF (boxGraph d n) (boxBoundary d n) hp hp1 (by norm_num : (0 : ℝ) < 2)).toMeasure
          (extendEdge d n ⁻¹' (boxBdryConnEvent d n))).toReal := by
    unfold wiredFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d n) hA]
  rw [hw, extendEdge_preimage_boxBdryConnEvent,
    wiredFkPMF_toMeasure_toReal d n hp hp1 (by norm_num : (0 : ℝ) < 2)]
  rw [wiredConnToBdryProb_eq_wiredFkProb_sum (boxGraph d n) (boxBoundary d n) p
    (IsingFK.boxOrigin d n)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ω _
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  by_cases hω : ConnToBdry (boxGraph d n) (boxBoundary d n) ω (IsingFK.boxOrigin d n)
  · rw [ite_eq_left hω, ite_eq_left hω, one_mul]
  · rw [ite_eq_right hω, ite_eq_right hω, zero_mul]

lemma boxBoundaryConnProfile_eq_wiredFiniteMeasure_real (d n : ℕ) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) :
    IsingFK.boxBoundaryConnProfile d hp hp1 (by norm_num : (0 : ℝ) < 2) n
      = (wiredFiniteMeasure d n hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
  rw [IsingFK.boxBoundaryConnProfile, wiredFiniteMeasure_real_boxBdryConnEvent d n hp hp1]

/-- If the wired `q = 2` probabilities of `{0 ↔ ∂Λ_n}` converge to `θ(p, 2)`, then so does the
Ising
box-boundary connection profile.
-/
lemma boxBoundaryConnProfile_tendsto_of_diag (d : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hdiag : Tendsto
      (fun n => (wiredFiniteMeasure d n hp hp1 (by norm_num : (0 : ℝ) < 2)
          : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n))
      atTop (𝓝 (fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)))) :
    Tendsto (fun n => IsingFK.boxBoundaryConnProfile d hp hp1 (by norm_num : (0 : ℝ) < 2) n)
      atTop (𝓝 (fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))) := by
  refine hdiag.congr (fun n => ?_)
  exact (boxBoundaryConnProfile_eq_wiredFiniteMeasure_real d n hp hp1).symm

end FK

end StatMech
