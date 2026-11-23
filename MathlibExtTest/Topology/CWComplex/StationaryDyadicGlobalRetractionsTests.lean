/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.CWComplex.StationaryDyadicGlobalRetractions

noncomputable section
open CategoryTheory CategoryTheory.Limits Topology Topology.CWComplex
open scoped unitInterval
universe u

#check Topology.CWComplex.StationaryDyadicFixedStage
#print axioms Topology.CWComplex.StationaryDyadicFixedStage
#check Topology.CWComplex.StationaryDyadicGlobalRetractionsData
#print axioms Topology.CWComplex.StationaryDyadicGlobalRetractionsData
#check Topology.CWComplex.StationaryDyadicGlobalRetractionsData.tailInclusion
#print axioms Topology.CWComplex.StationaryDyadicGlobalRetractionsData.tailInclusion
#check Topology.CWComplex.StationaryDyadicGlobalRetractionsData.tailRetraction
#print axioms Topology.CWComplex.StationaryDyadicGlobalRetractionsData.tailRetraction
#check Topology.CWComplex.StationaryDyadicGlobalRetractionsData.tailInclusion_zero
#print axioms Topology.CWComplex.StationaryDyadicGlobalRetractionsData.tailInclusion_zero
#check Topology.CWComplex.StationaryDyadicGlobalRetractionsData.tailInclusion_succ
#print axioms Topology.CWComplex.StationaryDyadicGlobalRetractionsData.tailInclusion_succ
#check Topology.CWComplex.StationaryDyadicGlobalRetractionsData.tailRetraction_zero
#print axioms Topology.CWComplex.StationaryDyadicGlobalRetractionsData.tailRetraction_zero
#check Topology.CWComplex.StationaryDyadicGlobalRetractionsData.tailRetraction_succ
#print axioms Topology.CWComplex.StationaryDyadicGlobalRetractionsData.tailRetraction_succ
#check Topology.CWComplex.StationaryDyadicGlobalRetractionsData.stageFamily
#print axioms Topology.CWComplex.StationaryDyadicGlobalRetractionsData.stageFamily
#check Topology.CWComplex.StationaryDyadicGlobalRetractionsData.stageFamily_apply
#print axioms Topology.CWComplex.StationaryDyadicGlobalRetractionsData.stageFamily_apply
#check Topology.CWComplex.stationaryDyadicGlobalRetractions
#print axioms Topology.CWComplex.stationaryDyadicGlobalRetractions
#check Topology.CWComplex.stationaryDyadicGlobalRetractions_originalRetraction_comp_end
#print axioms Topology.CWComplex.stationaryDyadicGlobalRetractions_originalRetraction_comp_end
#check Topology.CWComplex.stationaryDyadicGlobalRetractions_polyhedralRetraction_comp_end
#print axioms Topology.CWComplex.stationaryDyadicGlobalRetractions_polyhedralRetraction_comp_end
#check Topology.CWComplex.stationaryDyadicGlobalRetractions_stageFamily_map
#print axioms Topology.CWComplex.stationaryDyadicGlobalRetractions_stageFamily_map
#check Topology.CWComplex.stationaryDyadicGlobalRetractions_stationary
#print axioms Topology.CWComplex.stationaryDyadicGlobalRetractions_stationary
#check Topology.CWComplex.stationaryDyadicGlobalRetractions_shared_zero
#print axioms Topology.CWComplex.stationaryDyadicGlobalRetractions_shared_zero
#check Topology.CWComplex.stationaryDyadicGlobalRetractions_interval
#print axioms Topology.CWComplex.stationaryDyadicGlobalRetractions_interval

variable (X : TopCat.{u}) [T2Space X] [CWComplex (Set.univ : Set X)]

example (x : X) :
    (stationaryDyadicGlobalRetractions X).originalRetraction
      ((commonDimensionUnion.{u, u} X).originalEnd x) = x :=
  (stationaryDyadicGlobalRetractions X).originalRetraction_end x

example (p : (commonDimensionUnion.{u, u} X).polyhedron.Realization) :
    (stationaryDyadicGlobalRetractions X).polyhedralRetraction
      ((commonDimensionUnion.{u, u} X).polyhedralEnd p) = p :=
  (stationaryDyadicGlobalRetractions X).polyhedralRetraction_end p

example (t : unitInterval) (x : X) :
    (stationaryDyadicGlobalRetractions X).originalHomotopy
      (t, (commonDimensionUnion.{u, u} X).originalEnd x) =
        (commonDimensionUnion.{u, u} X).originalEnd x :=
  (stationaryDyadicGlobalRetractions X).originalHomotopy.eq_fst t (Set.mem_range_self x)

example (t : unitInterval) (p : (commonDimensionUnion.{u, u} X).polyhedron.Realization) :
    (stationaryDyadicGlobalRetractions X).polyhedralHomotopy
      (t, (commonDimensionUnion.{u, u} X).polyhedralEnd p) =
        (commonDimensionUnion.{u, u} X).polyhedralEnd p :=
  (stationaryDyadicGlobalRetractions X).polyhedralHomotopy.eq_fst t (Set.mem_range_self p)

example (top : Bool) (t : unitInterval) {i j : ℕ} (f : i ⟶ j)
    (z : ((commonSuccessorSystem X).stages i).space) :
    (stationaryDyadicGlobalRetractions X).stageFamily top j
      (t, (Functor.ofSequence (X := fun n => ((commonSuccessorSystem X).stages n).space)
        (fun n => TopCat.ofHom ((commonSuccessorSystem X).transition n))).map f z) =
      (stationaryDyadicGlobalRetractions X).stageFamily top i (t, z) :=
  stationaryDyadicGlobalRetractions_stageFamily_map X top t f z

example (top : Bool) (n : ℕ) (t : unitInterval)
    (z : ((commonSuccessorSystem X).stages n).space) (ht : (t : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹) :
    (stationaryDyadicGlobalRetractions X).stageFamily top n (t, z) =
      (commonDimensionUnion.{u, u} X).commonCocone.ι.app n z :=
  stationaryDyadicGlobalRetractions_stationary X top n t z ht

example (top : Bool) (t : unitInterval) (j : cell (Set.univ : Set X) 0) :
    (if top then (stationaryDyadicGlobalRetractions X).polyhedralHomotopy
      (t, (commonDimensionUnion.{u, u} X).originalEnd (map (C := (Set.univ : Set X)) 0 j 0))
    else (stationaryDyadicGlobalRetractions X).originalHomotopy
      (t, (commonDimensionUnion.{u, u} X).originalEnd (map (C := (Set.univ : Set X)) 0 j 0))) =
      (commonDimensionUnion.{u, u} X).originalEnd (map (C := (Set.univ : Set X)) 0 j 0) :=
  stationaryDyadicGlobalRetractions_shared_zero X top t j

example (top : Bool) (k l : ℕ) (t : unitInterval)
    (ht : (t : ℝ) ∈ Set.Icc (((2 : ℝ) ^ (k + 1))⁻¹) (((2 : ℝ) ^ k)⁻¹))
    (z : ((commonSuccessorSystem X).stages (k + 1 + l)).space) :
    let d := stationaryDyadicGlobalRetractions X
    d.stageFamily top (k + 1 + l) (t, z) =
      (d.tailInclusion top (k + 1) l
        (d.localHomotopy top k
          (Set.projIcc 0 1 zero_le_one ((2 : ℝ) ^ (k + 1) * (t : ℝ) - 1),
            d.tailRetraction top (k + 1) l
              (⟨(commonDimensionUnion.{u, u} X).commonCocone.ι.app (k + 1 + l) z,
                Or.inr (Set.mem_range_self z)⟩ : StationaryDyadicFixedStage X top (k + 1 + l))))).val :=
  stationaryDyadicGlobalRetractions_interval X top k l t ht z

example (top : Bool) (n : ℕ) (b : StationaryDyadicFixedStage X top n) :
    let d := stationaryDyadicGlobalRetractions X
    (d.localInclusion top n b).val = b.val ∧ d.localRetraction top n (d.localInclusion top n b) = b :=
  ⟨(stationaryDyadicGlobalRetractions X).localInclusion_value top n b,
    (stationaryDyadicGlobalRetractions X).localRetraction_inclusion top n b⟩

end
