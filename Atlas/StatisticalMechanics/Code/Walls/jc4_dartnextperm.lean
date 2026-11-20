/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.DartDef
import Code.Lattice.DartNext
import Code.Lattice.DartInjective
import Code.Lattice.DartOrbit
import Code.Lattice.StarHullPeriod
import Code.Lattice.JordanSingleCycle

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice











theorem jc4_dartNextSub_injective (K : Set (Site 2)) :
    Function.Injective (dartNextSub K) :=
  dartNextSub_injective K




theorem jc4_dartNextSub_bijective (K : Set (Site 2)) (hK : K.Finite) :
    Function.Bijective (dartNextSub K) := by
  have : Finite {e : Dart // IsBoundaryDart K e} := (boundaryDarts_finite K hK).to_subtype
  exact Finite.injective_iff_bijective.mp (jc4_dartNextSub_injective K)




theorem jc4_dartNextSub_surjective (K : Set (Site 2)) (hK : K.Finite) :
    Function.Surjective (dartNextSub K) :=
  (jc4_dartNextSub_bijective K hK).2




theorem jc4_dartNextSub_ne_self (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    dartNextSub K a ≠ a :=
  dartNextSub_ne_self K a










theorem jc4_dartNext_periodic (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) : ∃ p > 0, (dartNext K)^[p] e = e :=
  dartNext_periodic K hK e he




theorem jc4_dartNextSub_mem_periodicPts (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) : a ∈ Function.periodicPts (dartNextSub K) := by
  have : Finite {e : Dart // IsBoundaryDart K e} := (boundaryDarts_finite K hK).to_subtype
  exact (jc4_dartNextSub_injective K).mem_periodicPts a









theorem jc4_dartOrbitPeriod_eq_minimalPeriod (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    dartOrbitPeriod K a = Function.minimalPeriod (dartNextSub K) a := rfl



theorem jc4_dartOrbitPeriod_pos (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) : 0 < dartOrbitPeriod K a :=
  dartOrbitPeriod_pos K hK a




theorem jc4_one_lt_dartOrbitPeriod (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) : 1 < dartOrbitPeriod K a :=
  one_lt_dartOrbitPeriod K hK a



theorem jc4_dartOrbitPeriod_iterate (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (dartNextSub K)^[dartOrbitPeriod K a] a = a :=
  dartOrbitPeriod_iterate K a















theorem jc4_dartOrbitWalk_edges (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    (dartOrbitWalk K a).edges
      = (List.range (dartOrbitPeriod K a)).map
          (fun k => s((dartNextSub K)^[k] a, (dartNextSub K)^[k + 1] a)) := by
  have haux : ∀ n, (orbitWalkAux K a n).edges
      = (List.range n).map (fun k => s((dartNextSub K)^[k] a, (dartNextSub K)^[k + 1] a)) := by
    intro n
    induction n with
    | zero => rfl
    | succ m ih =>
      rw [orbitWalkAux, SimpleGraph.Walk.edges_concat, ih, List.range_succ, List.map_append]
      simp only [List.concat_eq_append, List.map_cons, List.map_nil, Function.iterate_succ_apply']
  rw [dartOrbitWalk, SimpleGraph.Walk.edges_copy, haux]




















theorem jc4_dartOrbitWalk_isCycle (K : Set (Site 2)) (hK : K.Finite)
    (a : {e : Dart // IsBoundaryDart K e}) :
    (dartOrbitWalk K a).IsCycle := by
  set p := dartOrbitPeriod K a with hp
  have hpe : p = Function.minimalPeriod (dartNextSub K) a := rfl
  have hp3 : 3 ≤ p := shp_period_ge_three K hK a
  set g : ℕ → {e : Dart // IsBoundaryDart K e} := fun k => (dartNextSub K)^[k] a with hg
  have hper : ∀ k, g k = g (k % p) := by
    intro k
    change (dartNextSub K)^[k] a = (dartNextSub K)^[k % p] a
    rw [hpe, Function.iterate_mod_minimalPeriod_eq]
  have hinj : Set.InjOn g (Set.Iio p) := by
    intro i hi j hj h
    exact Function.iterate_injOn_Iio_minimalPeriod (Set.mem_Iio.mp hi) (Set.mem_Iio.mp hj) h
  rw [Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · 
    rw [Walk.isTrail_def, jc4_dartOrbitWalk_edges]
    exact polygon_edges_nodup g p hp3 hper hinj
  · 
    exact dartOrbitWalk_ne_nil K hK a
  · 
    exact dartOrbitWalk_support_tail_nodup K hK a











def jc4_DartNextPerm (K : Set (Site 2)) : Prop :=
  Function.Injective (dartNextSub K) ∧
    ∀ a : {e : Dart // IsBoundaryDart K e},
      dartOrbitPeriod K a = Function.minimalPeriod (dartNextSub K) a ∧
      0 < dartOrbitPeriod K a ∧
      (dartNextSub K)^[dartOrbitPeriod K a] a = a ∧
      (dartOrbitWalk K a).IsCycle




theorem jc4_dartNextPerm (K : Set (Site 2)) (hK : K.Finite) : jc4_DartNextPerm K := by
  refine ⟨jc4_dartNextSub_injective K, fun a => ⟨rfl, ?_, ?_, ?_⟩⟩
  · exact jc4_dartOrbitPeriod_pos K hK a
  · exact jc4_dartOrbitPeriod_iterate K a
  · exact jc4_dartOrbitWalk_isCycle K hK a

end Walls

end StatMech
