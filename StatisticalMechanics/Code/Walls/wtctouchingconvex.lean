/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


























































import Mathlib
import Code.Lattice.DartOrbit
import Code.Walls.jc4_firstreturnK
import Code.Walls.jc5_core
import Code.Walls.jc5_singlecycle
import Code.Walls.jc5_footprintdartsfinite

open SimpleGraph Function Set

namespace StatMech

namespace Walls

open StatMech.Lattice














theorem wtc_touching_iff_probes (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (i : ℕ) :
    ¬ jc4_FootprintFree K a r i ↔ jc5_ProbesEarFootprint r ((dartNext K)^[i] a.1) := by
  unfold jc4_FootprintFree
  exact jc5_not_avoidsEarFootprint_iff_probes r _



theorem wtc_free_iff_avoids (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (i : ℕ) :
    jc4_FootprintFree K a r i ↔ jc3_AvoidsEarFootprint r ((dartNext K)^[i] a.1) :=
  Iff.rfl










def wtc_touchingSteps (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2) :
    Set ℕ :=
  {i | i < dartOrbitPeriod K a ∧ ¬ jc4_FootprintFree K a r i}





theorem wtc_touchingSteps_injOn (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) :
    Set.InjOn (fun i => (dartNext K)^[i] a.1) (wtc_touchingSteps K a r) := by
  intro i hi j hj h
  have hi' : i < dartOrbitPeriod K a := hi.1
  have hj' : j < dartOrbitPeriod K a := hj.1
  
  have hsub : (dartNextSub K)^[i] a = (dartNextSub K)^[j] a := by
    apply Subtype.ext
    rw [dartNextSub_iterate_val, dartNextSub_iterate_val]
    exact h
  exact jc5_orbit_injOn_Iio K a (Set.mem_Iio.mpr hi') (Set.mem_Iio.mpr hj') hsub





theorem wtc_touchingSteps_finite (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) :
    (wtc_touchingSteps K a r).Finite := by
  apply Set.Finite.of_finite_image (f := fun i => (dartNext K)^[i] a.1) _
    (wtc_touchingSteps_injOn K a r)
  
  apply (jc5_footprintDarts_finite r).subset
  rintro _ ⟨i, hi, rfl⟩
  exact (wtc_touching_iff_probes K a r i).mp hi.2















def wtc_TouchingDartsConvex (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) : Prop :=
  ∀ i j k, i < j → j < k → k < dartOrbitPeriod K a →
    jc5_ProbesEarFootprint r ((dartNext K)^[i] a.1) →
    jc5_ProbesEarFootprint r ((dartNext K)^[k] a.1) →
    jc5_ProbesEarFootprint r ((dartNext K)^[j] a.1)














theorem wtc_touchingConvex_windowed_of_dartsConvex (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hconv : wtc_TouchingDartsConvex K a r) :
    ∀ i j k, i < j → j < k → k < dartOrbitPeriod K a →
      ¬ jc4_FootprintFree K a r i → ¬ jc4_FootprintFree K a r k →
      ¬ jc4_FootprintFree K a r j := by
  intro i j k hij hjk hk hi hkt
  rw [wtc_touching_iff_probes] at hi hkt ⊢
  exact hconv i j k hij hjk hk hi hkt









theorem wtc_touchingDartsConvex_of_disjoint (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hfoot : ∀ i, ¬ jc5_ProbesEarFootprint r ((dartNext K)^[i] a.1)) :
    wtc_TouchingDartsConvex K a r := by
  intro i _ _ _ _ _ hi _
  exact absurd hi (hfoot i)



theorem wtc_touchingConvex_of_disjoint (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hfoot : ∀ i, jc4_FootprintFree K a r i) :
    jc5_TouchingConvex K a r :=
  jc5_touchingConvex_of_disjoint K a r hfoot


























end Walls

end StatMech
