/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.EarContraction
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.StarHull

/-!
# Faces along boundary orbits, and single-cell turning

Each dart of a boundary orbit of a set `K` of sites has a unit face on its left (`dartFace`). If
the orbit visits every face at most once per period (`usc_FaceMultiplicityOne`), the face labels of
one period are distinct, so the number of faces visited equals the orbit period. Star hulls
(`ndt_StarHull`) have this property for every boundary orbit.

The file also records that the total turning of every boundary orbit of a single cell is `±4`,
and the conditional full-revolution statements for star hulls that assume
`BalancePreservingContraction`. That hypothesis is false
(`StatMech.Lattice.not_balancePreservingContraction`), so those statements are vacuous.

## Main results

* `StatMech.Lattice.gbe_faceLabel_injOn`, `StatMech.Lattice.gbe_orbitFaces_card_eq_period`: under
  face multiplicity one, the faces of one period are distinct and there are as many as darts.
* `StatMech.Lattice.gbe_starHull_orbitFaces_card_eq_period`: the same for every boundary orbit of a
  star hull.
* `StatMech.Lattice.gbe_singleton_totalTurn_eq_four`: every boundary orbit of a single cell has
  total turning `±4`.
-/

@[expose] public section

open SimpleGraph Function Set Finset

namespace StatMech

namespace Lattice

/-- If the boundary orbit of `a` visits each face at most once per period, the faces on the left
of the darts of one period are pairwise distinct. -/
theorem gbe_faceLabel_injOn (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hmult : usc_FaceMultiplicityOne K a) :
    Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)) := by
  rw [usc_faceInjOn_iff_visit_le_one K a]
  intro f
  rcases Nat.eq_zero_or_pos (usc_visitSet K a f).card with h0 | hpos
  · omega
  · rw [hmult f hpos]

/-- If the boundary orbit of `a` visits each face at most once per period, the number of faces it
visits equals its period. -/
theorem gbe_orbitFaces_card_eq_period (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (hmult : usc_FaceMultiplicityOne K a) :
    (usc_orbitFaces K a).card = dartOrbitPeriod K a := by
  classical
  unfold usc_orbitFaces
  rw [Finset.card_image_of_injOn]
  · rw [Finset.card_range]
  · intro i hi j hj hij
    rw [Finset.coe_range, Set.mem_Iio] at hi hj
    exact gbe_faceLabel_injOn K a hmult (Set.mem_Iio.mpr hi) (Set.mem_Iio.mpr hj) hij

/-- Every boundary orbit of a star hull visits as many faces as its period. -/
theorem gbe_starHull_orbitFaces_card_eq_period (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}) :
    (usc_orbitFaces (ndt_StarHull K) a).card = dartOrbitPeriod (ndt_StarHull K) a :=
  gbe_orbitFaces_card_eq_period (ndt_StarHull K) a (ndt_faceMultiplicityOne K a)

/-- Every boundary orbit of a single cell has total turning `±4`. -/
theorem gbe_singleton_totalTurn_eq_four (v : Site 2)
    (a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}) :
    totalTurnZ ({v} : Set (Site 2)) a.1 (dartOrbitPeriod ({v} : Set (Site 2)) a) = 4 ∨
      totalTurnZ ({v} : Set (Site 2)) a.1 (dartOrbitPeriod ({v} : Set (Site 2)) a) = -4 := by
  have h := singleton_balanceIsFour v a
  unfold BalanceIsFour at h
  rw [cornerBalance_eq_totalTurnZ] at h
  exact h

/-- Under `BalancePreservingContraction`, every boundary orbit of a finite nonempty star hull
makes a full revolution. The hypothesis `BalancePreservingContraction` is false (see
`StatMech.Lattice.not_balancePreservingContraction`), so this statement is vacuous. -/
theorem gbe_totalTurn_eq_four_of_contraction (K : Set (Site 2))
    (hSK : (ndt_StarHull K).Finite) (hne : (ndt_StarHull K).Nonempty)
    (a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e})
    (hcontr : BalancePreservingContraction) :
    TurningIsFullRevolution (ndt_StarHull K) a :=
  turningIsFullRevolution_of_contraction hcontr (ndt_StarHull K) hSK hne a

end Lattice

end StatMech
