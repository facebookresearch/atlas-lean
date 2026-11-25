/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/SimplicialSet/Pointed/Suspension.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.SimplicialSet.Pointed.Circle
public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.SimplicialSet.Pointed.Closed

/-!
# Suspension and loops of pointed simplicial sets

The simplicial suspension of a pointed simplicial set is its smash product with the simplicial
circle on the left.  Its right adjoint is the pointed mapping simplicial set out of that circle.
This file names these two functors and their adjunction, fixing the left-coordinate convention
used by spectra and reduced cohomology.

## Main definitions

* `PointedSSet.suspension`: the functor `X ↦ S¹ ∧ X`.
* `PointedSSet.loops`: the functor `Y ↦ Map_*(S¹, Y)`.
* `PointedSSet.suspensionLoopAdjunction`: the adjunction `S¹ ∧ - ⊣ Map_*(S¹, -)`.

## References

* M. Hovey, B. Shipley and J. Smith, *Symmetric spectra*, J. Amer. Math. Soc. 13 (2000),
  Section 1.
-/

public section

open CategoryTheory MonoidalCategory

namespace MathlibExt.SpectraSource.PointedSSet

/-- Simplicial suspension, with the circle as the left smash factor. -/
noncomputable abbrev suspension : PointedSSet.{0} ⥤ PointedSSet.{0} :=
  tensorLeft circle

/-- The pointed simplicial loop-space functor `Map_*(S¹, -)`. -/
noncomputable abbrev loops : PointedSSet.{0} ⥤ PointedSSet.{0} :=
  PointedSSet.ihom circle

/-- Smash with the simplicial circle is left adjoint to the pointed mapping simplicial set out
of the circle. -/
noncomputable abbrev suspensionLoopAdjunction : suspension ⊣ loops :=
  ihom.adjunction circle

end MathlibExt.SpectraSource.PointedSSet
