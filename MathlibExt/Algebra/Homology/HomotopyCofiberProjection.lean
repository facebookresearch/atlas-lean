/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomotopyCofiber

/-!
# Homotopy cofiber projection

Projection from the homotopy cofiber onto the biproduct factor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex.homotopyCofiber

variable {C : Type u} [Category.{v} C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι}

/-- The second projection `sndX` agrees with the biproduct isomorphism. -/
lemma sndX_eq_XIsoBiprod
    {F G : HomologicalComplex C c} (φ : F ⟶ G)
    [HasHomotopyCofiber φ] [DecidableRel c.Rel]
    (i j : ι) (hij : c.Rel i j) :
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ i j hij
    sndX φ i = (XIsoBiprod φ i j hij).hom ≫ biprod.snd := by
  obtain rfl := c.next_eq' hij
  simp only [sndX, dite_eq_left hij]

end HomologicalComplex.homotopyCofiber
