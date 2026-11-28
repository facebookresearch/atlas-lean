/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomotopyCofiber

/-!
# Degree projection from a homotopy cofiber

For a map of complexes in a preadditive category, whenever its
homotopy cofiber exists and the complex-shape relation is decidable,
the degree-`i` object at an edge `i → j` is canonically identified
with the biproduct of the shifted source term and the target term.
Its second projection is the target projection under this identification.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace HomologicalComplex.homotopyCofiber

variable {C : Type u} [Category.{v} C] [Preadditive C]

variable {ι : Type*} {c : ComplexShape ι}

/-- Let `C` be preadditive, `φ : F → G` a map of complexes of
shape `c` with a homotopy cofiber, and `c.Rel` decidable. For
`c.Rel i j`, the target projection from the degree-`i` cofiber is
its identification with `F_j ⊞ G_i` followed by `biprod.snd`. -/
lemma sndX_eq_XIsoBiprod
    {F G : HomologicalComplex C c} (φ : F ⟶ G)
    [HasHomotopyCofiber φ] [DecidableRel c.Rel]
    (i j : ι) (hij : c.Rel i j) :
    haveI := HasHomotopyCofiber.hasBinaryBiproduct φ i j hij
    sndX φ i = (XIsoBiprod φ i j hij).hom ≫ biprod.snd := by
  obtain rfl := c.next_eq' hij
  simp only [sndX, dite_eq_left hij]

end HomologicalComplex.homotopyCofiber
