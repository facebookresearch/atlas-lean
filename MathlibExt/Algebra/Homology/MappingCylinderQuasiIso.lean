/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module


public import Mathlib.Algebra.Homology.QuasiIso
public import MathlibExt.Algebra.Homology.MappingCylinder

/-!
# Quasi-isomorphisms from mapping cylinders

The endpoint and projection of a mapping cylinder are quasi-isomorphisms
because they form a proved homotopy equivalence.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex.mappingCylinder

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasBinaryBiproducts C]
variable {ι : Type w} {c : ComplexShape ι} [DecidableRel c.Rel]
variable {F G : HomologicalComplex C c}

/-- The target endpoint of a mapping cylinder is a quasi-isomorphism. -/
theorem target_quasiIso (f : F ⟶ G) [HasMappingCylinder f]
    (H : ∀ j, ∃ i, c.Rel i j)
    [∀ i, G.HasHomology i]
    [∀ i, (HomologicalComplex.mappingCylinder f).HasHomology i] :
    QuasiIso (target f) :=
  (homotopyEquiv f H).quasiIso_hom

/-- The mapping-cylinder projection is a quasi-isomorphism. -/
theorem projection_quasiIso (f : F ⟶ G) [HasMappingCylinder f]
    (H : ∀ j, ∃ i, c.Rel i j)
    [∀ i, G.HasHomology i]
    [∀ i, (HomologicalComplex.mappingCylinder f).HasHomology i] :
    QuasiIso (projection f) :=
  (homotopyEquiv f H).quasiIso_inv

end HomologicalComplex.mappingCylinder

end
