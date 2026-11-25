/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite homology over a Noetherian ring

The homology in one degree of a complex of modules over a Noetherian ring is
finitely generated whenever the chain module in that degree is finitely
generated.  Indeed, cycles form a submodule of that chain module and homology
is a quotient of cycles.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace HomologicalComplex

universe u v w

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {I : Type w} {c : ComplexShape I}

/-- Homology in a fixed degree is finite when the ambient chain module in
that degree is finite and the base ring is Noetherian. -/
theorem homology_finite_of_finite
    (C : HomologicalComplex (ModuleCat.{v} R) c) (i : I)
    [C.HasHomology i] [Module.Finite R (C.X i)] :
    Module.Finite R (C.homology i) := by
  have : IsNoetherian R (C.X i) :=
    isNoetherian_of_isNoetherianRing_of_finite R (C.X i)
  have hcycles : Module.Finite R (C.cycles i) :=
    Module.Finite.of_injective (C.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  let : Module.Finite R (C.cycles i) := hcycles
  exact Module.Finite.of_surjective (C.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

end HomologicalComplex
