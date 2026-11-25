/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: @toskua
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.RingTheory.Artinian.Module

/-!
# Artinian cycles and homology of module complexes

Cycles are subobjects of the middle module, and homology is their quotient.
The native cycle inclusion and homology-class map therefore transport the
Artinian condition from a single middle term. No condition on adjacent terms
or on the existence of a predecessor is needed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u v w

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Ring R]

/-- The cycles of a module short complex are Artinian when its middle module is. -/
theorem isArtinian_cycles_of_isArtinian_middle
    (S : ShortComplex (ModuleCat.{w} R)) [IsArtinian R S.X₂] :
    IsArtinian R S.cycles :=
  isArtinian_of_injective S.iCycles.hom
    ((ModuleCat.mono_iff_injective S.iCycles).mp inferInstance)

/-- The homology of a module short complex is Artinian when its middle module is. -/
theorem isArtinian_homology_of_isArtinian_middle
    (S : ShortComplex (ModuleCat.{w} R)) [IsArtinian R S.X₂] :
    IsArtinian R S.homology := by
  have : IsArtinian R S.cycles := isArtinian_cycles_of_isArtinian_middle S
  exact isArtinian_of_surjective S.cycles S.homologyπ.hom
    ((ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance)

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {R : Type u} [Ring R] {ι : Type v} {c : ComplexShape ι}

/-- Degree-i cycles are Artinian whenever the degree-i module is Artinian. -/
theorem isArtinian_cycles_of_isArtinian_degree
    (K : HomologicalComplex (ModuleCat.{w} R) c) (i : ι) [IsArtinian R (K.X i)] :
    IsArtinian R (K.cycles i) := by
  have : IsArtinian R (K.sc i).X₂ := by
    change IsArtinian R (K.X i)
    infer_instance
  change IsArtinian R (K.sc i).cycles
  exact ShortComplex.isArtinian_cycles_of_isArtinian_middle (K.sc i)

/-- Degree-i homology is Artinian whenever the degree-i module is Artinian. -/
theorem isArtinian_homology_of_isArtinian_degree
    (K : HomologicalComplex (ModuleCat.{w} R) c) (i : ι) [IsArtinian R (K.X i)] :
    IsArtinian R (K.homology i) := by
  have : IsArtinian R (K.sc i).X₂ := by
    change IsArtinian R (K.X i)
    infer_instance
  change IsArtinian R (K.sc i).homology
  exact ShortComplex.isArtinian_homology_of_isArtinian_middle (K.sc i)

end HomologicalComplex
