/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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

For a short complex of R-modules, its cycles form a submodule of the middle term and its
homology is a quotient of those cycles. If the middle module is Artinian, both cycles and
homology are therefore Artinian.

Applying this at any degree of a homological complex gives the same result from Artinianity of
the module in that degree. The ring, degree-index and coefficient carrier universes are
independent, and the complex shape is arbitrary.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u v w

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Ring R]

/-- Cycles of a short complex with Artinian middle module.

For a short complex of R-modules with Artinian middle term, its cycle module is Artinian by
its injective inclusion into that term. -/
theorem isArtinian_cycles_of_isArtinian_middle
    (S : ShortComplex (ModuleCat.{w} R)) [IsArtinian R S.X₂] :
    IsArtinian R S.cycles :=
  isArtinian_of_injective S.iCycles.hom
    ((ModuleCat.mono_iff_injective S.iCycles).mp inferInstance)

/-- Homology of a short complex with Artinian middle module.

For a short complex with Artinian middle R-module, its homology module is Artinian as a
quotient of the Artinian cycles. -/
theorem isArtinian_homology_of_isArtinian_middle
    (S : ShortComplex (ModuleCat.{w} R)) [IsArtinian R S.X₂] :
    IsArtinian R S.homology := by
  have : IsArtinian R S.cycles := isArtinian_cycles_of_isArtinian_middle S
  exact isArtinian_of_surjective S.cycles S.homologyπ.hom
    ((ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance)

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {R : Type u} [Ring R] {ι : Type v} {c : ComplexShape ι}

/-- Artinian cycles in an arbitrary complex degree.

If K_i is Artinian over R, then the cycles of the module complex K in degree i are Artinian,
for any complex shape. -/
theorem isArtinian_cycles_of_isArtinian_degree
    (K : HomologicalComplex (ModuleCat.{w} R) c) (i : ι) [IsArtinian R (K.X i)] :
    IsArtinian R (K.cycles i) := by
  have : IsArtinian R (K.sc i).X₂ := by
    change IsArtinian R (K.X i)
    infer_instance
  change IsArtinian R (K.sc i).cycles
  exact ShortComplex.isArtinian_cycles_of_isArtinian_middle (K.sc i)

/-- Artinian homology in an arbitrary complex degree.

If K_i is Artinian over R, then H_i(K) is Artinian, for any degree index and complex shape. -/
theorem isArtinian_homology_of_isArtinian_degree
    (K : HomologicalComplex (ModuleCat.{w} R) c) (i : ι) [IsArtinian R (K.X i)] :
    IsArtinian R (K.homology i) := by
  have : IsArtinian R (K.sc i).X₂ := by
    change IsArtinian R (K.X i)
    infer_instance
  change IsArtinian R (K.sc i).homology
  exact ShortComplex.isArtinian_homology_of_isArtinian_middle (K.sc i)

end HomologicalComplex
