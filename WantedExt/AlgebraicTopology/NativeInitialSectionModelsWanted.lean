/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicTopology.NativeInitialSectionModels
public import MathlibExt.AlgebraicTopology.StableInfinityFiniteDiagrams

/-!
# Source-normalized initial-index cocartesian sections

Every section, fibre and evaluation operator is native. The comparison
uses an actual initial source index, with full categorical inverses.
No arc cover, descent or Perf theorem is a source hypothesis here.

Source: HTT Section 3.3.3.
-/

set_option autoImplicit false
@[expose] public section

namespace MathlibExt.AlgebraicTopology.NativeInitialSectionModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open StableInfinityFiniteDiagrams CategoricalCocartesianSections
open scoped Simplicial

universe u

/-- Construct the native fibre map of the fixed whole section evaluation. -/
def_wanted native_section_fibre_evaluation {E B A : SSet.{u}}
    (p : E ⟶ B) (q : A ⟶ B) (x : A _⦋0⦌) : SectionFibreEvaluation p q x

/-- An actual initial source index identifies the full categorical sections with its original fibre. -/
def_wanted native_initial_cocartesian_sections {E B : SSet.{u}}
    [SSet.Quasicategory E] [SSet.Quasicategory B]
    (p : E ⟶ B) (h : CocartesianFibration p) {J : Type} [Category.{0} J]
    (q : indexNerve J ⟶ B) (j : J) (hj : IsInitial j) :
    InitialSectionComparison p q (ULift.up (ComposableArrows.mk₀ j))

end MathlibExt.AlgebraicTopology.NativeInitialSectionModels
