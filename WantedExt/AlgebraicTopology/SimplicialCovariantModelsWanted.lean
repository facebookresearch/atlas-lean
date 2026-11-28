/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialCovariantModels
public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Batteries.Util.ProofWanted

/-!
# Wanted native covariant fibrancy and actual left-slice mapping spaces

Reference: Lurie Higher Topos Theory §§2.1--2.2.
The slice, relative Hom and augmented covariant model have substantive
native definitions. These requests supply their actual lifting laws.
-/

open _root_.CategoryTheory
open MathlibExt.AlgebraicTopology.SimplicialCovariantModels
open scoped Simplicial

universe u

theorem_wanted native_left_slice_fibration (C : SSet.{u}) [SSet.Quasicategory C] (x : C _⦋0⦌) :
  IsLeftFibration (targetProjection C x)

def_wanted native_covariant_replacement (E B : SSet.{u}) (p : E ⟶ B) : CovariantReplacement p
