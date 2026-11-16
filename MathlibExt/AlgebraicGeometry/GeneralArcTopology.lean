/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeneralArcCoverModels
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# The actual arc topology on general qcqs schemes

Cover generators are the original rank-at-most-one valuation lifting maps.
The topology and its slice sites use native Grothendieck-topology operations.
No finite-type, field or Noetherian target condition is introduced.
Derived constructible and perfect-category hyperdescent are separate endpoints.

Source: Bhatt--Mathew, arXiv:1807.04725v4, Definitions 1.1--1.2
and Theorems 5.13/5.16. The valuation-ring maps are fixed in
GeneralArcCoverModels before constructing this topology.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeneralArcTopology

open CategoryTheory
open GeneralArcCoverModels

def precoverage : Precoverage QcqsScheme where
  coverings X := {s | ∃ (Y : QcqsScheme) (f : Y ⟶ X),
    IsArcCover f ∧ s = Presieve.singleton f}

def topology : GrothendieckTopology QcqsScheme := precoverage.toGrothendieck

def sliceTopology (X : QcqsScheme) : GrothendieckTopology (Over X) := topology.over X

abbrev Sheaves (A : Type*) [Category A] (X : QcqsScheme) :=
  Sheaf (sliceTopology X) A

end MathlibExt.AlgebraicGeometry.GeneralArcTopology
