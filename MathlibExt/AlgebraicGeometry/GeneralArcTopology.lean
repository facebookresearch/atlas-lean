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

Covering families are the finite families that jointly have the rank-at-most-one valuation
lifting property.
The topology and its slice sites use native Grothendieck-topology operations.
No finite-type, field or Noetherian target condition is introduced.
Derived constructible and perfect-category hyperdescent are separate endpoints.

Source: Bhatt--Mathew, arXiv:1807.04725v4, Definitions 1.1--1.2
and Theorems 5.13/5.16. The valuation-ring maps are fixed in
GeneralArcCoverModels before constructing this topology.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeneralArcTopology

open CategoryTheory _root_.AlgebraicGeometry
open GeneralArcCoverModels

/-- A presieve on `X` is an arc covering when a finite family of its arrows jointly has the
valuative lifting property: every point of `X` with values in a valuation ring of rank at most
one lifts, after an extension of valuation rings, along one of the arrows. For a finite family
this says that the map from the disjoint union is an arc cover (Bhatt–Mathew, Defs. 1.1–1.2 and
4.16); the empty family covers the empty scheme. -/
def IsJointArcCover {X : QcqsScheme} (R : Presieve X) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (Y : ι → QcqsScheme) (f : ∀ i, Y i ⟶ X), (∀ i, R (f i)) ∧
    ∀ (V : RankOneValuationRing) (x : Spec (.of V.ring) ⟶ X.scheme),
      ∃ i, Nonempty (ArcLift (f i) V x)

/-- A single arc cover is an arc covering. -/
theorem isJointArcCover_singleton {X Y : QcqsScheme} {f : Y ⟶ X} (hf : IsArcCover f) :
    IsJointArcCover (Presieve.singleton f) :=
  ⟨PUnit, inferInstance, fun _ => Y, fun _ => f, fun _ => Presieve.singleton.mk,
    fun V x => ⟨PUnit.unit, hf V x⟩⟩

def precoverage : Precoverage QcqsScheme where
  coverings _ := {s | IsJointArcCover s}

def topology : GrothendieckTopology QcqsScheme := precoverage.toGrothendieck

def sliceTopology (X : QcqsScheme) : GrothendieckTopology (Over X) := topology.over X

abbrev Sheaves (A : Type*) [Category A] (X : QcqsScheme) :=
  Sheaf (sliceTopology X) A

end MathlibExt.AlgebraicGeometry.GeneralArcTopology
