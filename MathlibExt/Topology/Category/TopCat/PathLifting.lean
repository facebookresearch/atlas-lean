/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyPullback

/-!
# Continuous-family path lifting in `TopCat`

This file packages a continuous lifting operator for compatible starting
points and compact-open base paths. It supplies family-level start and
projection laws, endpoint transport, and constant-path transport.

It makes no unique-lifting, regularity, fibration, inverse, homotopy,
weak-equivalence, realization, bar, `EG`, or `BG` claim and installs no
instance.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Topology

universe u

namespace TopCat

/-- Starting points paired with compact-open base paths having the matching
initial endpoint. -/
abbrev pathLiftInput {E B : TopCat.{u}} (p : E ⟶ B) : TopCat.{u} :=
  pullback p (TopCat.pathEvalZero B)

/-- The supplied starting point of a path-lifting input. -/
abbrev pathLiftStart {E B : TopCat.{u}} (p : E ⟶ B) :
    pathLiftInput p ⟶ E :=
  pullback.fst p (TopCat.pathEvalZero B)

/-- The supplied compact-open base path of a path-lifting input. -/
abbrev pathLiftBasePath {E B : TopCat.{u}} (p : E ⟶ B) :
    pathLiftInput p ⟶ TopCat.pathObject B :=
  pullback.snd p (TopCat.pathEvalZero B)

/-- A continuous-family path-lifting operator. Its input pullback encodes
the matching initial endpoint; its two laws specify the lifted start and
the full pointwise projection. -/
structure PathLiftingData {E B : TopCat.{u}} (p : E ⟶ B) where
  lift : pathLiftInput p ⟶ TopCat.pathObject E
  lift_zero : lift ≫ TopCat.pathEvalZero E = pathLiftStart p
  lift_proj : lift ≫ TopCat.pathObjectMap p = pathLiftBasePath p

/-- Lift a continuously parameterized family of compatible starting points
and base paths. -/
noncomputable def PathLiftingData.liftFamily
    {E B Z : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p)
    (start : Z ⟶ E) (basePath : Z ⟶ TopCat.pathObject B)
    (compatibility : start ≫ p = basePath ≫ TopCat.pathEvalZero B) :
    Z ⟶ TopCat.pathObject E :=
  pullback.lift start basePath compatibility ≫ L.lift

@[reassoc]
theorem PathLiftingData.liftFamily_zero
    {E B Z : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p)
    (start : Z ⟶ E) (basePath : Z ⟶ TopCat.pathObject B)
    (compatibility : start ≫ p = basePath ≫ TopCat.pathEvalZero B) :
    L.liftFamily start basePath compatibility ≫ TopCat.pathEvalZero E =
      start := by
  rw [PathLiftingData.liftFamily, Category.assoc, L.lift_zero,
    pullback.lift_fst]

@[reassoc]
theorem PathLiftingData.liftFamily_proj
    {E B Z : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p)
    (start : Z ⟶ E) (basePath : Z ⟶ TopCat.pathObject B)
    (compatibility : start ≫ p = basePath ≫ TopCat.pathEvalZero B) :
    L.liftFamily start basePath compatibility ≫ TopCat.pathObjectMap p =
      basePath := by
  rw [PathLiftingData.liftFamily, Category.assoc, L.lift_proj,
    pullback.lift_snd]

/-- Endpoint transport for every compatible starting-point/path pair. -/
def PathLiftingData.liftEndpoint
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p) :
    pathLiftInput p ⟶ E :=
  L.lift ≫ TopCat.pathEvalOne E

@[reassoc]
theorem PathLiftingData.liftEndpoint_proj
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p) :
    L.liftEndpoint ≫ p =
      pathLiftBasePath p ≫ TopCat.pathEvalOne B := by
  rw [PathLiftingData.liftEndpoint, Category.assoc,
    ← TopCat.pathObjectMap_evalOne]
  rw [← Category.assoc, L.lift_proj]

/-- The continuously parameterized family of constant base paths. -/
def constantBasePathFamily {E B : TopCat.{u}} (p : E ⟶ B) :
    E ⟶ TopCat.pathObject B :=
  TopCat.ofHom ((ContinuousMap.const'
    (X := TopCat.I.{u}) (Y := B)).comp p.hom)

@[reassoc]
theorem constantBasePathFamily_zero {E B : TopCat.{u}} (p : E ⟶ B) :
    constantBasePathFamily p ≫ TopCat.pathEvalZero B = p := by
  ext e
  simp [constantBasePathFamily, TopCat.pathEvalZero]

@[reassoc]
theorem constantBasePathFamily_one {E B : TopCat.{u}} (p : E ⟶ B) :
    constantBasePathFamily p ≫ TopCat.pathEvalOne B = p := by
  ext e
  simp [constantBasePathFamily, TopCat.pathEvalOne]

/-- Lift the constant base path continuously from every starting point. -/
noncomputable def PathLiftingData.constantLift
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p) :
    E ⟶ TopCat.pathObject E :=
  L.liftFamily (𝟙 E) (constantBasePathFamily p) (by
    rw [Category.id_comp, constantBasePathFamily_zero])

@[reassoc]
theorem PathLiftingData.constantLift_zero
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p) :
    L.constantLift ≫ TopCat.pathEvalZero E = 𝟙 E := by
  apply PathLiftingData.liftFamily_zero

@[reassoc]
theorem PathLiftingData.constantLift_proj
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p) :
    L.constantLift ≫ TopCat.pathObjectMap p =
      constantBasePathFamily p := by
  apply PathLiftingData.liftFamily_proj

/-- Endpoint transport along constant base paths. It is fiberwise homotopic
to the identity via `constantLift`; no equality with the identity is assumed. -/
def PathLiftingData.constantTransport
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p) : E ⟶ E :=
  L.constantLift ≫ TopCat.pathEvalOne E

@[reassoc]
theorem PathLiftingData.constantTransport_proj
    {E B : TopCat.{u}} {p : E ⟶ B} (L : PathLiftingData p) :
    L.constantTransport ≫ p = p := by
  rw [PathLiftingData.constantTransport, Category.assoc,
    ← TopCat.pathObjectMap_evalOne]
  rw [← Category.assoc, L.constantLift_proj,
    constantBasePathFamily_one]

end TopCat

end
