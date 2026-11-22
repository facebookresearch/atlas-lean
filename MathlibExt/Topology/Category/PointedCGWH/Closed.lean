/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.Smash
public import MathlibExt.Topology.Category.CGWH.CartesianClosed
public import MathlibExt.CategoryTheory.Monoidal.Pointed.Closed
public import MathlibExt.Topology.Category.CGWH.Limits

/-!
# Closed smash products of pointed CGWH spaces

The generic based internal-Hom pullback specializes to the closed native
CGWH subspace of maps preserving the selected basepoints.  Its generic
smash adjunction supplies evaluation, powers, copowers, and the sole native
closed-monoidal structure.  The final enriched Hom uses Mathlib's scoped
self-enrichment and installs no second enrichment instance.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory
open scoped CGWH.limits

namespace PointedCGWH

/-- The native based internal Hom, obtained from the generic pullback of
evaluation at the source basepoint along the target basepoint. -/
noncomputable def basedInternalHom (X : PointedCGWH.{u, v}) :
    PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} := by
  let _ : HasPullbacks CGWH.{u, v} := inferInstance
  letI : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  letI : SymmetricCategory CGWH.{u, v} := inferInstance
  exact CategoryTheory.Pointed.basedInternalHom
    CGWH.point CGWH.point_isTerminal X

/-- Fixed-left native smash is left adjoint to the native based internal
Hom. -/
noncomputable def smashBasedHomAdjunction (X : PointedCGWH.{u, v}) :
    PointedCGWH.smash.obj X ⊣ basedInternalHom X := by
  let _ : HasPullbacks CGWH.{u, v} := inferInstance
  letI : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  letI : SymmetricCategory CGWH.{u, v} := inferInstance
  exact CategoryTheory.Pointed.smashBasedHomAdjunction
    CGWH.point CGWH.point_isTerminal X

/-- Evaluation for the native based internal Hom. -/
noncomputable def basedEval (X : PointedCGWH.{u, v}) :
    basedInternalHom X ⋙ PointedCGWH.smash.obj X ⟶
      𝟭 PointedCGWH.{u, v} := by
  let _ : HasPullbacks CGWH.{u, v} := inferInstance
  letI : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  letI : SymmetricCategory CGWH.{u, v} := inferInstance
  exact CategoryTheory.Pointed.basedEval
    CGWH.point CGWH.point_isTerminal X

/-- Powers by a pointed CGWH space are native based internal Homs. -/
noncomputable def power (K : PointedCGWH.{u, v}) :
    PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} := by
  let _ : HasPullbacks CGWH.{u, v} := inferInstance
  letI : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  letI : SymmetricCategory CGWH.{u, v} := inferInstance
  exact CategoryTheory.Pointed.power CGWH.point CGWH.point_isTerminal K

/-- Copowers by a pointed CGWH space are fixed-left native smash products. -/
noncomputable def copower (K : PointedCGWH.{u, v}) :
    PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} := by
  let _ : HasPullbacks CGWH.{u, v} := inferInstance
  letI : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  letI : SymmetricCategory CGWH.{u, v} := inferInstance
  exact CategoryTheory.Pointed.copower CGWH.point CGWH.point_isTerminal K

/-- The native smash product and based internal Hom form the selected closed
monoidal structure on pointed CGWH spaces. -/
noncomputable instance instMonoidalClosed :
    MonoidalClosed PointedCGWH.{u, v} := by
  let _ : HasPullbacks CGWH.{u, v} := inferInstance
  letI : BraidedCategory CGWH.{u, v} :=
    BraidedCategory.ofCartesianMonoidalCategory
  letI : SymmetricCategory CGWH.{u, v} := inferInstance
  exact CategoryTheory.Pointed.smashMonoidalClosed
    CGWH.point CGWH.point_isTerminal

open scoped MonoidalClosed in
/-- The native enriched Hom from Mathlib's scoped closed self-enrichment. -/
noncomputable abbrev enrichedHom
    (X Y : PointedCGWH.{u, v}) : PointedCGWH.{u, v} :=
  EnrichedCategory.Hom X Y

end PointedCGWH
