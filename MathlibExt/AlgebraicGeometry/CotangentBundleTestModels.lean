/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeneralModuleTotalSpaces
public import MathlibExt.AlgebraicGeometry.LocalDifferentialPullbacks

/-!
# Closed cones and actual geometric cotangent fibres

The cotangent bundle represents sections of the actual sheaf of Kähler
one-forms. A covector at a geometric point is an actual section of that
pulled-back sheaf, and its point in the bundle is the universal-property
map. Closed cones are closed subsets of that scheme, invariant under every
nonzero geometric scalar. No replacement cotangent vector space is given.

Reference: Beilinson, arXiv:1505.06768v8, Sections 1.1--1.2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CotangentBundleTestModels

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Opposite
open AlgebraicDifferentialSheaves LocalDifferentialPullbacks GeneralModuleTotalSpaces

/-- A geometric coefficient field, with its actual algebraic closure property. -/
structure GeometricField where
  carrier : Type
  [field : Field carrier]
  [closed : IsAlgClosed carrier]

attribute [instance] GeometricField.field GeometricField.closed

variable {k : Type} [Field k] (X : Over (Spec (.of k)))

/-- The ordinary total space of the actual cotangent module sheaf. -/
abbrev CotangentBundle := TotalSpace X.left (forms k X 1)

/-- The native cotangent module at a geometric point. -/
abbrev Covector (Ω : GeometricField) (x : Spec (.of Ω.carrier) ⟶ X.left) :=
  CotangentFibre (X := X) x

/-- The scheme-valued point represented by that actual covector. -/
def covectorPoint (B : CotangentBundle X) (Ω : GeometricField)
    (x : Spec (.of Ω.carrier) ⟶ X.left) (v : Covector X Ω x) :
    Spec (.of Ω.carrier) ⟶ B.total := B.lift x v

@[simp] theorem covectorPoint_projection (B : CotangentBundle X) (Ω : GeometricField)
    (x : Spec (.of Ω.carrier) ⟶ X.left) (v : Covector X Ω x) :
    covectorPoint X B Ω x v ≫ B.projection = x := B.lift_over x v

/-- Membership uses the actual point of the actual cotangent total space. -/
def At (B : CotangentBundle X) (C : Set B.total) (Ω : GeometricField)
    (x : Spec (.of Ω.carrier) ⟶ X.left) (v : Covector X Ω x) : Prop :=
  Set.range (covectorPoint X B Ω x v) ⊆ C

/-- The scalar on a geometric cotangent fibre is the native Γ(Spec Ω) scalar. -/
def scalar (Ω : GeometricField) (a : Ω.carrier) : Γ(Spec (.of Ω.carrier), ⊤) :=
  (Scheme.ΓSpecIso (.of Ω.carrier)).inv.hom a

/-- A closed conical subset; nonzero scalars act on actual module fibres. -/
structure ClosedCone (B : CotangentBundle X) where
  support : Set B.total
  closed : IsClosed support
  conical : ∀ (Ω : GeometricField) (x : Spec (.of Ω.carrier) ⟶ X.left)
    (v : Covector X Ω x) (a : Ω.carrierˣ),
    At X B support Ω x v ↔ At X B support Ω x (scalar Ω a.val • v)

namespace ClosedCone

variable {X} {B : CotangentBundle X} (C : ClosedCone X B)

abbrev memFibre (Ω : GeometricField) (x : Spec (.of Ω.carrier) ⟶ X.left)
    (v : Covector X Ω x) : Prop := At X B C.support Ω x v

/-- Cone inclusion is inclusion in the actual total-space scheme. -/
def LE (D : ClosedCone X B) : Prop := C.support ⊆ D.support

end ClosedCone

variable {X} {U : Over (Spec (.of k))} (h : U ⟶ X)
  (D : PullbackDifferential X h)

/-- The cotangent map is computed from the same normalized Kähler sheaf map. -/
def dh (Ω : GeometricField) (u : Spec (.of Ω.carrier) ⟶ U.left) :
    Covector X Ω (u ≫ h.left) →ₗ[Γ(Spec (.of Ω.carrier), ⊤)] Covector U Ω u :=
  fibreMap D u

@[simp] theorem dh_zero (Ω : GeometricField) (u : Spec (.of Ω.carrier) ⟶ U.left) :
    dh h D Ω u 0 = 0 := map_zero _

end MathlibExt.AlgebraicGeometry.CotangentBundleTestModels
