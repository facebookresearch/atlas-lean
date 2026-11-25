/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AffineNormalConeMaps
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Actual affine normal rings and coherent global normal-cone charts

Every affine ring is formed from the actual surjective section map of the
closed immersion. Restrictions use the actual section maps, and the ring
maps are fixed on coefficients and mapped degree-one kernel elements.
The global model records those full normalized restrictions. It cannot
be an arbitrary variety locally isomorphic to an unnamed cone.

Ordinary affine surjectivity and extension constructors are Mathlib at
56a005855ea17e0b0958f73ec801ae140b0a1679 (Apache 2.0). Global cone gluing
is a source integration dependency, not a new Wanted primitive.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SchemeNormalConeCharts

open CategoryTheory _root_.AlgebraicGeometry Opposite
open AffineConeAtlas AffineNormalConeMaps

variable {Z Y : Scheme.{0}} (i : Z ⟶ Y) [IsClosedImmersion i]

abbrev sectionAlgebra (U : Y.affineOpens) :
    Algebra Γ(Y, U.val) Γ(Z, i ⁻¹ᵁ U.val) :=
  (i.app U.val).hom.toAlgebra

def sectionExtension (U : Y.affineOpens) :
    @Algebra.Extension.{0} Γ(Y, U.val) Γ(Z, i ⁻¹ᵁ U.val) _ _ (sectionAlgebra i U) := by
  letI := sectionAlgebra i U
  exact Algebra.Extension.ofSurjective
    { toRingHom := (i.app U.val).hom
      commutes' := fun _ ↦ rfl } (i.app_surjective U.val U.property)

abbrev normalRing (U : Y.affineOpens) : Type := by
  letI := sectionAlgebra i U
  exact normalAlgebra (sectionExtension i U)

def coefficient (U : Y.affineOpens) : Γ(Z, i ⁻¹ᵁ U.val) →+* normalRing i U := by
  letI := sectionAlgebra i U
  exact (Algebra.TensorProduct.includeLeft
    (R := (sectionExtension i U).Ring)
    (S := Γ(Z, i ⁻¹ᵁ U.val))
    (A := Γ(Z, i ⁻¹ᵁ U.val))
    (B := reesAlgebra (sectionExtension i U).ker)).toRingHom

def baseRestriction {U V : Y.affineOpens} (h : V ≤ U) :
    Γ(Y, U.val) →+* Γ(Y, V.val) :=
  (Y.presheaf.map (homOfLE h).op).hom

def closedRestriction {U V : Y.affineOpens} (h : V ≤ U) :
    Γ(Z, i ⁻¹ᵁ U.val) →+* Γ(Z, i ⁻¹ᵁ V.val) :=
  (Z.presheaf.map (homOfLE (show i ⁻¹ᵁ V.val ≤ i ⁻¹ᵁ U.val from fun _ hx ↦ h hx)).op).hom

theorem restrictionSquare {U V : Y.affineOpens} (h : V ≤ U) :
    letI := sectionAlgebra i U
    letI := sectionAlgebra i V
    (algebraMap (sectionExtension i V).Ring Γ(Z, i ⁻¹ᵁ V.val)).comp (baseRestriction (Y := Y) h) =
      (closedRestriction i h).comp
        (algebraMap (sectionExtension i U).Ring Γ(Z, i ⁻¹ᵁ U.val)) := by
  let _ := sectionAlgebra i U
  let _ := sectionAlgebra i V
  change (i.app V.val).hom.comp _ = (closedRestriction i h).comp (i.app U.val).hom
  ext a
  exact congrArg (fun f : Γ(Y, U.val) ⟶ Γ(Z, i ⁻¹ᵁ V.val) ↦ f.hom a)
    (i.naturality (homOfLE h).op)

abbrev RestrictionMap (U V : Y.affineOpens) (h : V ≤ U) : Type := by
  letI := sectionAlgebra i U
  letI := sectionAlgebra i V
  exact NormalMap (sectionExtension i U) (sectionExtension i V)
    (baseRestriction (Y := Y) h) (closedRestriction i h) (restrictionSquare i h)

def restrictionRingMap {U V : Y.affineOpens} {h : V ≤ U}
    (R : RestrictionMap i U V h) : normalRing i U →+* normalRing i V := by
  letI := sectionAlgebra i U
  letI := sectionAlgebra i V
  exact R.map

structure NormalConeModel where
  cone : Scheme.{0}
  projection : cone ⟶ Z
  affine : ∀ U : Y.affineOpens, IsAffineOpen (projection ⁻¹ᵁ (i ⁻¹ᵁ U.val))
  chart : ∀ U : Y.affineOpens,
    Γ(cone, projection ⁻¹ᵁ (i ⁻¹ᵁ U.val)) ≃+* normalRing i U
  coefficients : ∀ (U : Y.affineOpens) (a : Γ(Z, i ⁻¹ᵁ U.val)),
    chart U ((projection.app (i ⁻¹ᵁ U.val)).hom a) = coefficient i U a
  transition : ∀ (U V : Y.affineOpens) (h : V ≤ U), RestrictionMap i U V h
  restrictions : ∀ (U V : Y.affineOpens) (h : V ≤ U)
      (a : Γ(cone, projection ⁻¹ᵁ (i ⁻¹ᵁ U.val))),
    chart V ((cone.presheaf.map
      (homOfLE (show projection ⁻¹ᵁ (i ⁻¹ᵁ V.val) ≤ projection ⁻¹ᵁ (i ⁻¹ᵁ U.val)
        from fun _ hx ↦ h hx)).op).hom a) =
      restrictionRingMap i (transition U V h) (chart U a)

end MathlibExt.AlgebraicGeometry.SchemeNormalConeCharts
