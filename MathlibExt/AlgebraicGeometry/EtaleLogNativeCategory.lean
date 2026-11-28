/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EtaleLogDiagrams

/-!
# The native category of small-etale log schemes

Objects and morphisms are the existing ringed-site log structures and
actual monoid-sheaf triangles. Identity and composition are fixed on
every original log section by the native etale pullback comparisons.
This does not identify a log arrow merely by its image under alpha: that
image can be zero for several distinct log sections.

Ordinary categorical realization is an independent construction request.
No Kummer-flat or infinite-root comparison is an input to this category.

Source: Kato, Logarithmic structures of Fontaine--Illusie, Section1;
Talpo--Vistoli, arXiv:1410.1164v2, Definition6.10.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EtaleLogNativeCategory

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open EtaleLogSchemes EtaleLogDiagrams LogStructures SmallEtaleGeometry

universe u

variable [InverseImageTheory.{u}]

/-- The actual site identity, transported along the displayed scheme equality. -/
def identitySite {X : Scheme.{u}} (e : X ⟶ X) (h : e = 𝟙 X) :
    etaleBaseChange e ≅ 𝟭 X.Etale :=
  eqToIso (congrArg etaleBaseChange h) ≪≫ EtaleBaseChangeCoherence.identity X

/-- The actual site composition, with the final base map equality explicit. -/
def compositionSite {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : X ⟶ Z) (h : f ≫ g = c) :
    etaleBaseChange g ⋙ etaleBaseChange f ≅ etaleBaseChange c :=
  EtaleBaseChangeCoherence.composition f g ≪≫ eqToIso (congrArg etaleBaseChange h)

/-- Only the existing Hom type is used. Every underlying and log-section
map is prescribed by native identity or composition. -/
structure Operations where
  identity : ∀ X : LogScheme.{u}, EtaleLogSchemes.Hom X X
  identity_map : ∀ X : LogScheme.{u}, (identity X).map = 𝟙 X.scheme
  identity_sections : ∀ (X : LogScheme.{u}) (U : X.scheme.Etale)
      (m : (monoid X.scheme.smallEtaleTopology X.log).obj.obj (op U)),
    ((identity X).logMap.left).hom.app (op U) m =
      (monoid X.scheme.smallEtaleTopology X.log).obj.map
        ((identitySite (identity X).map (identity_map X)).hom.app U).op m
  compose : ∀ {X Y Z : LogScheme.{u}},
    EtaleLogSchemes.Hom X Y → EtaleLogSchemes.Hom Y Z → EtaleLogSchemes.Hom X Z
  compose_map : ∀ {X Y Z : LogScheme.{u}}
      (f : EtaleLogSchemes.Hom X Y) (g : EtaleLogSchemes.Hom Y Z),
    f.map ≫ g.map = (compose f g).map
  compose_sections : ∀ {X Y Z : LogScheme.{u}}
      (f : EtaleLogSchemes.Hom X Y) (g : EtaleLogSchemes.Hom Y Z)
      (U : Z.scheme.Etale)
      (m : (monoid Z.scheme.smallEtaleTopology Z.log).obj.obj (op U)),
    ((compose f g).logMap.left).hom.app (op U) m =
      (monoid X.scheme.smallEtaleTopology X.log).obj.map
        ((compositionSite f.map g.map (compose f g).map (compose_map f g)).inv.app U).op
        (f.logMap.left.hom.app (op ((etaleBaseChange g.map).obj U))
          (g.logMap.left.hom.app (op U) m))

/-- Category laws for those already prescribed operations. -/
structure Laws (O : Operations.{u}) : Prop where
  identity_comp : ∀ {X Y : LogScheme.{u}} (f : EtaleLogSchemes.Hom X Y),
    O.compose (O.identity X) f = f
  comp_identity : ∀ {X Y : LogScheme.{u}} (f : EtaleLogSchemes.Hom X Y),
    O.compose f (O.identity Y) = f
  associative : ∀ {W X Y Z : LogScheme.{u}} (f : EtaleLogSchemes.Hom W X)
      (g : EtaleLogSchemes.Hom X Y) (h : EtaleLogSchemes.Hom Y Z),
    O.compose (O.compose f g) h = O.compose f (O.compose g h)

class NativeCategoryModel where
  operations : Operations.{u}
  laws : Laws operations

namespace NativeCategoryModel

variable (N : NativeCategoryModel.{u})

/-- The category has exactly the original log Hom type, not a proxy. -/
@[instance_reducible]
def category : Category (LogScheme.{u}) where
  Hom := EtaleLogSchemes.Hom
  id := N.operations.identity
  comp := N.operations.compose
  id_comp := N.laws.identity_comp
  comp_id := N.laws.comp_identity
  assoc := N.laws.associative

/-- Forgetting the log triangle retains the actual scheme map. -/
def forget : letI := N.category; LogScheme.{u} ⥤ Scheme.{u} := by
  letI := N.category
  exact {
    obj := LogScheme.scheme
    map := EtaleLogSchemes.Hom.map
    map_id := N.operations.identity_map
    map_comp := fun f g => (N.operations.compose_map f g).symm }

end NativeCategoryModel

instance nativeCategory [N : NativeCategoryModel.{u}] : Category (LogScheme.{u}) :=
  N.category

end MathlibExt.AlgebraicGeometry.EtaleLogNativeCategory
