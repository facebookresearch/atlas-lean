/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.KTheory.Exact.Quillen.QuillenSpanEndpointNaturality
public import MathlibExt.CategoryTheory.Waldhausen.Exact
import MathlibExt.KTheory.Exact.Quillen.SpanFlagStageShell

/-!
# Tests for converse endpoint naturality of Quillen spans

These tests exercise converse existence and uniqueness, all four leg
computations, identity and repeated spans, inverse and transitive endpoint
comparisons, independent universes, and spans coming from degree-two Stage
shells.  Composition here is composition of comparisons only; no flagged-span
composition, fiber connectedness, contractibility, or weak-equivalence claim
is tested or exposed.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace MathlibExtTest.KTheory.Categorical.QuillenSpanEndpointNaturalityTests

open AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

section PublicApi

variable {X X' X'' Y Y' Y'' : C}
variable (S : QuillenSpan X Y) (T : QuillenSpan X' Y')
  (U : QuillenSpan X'' Y'')
variable (eX : X ≅ X') (eY : Y ≅ Y')
  (fX : X' ≅ X'') (fY : Y' ≅ Y'')

example
    (h : QuillenQ.mkHom S ≫ (QuillenQ.underlyingIso eY).hom =
      (QuillenQ.underlyingIso eX).hom ≫ QuillenQ.mkHom T) :
    Nonempty (QuillenSpan.EndpointIso S T eX eY) :=
  QuillenQ.endpointIso_nonempty_of_mkHom_naturality S T eX eY h

example
    (h : QuillenQ.mkHom S ≫ (QuillenQ.underlyingIso eY).hom =
      (QuillenQ.underlyingIso eX).hom ≫ QuillenQ.mkHom T) :
    QuillenSpan.EndpointIso S T eX eY :=
  QuillenQ.endpointIsoOfMkHomNaturality S T eX eY h

example (e : QuillenSpan.EndpointIso S T eX eY) :
    e.1.hom ≫ T.l = S.l ≫ eX.hom :=
  e.hom_l

example (e : QuillenSpan.EndpointIso S T eX eY) :
    e.1.hom ≫ T.r = S.r ≫ eY.hom :=
  e.hom_r

example (e : QuillenSpan.EndpointIso S T eX eY) :
    e.1.inv ≫ S.l = T.l ≫ eX.inv :=
  e.inv_l

example (e : QuillenSpan.EndpointIso S T eX eY) :
    e.1.inv ≫ S.r = T.r ≫ eY.inv :=
  e.inv_r

example (e : QuillenSpan.EndpointIso S T eX eY) :
    QuillenSpan.EndpointIso T S eX.symm eY.symm :=
  e.symm

example (e : QuillenSpan.EndpointIso S T eX eY)
    (f : QuillenSpan.EndpointIso T U fX fY) :
    QuillenSpan.EndpointIso S U (eX.trans fX) (eY.trans fY) :=
  e.trans f

example (e f : QuillenSpan.EndpointIso S T eX eY) : e = f :=
  e.unique f

end PublicApi

section IdentityInverseAndRoundTrip

variable {X Y X' Y' : C}
variable (S : QuillenSpan X Y) (T : QuillenSpan X' Y')
variable (eX : X ≅ X') (eY : Y ≅ Y')

private theorem refl_naturality :
    QuillenQ.mkHom S ≫
        (QuillenQ.underlyingIso (Iso.refl Y)).hom =
      (QuillenQ.underlyingIso (Iso.refl X)).hom ≫
        QuillenQ.mkHom S := by
  apply QuillenQ.mkHom_naturality_of_span_iso
    S S (Iso.refl X) (Iso.refl Y) (Iso.refl S.apex)
  · simp
  · simp

/-- On a repeated span with identity endpoints, uniqueness identifies the
selected converse witness with the reflexive endpoint comparison. -/
example :
    QuillenQ.endpointIsoOfMkHomNaturality S S
        (Iso.refl X) (Iso.refl Y) (refl_naturality S) =
      QuillenSpan.EndpointIso.refl S :=
  QuillenSpan.EndpointIso.unique _ _

private theorem forward_naturality
    (e : QuillenSpan.EndpointIso S T eX eY) :
    QuillenQ.mkHom S ≫ (QuillenQ.underlyingIso eY).hom =
      (QuillenQ.underlyingIso eX).hom ≫ QuillenQ.mkHom T :=
  QuillenQ.mkHom_naturality_of_span_iso
    S T eX eY e.1 e.hom_l e.hom_r

/-- Forward naturality followed by the converse recovers the supplied unique
endpoint comparison. -/
example (e : QuillenSpan.EndpointIso S T eX eY) :
    QuillenQ.endpointIsoOfMkHomNaturality S T eX eY
        (forward_naturality S T eX eY e) = e :=
  QuillenSpan.EndpointIso.unique _ _

example (e : QuillenSpan.EndpointIso S T eX eY) :
    (e.symm).1.hom = e.1.inv :=
  rfl

example (e : QuillenSpan.EndpointIso S T eX eY) :
    (e.symm).1.inv = e.1.hom :=
  rfl

end IdentityInverseAndRoundTrip

section Composition

variable {X X' X'' Y Y' Y'' : C}
variable {S : QuillenSpan X Y} {T : QuillenSpan X' Y'}
  {U : QuillenSpan X'' Y''}
variable {eX : X ≅ X'} {eY : Y ≅ Y'}
  {fX : X' ≅ X''} {fY : Y' ≅ Y''}

example (e : QuillenSpan.EndpointIso S T eX eY)
    (f : QuillenSpan.EndpointIso T U fX fY) :
    (e.trans f).1.hom = e.1.hom ≫ f.1.hom :=
  rfl

example (e : QuillenSpan.EndpointIso S T eX eY)
    (f : QuillenSpan.EndpointIso T U fX fY) :
    (e.trans f).1.inv = f.1.inv ≫ e.1.inv :=
  rfl

end Composition

section TypeZero

variable {C₀ : Type} [Category C₀] [Preadditive C₀]
  [HasZeroObject C₀] [HasBinaryBiproducts C₀] [ExactCategory C₀]

example {X X' Y Y' : C₀}
    (S : QuillenSpan X Y) (T : QuillenSpan X' Y')
    (eX : X ≅ X') (eY : Y ≅ Y')
    (h : QuillenQ.mkHom S ≫ (QuillenQ.underlyingIso eY).hom =
      (QuillenQ.underlyingIso eX).hom ≫ QuillenQ.mkHom T) :
    Nonempty (QuillenSpan.EndpointIso S T eX eY) :=
  QuillenQ.endpointIso_nonempty_of_mkHom_naturality S T eX eY h

end TypeZero

section TypeOne

variable {C₁ : Type 1} [Category.{1} C₁] [Preadditive C₁]
  [HasZeroObject C₁] [HasBinaryBiproducts C₁] [ExactCategory C₁]

example {X X' Y Y' : C₁}
    (S : QuillenSpan X Y) (T : QuillenSpan X' Y')
    (eX : X ≅ X') (eY : Y ≅ Y')
    (h : QuillenQ.mkHom S ≫ (QuillenQ.underlyingIso eY).hom =
      (QuillenQ.underlyingIso eX).hom ≫ QuillenQ.mkHom T) :
    Nonempty (QuillenSpan.EndpointIso S T eX eY) :=
  QuillenQ.endpointIso_nonempty_of_mkHom_naturality S T eX eY h

end TypeOne

section MixedUniverses

variable {C₀₁ : Type} [Category.{1} C₀₁] [Preadditive C₀₁]
  [HasZeroObject C₀₁] [HasBinaryBiproducts C₀₁] [ExactCategory C₀₁]
variable {C₁₀ : Type 1} [Category.{0} C₁₀] [Preadditive C₁₀]
  [HasZeroObject C₁₀] [HasBinaryBiproducts C₁₀] [ExactCategory C₁₀]

example {X X' Y Y' : C₀₁}
    (S : QuillenSpan X Y) (T : QuillenSpan X' Y')
    (eX : X ≅ X') (eY : Y ≅ Y')
    (h : QuillenQ.mkHom S ≫ (QuillenQ.underlyingIso eY).hom =
      (QuillenQ.underlyingIso eX).hom ≫ QuillenQ.mkHom T) :
    Nonempty (QuillenSpan.EndpointIso S T eX eY) :=
  QuillenQ.endpointIso_nonempty_of_mkHom_naturality S T eX eY h

example {X X' Y Y' : C₁₀}
    (S : QuillenSpan X Y) (T : QuillenSpan X' Y')
    (eX : X ≅ X') (eY : Y ≅ Y')
    (h : QuillenQ.mkHom S ≫ (QuillenQ.underlyingIso eY).hom =
      (QuillenQ.underlyingIso eX).hom ≫ QuillenQ.mkHom T) :
    Nonempty (QuillenSpan.EndpointIso S T eX eY) :=
  QuillenQ.endpointIso_nonempty_of_mkHom_naturality S T eX eY h

end MixedUniverses

section DegreeTwoShell

local instance degreeTwoShellWaldhausenCategory :
    WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

/-- The converse applies directly to interval spans cut from degree-two
edgewise data, i.e. degree-five Stages and indices in `Fin 3`. -/
example (A B : Stage C 5) (k l : Fin 3) (hkl : k ≤ l)
    (eX :
      (edgewiseStageShellPacketNat (n := 2) A k l hkl).source ≅
        (edgewiseStageShellPacketNat (n := 2) B k l hkl).source)
    (eY :
      (edgewiseStageShellPacketNat (n := 2) A k l hkl).target ≅
        (edgewiseStageShellPacketNat (n := 2) B k l hkl).target)
    (h :
      QuillenQ.mkHom
            (edgewiseStageShellPacketNat (n := 2) A k l hkl).span ≫
          (QuillenQ.underlyingIso eY).hom =
        (QuillenQ.underlyingIso eX).hom ≫
          QuillenQ.mkHom
            (edgewiseStageShellPacketNat (n := 2) B k l hkl).span) :
    Nonempty (QuillenSpan.EndpointIso
      (edgewiseStageShellPacketNat (n := 2) A k l hkl).span
      (edgewiseStageShellPacketNat (n := 2) B k l hkl).span
      eX eY) :=
  QuillenQ.endpointIso_nonempty_of_mkHom_naturality _ _ eX eY h

end DegreeTwoShell

#print axioms AlgebraicKTheory.QuillenQ.endpointIso_nonempty_of_mkHom_naturality
#print axioms AlgebraicKTheory.QuillenQ.endpointIsoOfMkHomNaturality

end MathlibExtTest.KTheory.Categorical.QuillenSpanEndpointNaturalityTests

end
