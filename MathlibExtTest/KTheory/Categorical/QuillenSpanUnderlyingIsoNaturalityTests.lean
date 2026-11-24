/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.KTheory.Exact.Quillen.SpanUnderlyingIsoNaturality

/-!
# Span endpoint-isomorphism naturality tests

These tests pin the generic naturality square and its identity and transitive
isomorphism specializations.  They contain no Stage-grid or all-degree lift
claim.
-/

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v u

namespace MathlibExtTest.KTheory.Categorical
namespace QuillenSpanUnderlyingIsoNaturalityTests

open AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

example {X X' Y Y' : C}
    (S : QuillenSpan X Y) (T : QuillenSpan X' Y')
    (eX : X ≅ X') (eY : Y ≅ Y') (eA : S.apex ≅ T.apex)
    (hl : eA.hom ≫ T.l = S.l ≫ eX.hom)
    (hr : eA.hom ≫ T.r = S.r ≫ eY.hom) :
    QuillenQ.mkHom S ≫ (QuillenQ.underlyingIso eY).hom =
      (QuillenQ.underlyingIso eX).hom ≫ QuillenQ.mkHom T :=
  QuillenQ.mkHom_naturality_of_span_iso S T eX eY eA hl hr

/-- Identity endpoint and apex isomorphisms recover the tautological square. -/
example {X Y : C} (S : QuillenSpan X Y) :
    QuillenQ.mkHom S ≫
        (QuillenQ.underlyingIso (Iso.refl Y)).hom =
      (QuillenQ.underlyingIso (Iso.refl X)).hom ≫
        QuillenQ.mkHom S := by
  apply QuillenQ.mkHom_naturality_of_span_iso
    S S (Iso.refl X) (Iso.refl Y) (Iso.refl S.apex)
  · simp
  · simp

/-- Compatible span isomorphism data compose transitively. -/
example {X X' X'' Y Y' Y'' : C}
    (S : QuillenSpan X Y) (T : QuillenSpan X' Y')
    (U : QuillenSpan X'' Y'')
    (eX : X ≅ X') (fX : X' ≅ X'')
    (eY : Y ≅ Y') (fY : Y' ≅ Y'')
    (eA : S.apex ≅ T.apex) (fA : T.apex ≅ U.apex)
    (hl₁ : eA.hom ≫ T.l = S.l ≫ eX.hom)
    (hr₁ : eA.hom ≫ T.r = S.r ≫ eY.hom)
    (hl₂ : fA.hom ≫ U.l = T.l ≫ fX.hom)
    (hr₂ : fA.hom ≫ U.r = T.r ≫ fY.hom) :
    QuillenQ.mkHom S ≫
        (QuillenQ.underlyingIso (eY.trans fY)).hom =
      (QuillenQ.underlyingIso (eX.trans fX)).hom ≫
        QuillenQ.mkHom U := by
  apply QuillenQ.mkHom_naturality_of_span_iso
    S U (eX.trans fX) (eY.trans fY) (eA.trans fA)
  · calc
      (eA.trans fA).hom ≫ U.l =
          eA.hom ≫ (fA.hom ≫ U.l) := by simp
      _ = eA.hom ≫ (T.l ≫ fX.hom) := by rw [hl₂]
      _ = (eA.hom ≫ T.l) ≫ fX.hom := by rw [Category.assoc]
      _ = (S.l ≫ eX.hom) ≫ fX.hom := by rw [hl₁]
      _ = S.l ≫ (eX.trans fX).hom := by simp
  · calc
      (eA.trans fA).hom ≫ U.r =
          eA.hom ≫ (fA.hom ≫ U.r) := by simp
      _ = eA.hom ≫ (T.r ≫ fY.hom) := by rw [hr₂]
      _ = (eA.hom ≫ T.r) ≫ fY.hom := by rw [Category.assoc]
      _ = (S.r ≫ eY.hom) ≫ fY.hom := by rw [hr₁]
      _ = S.r ≫ (eY.trans fY).hom := by simp

end QuillenSpanUnderlyingIsoNaturalityTests
end MathlibExtTest.KTheory.Categorical

end
