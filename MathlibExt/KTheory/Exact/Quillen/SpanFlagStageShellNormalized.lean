/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.KTheory.Exact.Quillen.SpanFlagStageShellFunctor

/-!
# Endpoint-normalized representatives of Quillen Stage shells

The raw span extracted from an edgewise Stage shell has endpoints that are
propositionally equal to the fixed cross vertices.  This file transports both
legs along those endpoint equalities, producing a raw admissible span between
the literal cross vertices.  Its class in the Quillen Q-construction is the
existing normalized shell class.

This is only a representative-level adapter for the forward shell
construction.  It chooses no Stage grid or lift and makes no fiber,
contractibility, bar-construction, or Q/S comparison claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance spanFlagStageShellNormalizedWaldhausenC :
    WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

/-- The raw shell span with both legs postcomposed by the canonical endpoint
equality isomorphisms to the fixed cross vertices. -/
noncomputable def edgewiseStageShellSpanNormalized {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    QuillenSpan (edgewiseStageVertex A k) (edgewiseStageVertex A l) := by
  let S := (edgewiseStageShellPacket A k l hkl).span
  let eX := eqToIso (edgewiseStageShellSourceEqVertex A k l hkl)
  let eY := eqToIso (edgewiseStageShellTargetEqVertex A k l hkl)
  exact
    { apex := S.apex
      l := S.l ≫ eX.hom
      r := S.r ≫ eY.hom
      wl := admissibleEpi_comp.comp_mem _ _ S.wl
        (IsAdmissibleEpi.of_isIso eX.hom)
      wr := admissibleMono_comp.comp_mem _ _ S.wr
        (IsAdmissibleMono.of_isIso eY.hom) }

@[simp]
theorem edgewiseStageShellSpanNormalized_apex {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (edgewiseStageShellSpanNormalized A k l hkl).apex =
      (edgewiseStageShellPacket A k l hkl).span.apex :=
  rfl

@[simp]
theorem edgewiseStageShellSpanNormalized_l {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (edgewiseStageShellSpanNormalized A k l hkl).l =
      (edgewiseStageShellPacket A k l hkl).span.l ≫
        (eqToIso (edgewiseStageShellSourceEqVertex A k l hkl)).hom :=
  rfl

@[simp]
theorem edgewiseStageShellSpanNormalized_r {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    (edgewiseStageShellSpanNormalized A k l hkl).r =
      (edgewiseStageShellPacket A k l hkl).span.r ≫
        (eqToIso (edgewiseStageShellTargetEqVertex A k l hkl)).hom :=
  rfl

/-- The endpoint-normalized raw shell represents the existing normalized
shell class in the Quillen Q-construction. -/
theorem edgewiseStageShellSpanNormalized_mkHom {a : SimplexCategory}
    (A : Stage C (edgewiseQ.obj a).len)
    (k l : Fin (a.len + 1)) (hkl : k ≤ l) :
    QuillenQ.mkHom (edgewiseStageShellSpanNormalized A k l hkl) =
      edgewiseStageShellClassNormalized A k l hkl := by
  let S := (edgewiseStageShellPacket A k l hkl).span
  let T := edgewiseStageShellSpanNormalized A k l hkl
  let eX := eqToIso (edgewiseStageShellSourceEqVertex A k l hkl)
  let eY := eqToIso (edgewiseStageShellTargetEqVertex A k l hkl)
  have h := QuillenQ.mkHom_naturality_of_span_iso S T eX eY
    (Iso.refl S.apex)
    (by simp [S, T, eX, edgewiseStageShellSpanNormalized])
    (by simp [S, T, eY, edgewiseStageShellSpanNormalized])
  change QuillenQ.mkHom T =
    (QuillenQ.underlyingIso eX).inv ≫ QuillenQ.mkHom S ≫
      (QuillenQ.underlyingIso eY).hom
  rw [h, Iso.inv_hom_id_assoc]
  rfl

end AlgebraicKTheory

end
