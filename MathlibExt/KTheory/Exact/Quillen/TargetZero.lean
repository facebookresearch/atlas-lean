/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.KTheory.Exact.Quillen.UnderlyingIso

/-!
# Morphisms into zero objects in the Quillen Q-construction

A morphism in `QuillenQ C` whose target is represented by a zero object is
necessarily an isomorphism.  For a representative span `X ←↞ M ↪ Z`, the
admissible-mono right leg makes `M` zero, and the admissible-epi left leg then
makes `X` zero.  Both legs are therefore invertible, so the span is isomorphic
to the forward span of the induced underlying isomorphism `X ≅ Z`.

The orientation is essential.  Morphisms *from* a zero object need not be
invertible: the canonical zero-to-object Quillen morphism exists for every
object.  This file makes no terminal-object, comma-category, localization,
realization, or Q/S comparison claim.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits
open CategoryTheory.ExactCategory

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

set_option linter.style.haveILetI false in
/-- Every Quillen-Q morphism into an object represented by a zero object is
an isomorphism. -/
theorem QuillenQ.isIso_of_target_isZero
    {X Z : C} (f : (⟨X⟩ : QuillenQ C) ⟶ (⟨Z⟩ : QuillenQ C))
    (hZ : IsZero Z) : IsIso f := by
  obtain ⟨S, hS⟩ := Quotient.exists_rep f
  change QuillenQ.mkHom S = f at hS
  letI : Mono S.r := IsAdmissibleMono.mono S.wr
  have hApex : IsZero S.apex := IsZero.of_mono S.r hZ
  letI : Epi S.l := IsAdmissibleEpi.epi S.wl
  have hX : IsZero X := IsZero.of_epi S.l hApex
  letI : IsIso S.l := IsZero.isIso hApex hX S.l
  letI : IsIso S.r := IsZero.isIso hApex hZ S.r
  let e : X ≅ Z := (asIso S.l).symm.trans (asIso S.r)
  have hUnderlying : QuillenQ.mkHom S = (QuillenQ.underlyingIso e).hom := by
    rw [QuillenQ.underlyingIso_hom]
    apply QuillenQ.mkHom_sound
    refine Span.mkIso (asIso S.l) ?_ ?_
    · simp
    · change S.l ≫ e.hom = S.r
      simp [e]
  rw [← hS, hUnderlying]
  infer_instance

/-- Original Quillen arrows into an underlying zero object are unique
under the standard exact-category assumptions. -/
theorem QuillenQ.hom_eq_of_target_isZero {X Z : C}
    (f g : (⟨X⟩ : QuillenQ C) ⟶ (⟨Z⟩ : QuillenQ C)) (hZ : IsZero Z) : f = g := by
  obtain ⟨S, hS⟩ := Quotient.exists_rep f
  obtain ⟨T, hT⟩ := Quotient.exists_rep g
  change QuillenQ.mkHom S = f at hS
  change QuillenQ.mkHom T = g at hT
  let _ : Epi S.l := (show IsAdmissibleEpi S.l from S.wl).epi
  let _ : Mono S.r := (show IsAdmissibleMono S.r from S.wr).mono
  let _ : Mono T.r := (show IsAdmissibleMono T.r from T.wr).mono
  have hA : IsZero S.apex := IsZero.of_mono S.r hZ
  have hB : IsZero T.apex := IsZero.of_mono T.r hZ
  have hX : IsZero X := IsZero.of_epi S.l hA
  have hST : QuillenQ.mkHom S = QuillenQ.mkHom T := by
    apply QuillenQ.mkHom_sound
    exact Span.mkIso (hA.iso hB) (hX.eq_of_tgt _ _) (hZ.eq_of_tgt _ _)
  exact hS.symm.trans (hST.trans hT)

end AlgebraicKTheory

end
