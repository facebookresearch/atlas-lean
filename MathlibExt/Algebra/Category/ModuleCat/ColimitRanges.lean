/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Actual source ranges span a module colimit

Quotient by the sum of the original source images. Every original colimit
leg is killed by this quotient, so the actual colimit universal property
makes the quotient map zero and its kernel is the whole module.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

universe u v uJ vJ

variable {R : Type u} [Ring R] {J : Type uJ} [Category.{vJ} J]
  {D : J ⥤ ModuleCat.{v} R} {c : Cocone D}

/-- Retain the original colimit target as the actual codomain of each original module leg. -/
abbrev colimitLegLinearMap (c : Cocone D) (j : J) : D.obj j →ₗ[R] c.pt := (c.ι.app j).hom

/-- The actual colimit module is spanned by the original leg ranges, with no dimension bound. -/
lemma IsColimit.iSup_range_eq_top (h : IsColimit c) :
    (⨆ j : J, LinearMap.range (colimitLegLinearMap c j)) = ⊤ := by
  let S : Submodule R c.pt := ⨆ j : J, LinearMap.range (colimitLegLinearMap c j)
  let Q := ModuleCat.of R (c.pt ⧸ S)
  let q : c.pt ⟶ Q := ModuleCat.ofHom S.mkQ
  have hq : q = 0 := h.hom_ext (fun j => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change S.mkQ ((c.ι.app j).hom x) = 0
    exact (Submodule.Quotient.mk_eq_zero S).2
      ((le_iSup (fun k : J => LinearMap.range (colimitLegLinearMap c k)) j) ⟨x, rfl⟩))
  apply top_unique
  intro x _
  have hx : S.mkQ x = 0 := by
    have e := congrArg (fun f : c.pt ⟶ Q => f.hom x) hq
    exact e
  exact (Submodule.Quotient.mk_eq_zero S).1 hx

end ModuleCat
