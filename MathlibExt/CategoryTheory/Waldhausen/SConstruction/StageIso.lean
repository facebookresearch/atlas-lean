/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.FiniteStage
public import Mathlib.CategoryTheory.NatIso

/-!
# Finite Waldhausen stages transported by a whole natural isomorphism

The actual diagonal zero objects and every original cofiber triple
transport along a whole natural isomorphism. Cofibrations use the
original Waldhausen morphism property; each chosen-zero pushout uses
the actual three isomorphism components and identity on the zero.
-/

public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe u v

namespace CategoryTheory.Waldhausen.SConstruction

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Every finite Waldhausen stage transports along an actual whole
natural isomorphism, with all non-strict triples and original maps. -/
theorem IsStage.of_natIso {n : ℕ} {A B : Ar n ⥤ C}
    (hA : IsStage n A) (e : A ≅ B) : IsStage n B := by
  refine { diag_isZero := ?_, cofiber_triple := ?_ }
  · intro i
    exact IsZero.of_iso (hA.diag_isZero i) (e.symm.app (diag i))
  · intro i j k hij hjk
    obtain ⟨hi, h, q, hPush⟩ := hA.cofiber_triple hij hjk
    let P := WaldhausenCategoryWithoutGluing.cofibrations (C := C)
    have hComp : P (e.hom.app (interval i j hij) ≫ B.map (horiz hij hjk)) := by
      rw [← e.hom.naturality (horiz hij hjk)]
      exact P.comp_mem _ _ hi (P.of_isIso _)
    have hB : IsCofibration (B.map (horiz hij hjk)) :=
      (P.cancel_left_of_respectsIso (e.hom.app (interval i j hij))
        (B.map (horiz hij hjk))).mp hComp
    let e₀ := e.app (interval i j hij)
    let e₁ := e.app (interval i k (hij.trans hjk))
    let e₂ := e.app (interval j k hjk)
    refine ⟨hB, e₀.inv ≫ h, q ≫ e₂.hom, ?_⟩
    apply hPush.of_iso e₀ (Iso.refl (0 : C)) e₁ e₂
    · simp only [Iso.refl_hom, Category.comp_id, Iso.hom_inv_id_assoc]
    · exact e.hom.naturality (horiz hij hjk)
    · simp only [Iso.refl_hom, Category.id_comp]
    · exact e.hom.naturality (vert hij hjk)

end CategoryTheory.Waldhausen.SConstruction

end
