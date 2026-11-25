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


public import MathlibExt.Algebra.Homology.FirstQuadrantTotalQuasiIso

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

variable {B B' : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)} (φ : B ⟶ B')
  (hφ : ∀ p : ℕ, QuasiIso (φ.f p))

/-! ## Finite stages and full total -/

example (p : ℕ) : QuasiIso (B.partialTotalHom φ p) :=
  quasiIso_partialTotalHom_of_objwise φ hφ p

example : QuasiIso (B.partialTotalHom φ 0) :=
  quasiIso_partialTotalHom_of_objwise φ hφ 0

example : QuasiIso (B.partialTotalHom φ 1) :=
  quasiIso_partialTotalHom_of_objwise φ hφ 1

example :
    QuasiIso (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) :=
  quasiIso_totalMap_of_objwise_firstQuadrant φ hφ

example : IsIso (HomologicalComplex.homologyMap
    (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) 0) := by
  let _ : QuasiIso
      (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) :=
    quasiIso_totalMap_of_objwise_firstQuadrant φ hφ
  infer_instance

example : IsIso (HomologicalComplex.homologyMap
    (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) 1) := by
  let _ : QuasiIso
      (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)) :=
    quasiIso_totalMap_of_objwise_firstQuadrant φ hφ
  infer_instance

/-! The rowwise hypothesis does not require objectwise component
isomorphisms. -/

example (p q : ℕ) (_hnot : ¬ IsIso ((φ.f p).f q)) :
    QuasiIso (B.partialTotalHom φ p) :=
  quasiIso_partialTotalHom_of_objwise φ hφ p

/-! ## Identity and zero bicomplexes -/

example (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) (p : ℕ) :
    QuasiIso (B.partialTotalHom (𝟙 B) p) := by
  apply quasiIso_partialTotalHom_of_objwise
  intro i
  change QuasiIso (𝟙 (B.X i))
  infer_instance

example (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)) :
    QuasiIso
      (HomologicalComplex₂.total.map (𝟙 B) (ComplexShape.down ℕ)) := by
  apply quasiIso_totalMap_of_objwise_firstQuadrant
  intro i
  change QuasiIso (𝟙 (B.X i))
  infer_instance

example :
    let Z : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) := HomologicalComplex.zero
    QuasiIso
      (HomologicalComplex₂.total.map (𝟙 Z) (ComplexShape.down ℕ)) := by
  dsimp only
  apply quasiIso_totalMap_of_objwise_firstQuadrant
  intro i
  change QuasiIso (𝟙 _)
  infer_instance

/-! ## Naturality and a literal finite diagonal -/

example (p : ℕ) :
    B.partialTotalHom φ p ≫ B'.partialTotalι p =
      B.partialTotalι p ≫
        HomologicalComplex₂.total.map φ (ComplexShape.down ℕ) :=
  B.partialTotalHom_ι_naturality φ p

example (i j n : ℕ) (h : i + j = n) :
    B.ιTotal (ComplexShape.down ℕ) i j n h ≫
        (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)).f n =
      (φ.f i).f j ≫ B'.ιTotal (ComplexShape.down ℕ) i j n h :=
  HomologicalComplex₂.ιTotal_map B B' φ
    (ComplexShape.down ℕ) i j n h

example :
    B.ιTotal (ComplexShape.down ℕ) 0 0 0 rfl ≫
        (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ)).f 0 =
      (φ.f 0).f 0 ≫ B'.ιTotal (ComplexShape.down ℕ) 0 0 0 rfl :=
  HomologicalComplex₂.ιTotal_map B B' φ
    (ComplexShape.down ℕ) 0 0 0 rfl

end HomologicalComplex₂

end
