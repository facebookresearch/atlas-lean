/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Andres Barei Bueno
-/
module

public import MathlibExt.CategoryTheory.Semisimple

@[expose] public section

namespace MathlibExtTest.CategoryTheory.Semisimple

open MetaMathlibExt

-- Algebra 470: Semisimple object in a category

theorem semisimple_from_simple.{u,v} {C : Type u} [CategoryTheory.Category.{v} C]
  [CategoryTheory.Limits.HasZeroMorphisms C] (S : C) :
  CategoryTheory.Simple S → Semisimple S := by
    intro hyp
    constructor
    use Fin 1
    use fun _ => S
    use inferInstance
    constructor
    · intro
      exact hyp
    · exact ⟨(CategoryTheory.Limits.biproductUniqueIso
        (fun _ : Fin 1 => S)).symm⟩

-- Algebra 476: (Object) Semisimple category

theorem semisimple_contains_simples.{u,v} {C : Type u} [CategoryTheory.Category.{v} C]
  [CategoryTheory.Limits.HasZeroMorphisms C] [SemisimpleCategory C] :
  (∃ X Y : C, IsEmpty (X ≅ Y)) → (∃ S : C, CategoryTheory.Simple S)
  := by
    intro hyp
    rcases hyp with ⟨X,Y,hXY⟩
    have hX : Semisimple X := SemisimpleCategory.semisimple X
    have hY : Semisimple Y := SemisimpleCategory.semisimple Y
    rcases hX with ⟨⟨IX, SX, hBipX, hSimpleX, hIsoX⟩⟩
    rcases hY with ⟨⟨IY, SY, hBipY, hSimpleY, hIsoY⟩⟩
    by_cases hIX : Nonempty IX
    · rcases hIX with ⟨i⟩
      exact ⟨SX i, hSimpleX i⟩
    · by_cases hIY : Nonempty IY
      · rcases hIY with ⟨i⟩
        exact ⟨SY i, hSimpleY i⟩
      · rw [not_nonempty_iff] at hIX
        rw [not_nonempty_iff] at hIY
        let _ : IsEmpty IX := hIX
        let _ : IsEmpty IY := hIY
        let _ : CategoryTheory.Limits.HasBiproduct SX := hBipX
        let _ : CategoryTheory.Limits.HasBiproduct SY := hBipY
        let e : IX ≃ IY :=
          { toFun := fun i => isEmptyElim i
            invFun := fun i => isEmptyElim i
            left_inv := fun i => isEmptyElim i
            right_inv := fun i => isEmptyElim i }
        let eBip : (⨁ SX) ≅ (⨁ SY) :=
          CategoryTheory.Limits.biproduct.whiskerEquiv e (fun i => isEmptyElim i)
        rcases hIsoX with ⟨eX⟩
        rcases hIsoY with ⟨eY⟩
        exact (hXY.false (eX.trans (eBip.trans eY.symm))).elim

end MathlibExtTest.CategoryTheory.Semisimple

end
