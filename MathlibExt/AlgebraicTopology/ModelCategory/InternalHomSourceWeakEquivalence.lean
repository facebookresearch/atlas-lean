/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.Monoidal
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown

import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Weak invariance of internal Homs in the source

In a symmetric monoidal closed category, fixing the target of the internal
Hom gives a right adjoint from the opposite category.  In a closed symmetric
monoidal model category, Quillen--Brown therefore makes precomposition by a
weak equivalence between cofibrant sources weak against a fibrant target.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MorphismProperty

namespace CategoryTheory.MonoidalClosed

variable {C : Type u} [Category.{v} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]

/-- For a fixed target, the source-variable internal Hom is right adjoint to
its right-opposite functor. -/
noncomputable def internalHomSourceAdjunction (Z : C) :
    (MonoidalClosed.internalHom.flip.obj Z).rightOp ⊣
      MonoidalClosed.internalHom.flip.obj Z := by
  let H := MonoidalClosed.internalHom.flip.obj Z
  let L := H.rightOp
  let dualHomEquiv (A : C) (B : Cᵒᵖ) :
      (L.obj A ⟶ B) ≃ (A ⟶ H.obj B) :=
    { toFun := fun k ↦ MonoidalClosed.curry
        ((β_ B.unop A).hom ≫ MonoidalClosed.uncurry k.unop)
      invFun := fun l ↦ (MonoidalClosed.curry
        ((β_ A B.unop).hom ≫ MonoidalClosed.uncurry l)).op
      left_inv := fun k ↦ by
        set_option backward.isDefEq.respectTransparency false in
          apply Quiver.Hom.unop_inj
          dsimp
          rw [MonoidalClosed.uncurry_curry, ← Category.assoc,
            SymmetricCategory.symmetry, Category.id_comp,
            MonoidalClosed.curry_uncurry]
      right_inv := fun l ↦ by
        set_option backward.isDefEq.respectTransparency false in
          dsimp
          rw [MonoidalClosed.uncurry_curry, ← Category.assoc,
            SymmetricCategory.symmetry, Category.id_comp,
            MonoidalClosed.curry_uncurry] }
  exact Adjunction.mkOfHomEquiv
    { homEquiv := dualHomEquiv
      homEquiv_naturality_left_symm := by
        intro A' A B a l
        set_option backward.isDefEq.respectTransparency false in
          apply Quiver.Hom.unop_inj
          dsimp [dualHomEquiv, L, H]
          change MonoidalClosed.curry
              ((β_ A' B.unop).hom ≫ MonoidalClosed.uncurry (a ≫ l)) =
            MonoidalClosed.curry
                ((β_ A B.unop).hom ≫ MonoidalClosed.uncurry l) ≫
              (MonoidalClosed.pre a).app Z
          rw [MonoidalClosed.curry_pre_app]
          apply MonoidalClosed.uncurry_injective
          rw [MonoidalClosed.uncurry_curry,
            MonoidalClosed.uncurry_natural_left,
            MonoidalClosed.uncurry_curry,
            BraidedCategory.braiding_naturality_left_assoc]
      homEquiv_naturality_right := by
        intro A B B' k b
        set_option backward.isDefEq.respectTransparency false in
          dsimp [dualHomEquiv, L, H]
          change MonoidalClosed.curry
              ((β_ B'.unop A).hom ≫
                MonoidalClosed.uncurry (b.unop ≫ k.unop)) =
            MonoidalClosed.curry
                ((β_ B.unop A).hom ≫ MonoidalClosed.uncurry k.unop) ≫
              (MonoidalClosed.pre b.unop).app Z
          rw [MonoidalClosed.curry_pre_app]
          apply MonoidalClosed.uncurry_injective
          rw [MonoidalClosed.uncurry_curry,
            MonoidalClosed.uncurry_natural_left,
            MonoidalClosed.uncurry_curry,
            BraidedCategory.braiding_naturality_left_assoc] }

end CategoryTheory.MonoidalClosed

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]

private theorem internalHomSource_pullbackHomClauses :
    PullbackHomLe (cofibrations C) (trivialFibrations C)
        (trivialFibrations C) ∧
      PullbackHomLe (trivialCofibrations C) (fibrations C)
          (trivialFibrations C) ∧
        PullbackHomLe (cofibrations C) (fibrations C)
          (fibrations C) := by
  refine ⟨?_, ?_, ?_⟩
  · have hpp : PushoutProductLe (cofibrations C) (cofibrations C)
        (trivialFibrations C).llp := by
      rw [trivialFibrations_llp (C := C)]
      exact
        IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct
          (C := C)
    have h := (pushoutProduct_le_llp_iff_pullbackHom_le_rlp
      (cofibrations C) (cofibrations C) (trivialFibrations C)).mp hpp
    rwa [cofibrations_rlp (C := C)] at h
  · have hpp : PushoutProductLe (trivialCofibrations C) (cofibrations C)
        (fibrations C).llp := by
      rw [fibrations_llp (C := C)]
      exact
        IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left
          (C := C)
    have h := (pushoutProduct_le_llp_iff_pullbackHom_le_rlp
      (trivialCofibrations C) (cofibrations C) (fibrations C)).mp hpp
    rwa [cofibrations_rlp (C := C)] at h
  · have hpp : PushoutProductLe (cofibrations C) (trivialCofibrations C)
        (fibrations C).llp := by
      rw [fibrations_llp (C := C)]
      exact
        IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_right
          (C := C)
    have h := (pushoutProduct_le_llp_iff_pullbackHom_le_rlp
      (cofibrations C) (trivialCofibrations C) (fibrations C)).mp hpp
    rwa [trivialCofibrations_rlp (C := C)] at h

private theorem internalHomSourceAdjunction_isQuillen
    (Z : C) [IsFibrant Z] :
    Adjunction.IsQuillenAdjunction
      (MonoidalClosed.internalHomSourceAdjunction Z) := by
  exact
    { preservesCofibrations := by
        intro A B i hi
        rw [cofibrations_op]
        change fibrations C ((MonoidalClosed.pre i).app Z)
        have hpb := internalHomSource_pullbackHomClauses.2.2
          i (terminal.from Z) hi
          ((HomotopicalAlgebra.fibration_iff _).mp
            (show IsFibrant Z from inferInstance))
        let e := MonoidalCategory.Arrow.PullbackHom.isTerminalIso
          (Arrow.mk i) terminalIsTerminal (W := Z)
        exact ((fibrations C).arrow_mk_iso_iff e).mp hpb
      preservesTrivialCofibrations := by
        intro A B i hi
        rw [trivialCofibrations_op]
        change trivialFibrations C ((MonoidalClosed.pre i).app Z)
        have hpb := internalHomSource_pullbackHomClauses.2.1
          i (terminal.from Z) hi
          ((HomotopicalAlgebra.fibration_iff _).mp
            (show IsFibrant Z from inferInstance))
        let e := MonoidalCategory.Arrow.PullbackHom.isTerminalIso
          (Arrow.mk i) terminalIsTerminal (W := Z)
        exact ((trivialFibrations C).arrow_mk_iso_iff e).mp hpb }

/-- Precomposition by a weak equivalence between cofibrant sources is weak
against a fibrant internal-Hom target. -/
theorem weakEquivalence_pre_app_of_cofibrant
    {A B Z : C} (i : A ⟶ B)
    [IsCofibrant A] [IsCofibrant B] [IsFibrant Z]
    (hi : WeakEquivalence i) :
    WeakEquivalence ((MonoidalClosed.pre i).app Z) := by
  let _ : WeakEquivalence i := hi
  let H := MonoidalClosed.internalHom.flip.obj Z
  let L := H.rightOp
  let adj := MonoidalClosed.internalHomSourceAdjunction Z
  let _ : Adjunction.IsQuillenAdjunction adj :=
    internalHomSourceAdjunction_isQuillen Z
  have hop : WeakEquivalence (L.map i) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := adj) i
  exact
    (weakEquivalences_op_iff ((MonoidalClosed.pre i).app Z)).mp
      (by simpa [L, H, MonoidalClosed.internalHom] using hop)

end HomotopicalAlgebra
