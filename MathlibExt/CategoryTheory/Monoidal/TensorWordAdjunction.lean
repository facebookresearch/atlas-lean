/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.TensorWord
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Monad.Adjunction

/-!
# TensorWordAdjunction

The tensor-word free monoid adjunction, its induced monad, and the actual generator and multiplication maps.
-/

/- Source proof segment: TensorWordAdjunction -/
section source_TensorWordAdjunction
/-!
# The tensor-word free monoid adjunction

The tensor-word carrier and its full natural universal Hom equivalence
give the actual free/forgetful adjunction for unital monoid objects.
Its monad has word evaluation as multiplication. The degree-zero
summand is the tensor unit and evaluates to the monoid unit.

This is the tensor-word construction used for associative algebras.
The comparison with a symmetric associative operad is a separate result.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

namespace CategoryTheory.MonoidalCategory.TensorWord

open CategoryTheory Limits MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable [∀ (f : ℕ → C), HasCoproduct f]
variable [∀ (f : (Σ _ : ℕ, ℕ) → C), HasCoproduct f]
variable [∀ (M : C), PreservesColimitsOfShape (Discrete ℕ) (tensorLeft M)]
variable [∀ (T : C), PreservesColimitsOfShape (Discrete ℕ) (tensorRight T)]
variable [∀ (T : C),
  PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)]

/-- The tensor-word construction is left adjoint to the actual
forgetful functor from unital monoid objects. The Hom equivalence is
the extension/restriction equivalence of the tensor-word carrier. -/
def tensorWordAdjunction : tensorWordFunctor (C := C) ⊣ Mon.forget C :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X M => (tensorWordHomEquiv X M).symm
      homEquiv_naturality_left_symm := fun f g =>
        tensorWordHomEquiv_source f g
      homEquiv_naturality_right := fun f g => by
        change tensorWordGenerator _ ≫ (f.hom ≫ g.hom) =
          (tensorWordGenerator _ ≫ f.hom) ≫ g.hom
        exact (Category.assoc _ _ _).symm }

/-- The unit of the free monoid adjunction is the actual degree-one
word inclusion, prefaced by the ambient left unitor. -/
@[simp]
theorem tensorWordAdjunction_unit (X : C) :
    tensorWordAdjunction.unit.app X = tensorWordGenerator X := by
  change tensorWordGenerator X ≫ 𝟙 (tensorWordObj X) = tensorWordGenerator X
  exact Category.comp_id _

/-- The counit evaluates each tensor word using the original monoid's
unit and multiplication. -/
@[simp]
theorem tensorWordAdjunction_counit (M : Mon C) :
    tensorWordAdjunction.counit.app M = tensorWordLiftHom M (𝟙 M.X) :=
  rfl

/-- The induced tensor-word monad is obtained from the constructed
free/forgetful adjunction, with all three monad laws. -/
def tensorWordMonad : Monad C := tensorWordAdjunction.toMonad

/-- The monad carrier is the actual coproduct of every finite tensor
power, starting at degree zero. -/
@[simp]
theorem tensorWordMonad_obj (X : C) :
    tensorWordMonad.obj X = tensorWordObj X :=
  rfl

@[simp]
theorem tensorWordMonad_map {X Y : C} (f : X ⟶ Y) :
    tensorWordMonad.map f = tensorWordMap f :=
  rfl

@[simp]
theorem tensorWordMonad_unit (X : C) :
    tensorWordMonad.η.app X = tensorWordGenerator X :=
  tensorWordAdjunction_unit X

/-- Monad multiplication is the actual flattening of words of words
by the free word monoid's unit and multiplication. -/
@[simp]
theorem tensorWordMonad_multiplication (X : C) :
    tensorWordMonad.μ.app X =
      tensorWordLift (tensorWordMon X) (𝟙 (tensorWordObj X)) :=
  rfl

/-- The empty outer word evaluates to the actual degree-zero unit
summand of the target word monoid. -/
@[reassoc]
theorem tensorWordMonad_empty_word (X : C) :
    tensorWordι (tensorWordObj X) 0 ≫ tensorWordMonad.μ.app X =
      tensorWordOne X :=
  IsMonHom.one_hom (tensorWordAdjunction.counit.app (tensorWordMon X)).hom

/-- Flattening a singleton word returns its original word. -/
@[reassoc]
theorem tensorWordMonad_singleton_word (X : C) :
    tensorWordGenerator (tensorWordObj X) ≫ tensorWordMonad.μ.app X =
      𝟙 (tensorWordObj X) :=
  tensorWordLift_beta (tensorWordMon X) (𝟙 _)

/-- Flattening evaluates concatenation by concatenating the actual
target words. -/
@[reassoc]
theorem tensorWordMonad_concatenation (X : C) :
    tensorWordMul (tensorWordObj X) ≫ tensorWordMonad.μ.app X =
      (tensorWordMonad.μ.app X ⊗ₘ tensorWordMonad.μ.app X) ≫ tensorWordMul X :=
  IsMonHom.mul_hom (tensorWordAdjunction.counit.app (tensorWordMon X)).hom

/-- The left triangle equation of the free/forgetful adjunction,
written with the original tensor-word carrier maps. -/
theorem tensorWordAdjunction_left_triangle (X : C) :
    tensorWordMap (tensorWordGenerator X) ≫
        tensorWordLift (tensorWordMon X) (𝟙 (tensorWordObj X)) =
      𝟙 (tensorWordObj X) := by
  let m : tensorWordObj (tensorWordObj X) ⟶ tensorWordObj X :=
    tensorWordLift (tensorWordMon X) (𝟙 (tensorWordObj X))
  have hm : tensorWordGenerator (tensorWordObj X) ≫ m = 𝟙 (tensorWordObj X) :=
    tensorWordLift_beta (tensorWordMon X) (𝟙 (tensorWordObj X))
  let g : tensorWordMon X ⟶ tensorWordMon X :=
    tensorWordFunctor.map (tensorWordGenerator X) ≫
      tensorWordLiftHom (tensorWordMon X) (𝟙 (tensorWordObj X))
  have hg : tensorWordGenerator X ≫ g.hom = tensorWordGenerator X := by
    change tensorWordGenerator X ≫ (tensorWordMap (tensorWordGenerator X) ≫ m) =
      tensorWordGenerator X
    calc
      tensorWordGenerator X ≫ (tensorWordMap (tensorWordGenerator X) ≫ m) =
          (tensorWordGenerator X ≫ tensorWordMap (tensorWordGenerator X)) ≫ m :=
        (Category.assoc _ _ _).symm
      _ = (tensorWordGenerator X ≫ tensorWordGenerator (tensorWordObj X)) ≫ m :=
        congrArg (fun t : X ⟶ tensorWordObj (tensorWordObj X) => t ≫ m)
          (tensorWordGenerator_naturality (tensorWordGenerator X))
      _ = tensorWordGenerator X ≫ (tensorWordGenerator (tensorWordObj X) ≫ m) :=
        Category.assoc _ _ _
      _ = tensorWordGenerator X ≫ 𝟙 (tensorWordObj X) :=
        congrArg (tensorWordGenerator X ≫ ·) hm
      _ = tensorWordGenerator X := Category.comp_id _
  have hgi : g = 𝟙 (tensorWordMon X) :=
    (tensorWordLiftUnique (tensorWordGenerator X) g hg).trans
      (tensorWordLiftUnique (tensorWordGenerator X) (𝟙 (tensorWordMon X))
        (Category.comp_id _)).symm
  have h := congrArg Mon.Hom.hom hgi
  change tensorWordMap (tensorWordGenerator X) ≫
      tensorWordLift (tensorWordMon X) (𝟙 (tensorWordObj X)) =
    𝟙 (tensorWordObj X) at h
  exact h

omit [∀ (f : (Σ _ : ℕ, ℕ) → C), HasCoproduct f]
  [∀ (M : C), PreservesColimitsOfShape (Discrete ℕ) (tensorLeft M)]
  [∀ (T : C), PreservesColimitsOfShape (Discrete ℕ) (tensorRight T)]
  [∀ (T : C),
    PreservesColimitsOfShape (Discrete (Σ _ : ℕ, ℕ)) (tensorRight T)] in
/-- The right triangle equation evaluates a monoid's singleton
generators to themselves. -/
theorem tensorWordAdjunction_right_triangle (M : Mon C) :
    tensorWordGenerator M.X ≫ tensorWordLift M (𝟙 M.X) = 𝟙 M.X :=
  tensorWordLift_beta M (𝟙 _)

/-- The multiplication law uses the actual word-of-word evaluation
maps on both routes through three levels of words. -/
theorem tensorWordMonad_associativity (X : C) :
    tensorWordMap (tensorWordMonad.μ.app X) ≫ tensorWordMonad.μ.app X =
      tensorWordMonad.μ.app (tensorWordObj X) ≫ tensorWordMonad.μ.app X :=
  tensorWordMonad.assoc X






end CategoryTheory.MonoidalCategory.TensorWord
end
end
end source_TensorWordAdjunction
