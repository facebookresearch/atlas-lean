/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Embedding.DownNatToIntExact
public import MathlibExt.Algebra.Homology.PartialTotalZero

/-!
# Uniform steps of the partial-total filtration

The zero and successor stages give a natural family of short exact
filtration steps. Zero extension places each step in an integer-graded
cochain short complex.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

local instance : HasFiniteBiproducts C :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- The short complex attached to the `p`th filtration step: the zero-stage
sequence when `p=0`, and the predecessor/successor sequence when `p=m+1`. -/
noncomputable def partialTotalStepShortComplex :
    (p : ℕ) → ShortComplex (ChainComplex C ℕ)
  | 0 => B.partialTotalZeroShortComplex
  | m + 1 => B.partialTotalSuccShortComplex m

@[simp]
theorem partialTotalStepShortComplex_zero :
    B.partialTotalStepShortComplex 0 = B.partialTotalZeroShortComplex :=
  rfl

@[simp]
theorem partialTotalStepShortComplex_succ (m : ℕ) :
    B.partialTotalStepShortComplex (m + 1) =
      B.partialTotalSuccShortComplex m :=
  rfl

theorem partialTotalStepShortComplex_X₁_zero :
    (B.partialTotalStepShortComplex 0).X₁ = 0 :=
  rfl

theorem partialTotalStepShortComplex_X₁_succ (m : ℕ) :
    (B.partialTotalStepShortComplex (m + 1)).X₁ = B.partialTotal m :=
  rfl

@[simp]
theorem partialTotalStepShortComplex_X₂ (p : ℕ) :
    (B.partialTotalStepShortComplex p).X₂ = B.partialTotal p := by
  cases p <;> rfl

@[simp]
theorem partialTotalStepShortComplex_X₃ (p : ℕ) :
    (B.partialTotalStepShortComplex p).X₃ = B.totalRow p := by
  cases p <;> rfl

theorem partialTotalStepShortComplex_f_zero :
    (B.partialTotalStepShortComplex 0).f = 0 :=
  rfl

theorem partialTotalStepShortComplex_f_succ (m : ℕ) :
    (B.partialTotalStepShortComplex (m + 1)).f =
      B.partialTotalMap (Nat.le_succ m) :=
  rfl

theorem partialTotalStepShortComplex_g_zero :
    (B.partialTotalStepShortComplex 0).g =
      B.partialTotalRowQuotient 0 :=
  rfl

theorem partialTotalStepShortComplex_g_succ (m : ℕ) :
    (B.partialTotalStepShortComplex (m + 1)).g =
      B.partialTotalRowQuotient (m + 1) :=
  rfl

variable {B}
variable {B' B'' : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- A bicomplex morphism induces a morphism of the uniform partial-total
filtration-step presentation. -/
noncomputable def partialTotalStepShortComplexMap (φ : B ⟶ B') :
    (p : ℕ) → B.partialTotalStepShortComplex p ⟶
      B'.partialTotalStepShortComplex p
  | 0 => partialTotalZeroShortComplexMap φ
  | m + 1 => B.partialTotalSuccShortComplexMap φ m

@[simp]
theorem partialTotalStepShortComplexMap_zero (φ : B ⟶ B') :
    partialTotalStepShortComplexMap φ 0 =
      partialTotalZeroShortComplexMap φ :=
  rfl

@[simp]
theorem partialTotalStepShortComplexMap_succ (φ : B ⟶ B') (m : ℕ) :
    partialTotalStepShortComplexMap φ (m + 1) =
      B.partialTotalSuccShortComplexMap φ m :=
  rfl

@[simp]
theorem partialTotalStepShortComplexMap_id
    (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p : ℕ) :
    partialTotalStepShortComplexMap (𝟙 B) p = 𝟙 _ := by
  cases p with
  | zero => exact partialTotalZeroShortComplexMap_id B
  | succ m => exact B.partialTotalSuccShortComplexMap_id m

@[reassoc]
theorem partialTotalStepShortComplexMap_comp
    (φ : B ⟶ B') (ψ : B' ⟶ B'') (p : ℕ) :
    partialTotalStepShortComplexMap (φ ≫ ψ) p =
      partialTotalStepShortComplexMap φ p ≫
        partialTotalStepShortComplexMap ψ p := by
  cases p with
  | zero => exact partialTotalZeroShortComplexMap_comp φ ψ
  | succ m => exact B.partialTotalSuccShortComplexMap_comp φ ψ m

/-- At a fixed filtration index, the partial-total step presentation is
functorial in the bicomplex. -/
noncomputable abbrev partialTotalStepShortComplexFunctor (p : ℕ) :
    HomologicalComplex₂ C (ComplexShape.down ℕ) (ComplexShape.down ℕ) ⥤
      ShortComplex (ChainComplex C ℕ) where
  obj B := B.partialTotalStepShortComplex p
  map φ := partialTotalStepShortComplexMap φ p
  map_id B := partialTotalStepShortComplexMap_id B p
  map_comp φ ψ := partialTotalStepShortComplexMap_comp φ ψ p

variable (B)

/-- The `p`th filtration step after extension from chain degree `n` to
cochain degree `-n`. -/
noncomputable def partialTotalStepCochainShortComplex (p : ℕ) :
    ShortComplex (CochainComplex C ℤ) :=
  (B.partialTotalStepShortComplex p).map
    (ComplexShape.embeddingDownNat.extendFunctor C)

/-- The cochain filtration step at a successor is the extension of the raw
successor short complex. -/
@[simp]
theorem partialTotalStepCochainShortComplex_succ (m : ℕ) :
    B.partialTotalStepCochainShortComplex (m + 1) =
      (B.partialTotalSuccShortComplex m).map
        (ComplexShape.embeddingDownNat.extendFunctor C) :=
  rfl

section Abelian

variable {D : Type u} [Category.{v} D] [Abelian D]

/-- Every chain-level filtration step is short exact. -/
theorem partialTotalStepShortExact
    (B : HomologicalComplex₂ D (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p : ℕ) :
    (B.partialTotalStepShortComplex p).ShortExact := by
  cases p with
  | zero => exact B.partialTotalZeroShortExact
  | succ m => exact B.partialTotalSuccShortExact m

/-- Extension to integer-graded cochain complexes preserves exactness of
every filtration step. -/
theorem partialTotalStepCochainShortExact
    (B : HomologicalComplex₂ D (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p : ℕ) :
    (B.partialTotalStepCochainShortComplex p).ShortExact :=
  ShortComplex.ShortExact.map_extendFunctor ComplexShape.embeddingDownNat
    (B.partialTotalStepShortComplex p) (B.partialTotalStepShortExact p)

end Abelian

end HomologicalComplex₂

end
