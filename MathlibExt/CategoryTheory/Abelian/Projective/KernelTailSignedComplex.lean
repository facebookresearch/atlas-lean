/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.Projective.KernelTailResolution
public import MathlibExt.CategoryTheory.Abelian.Projective.Horseshoe

/-!
# The alternating-cross kernel-tail horseshoe complex
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
namespace CategoryTheory.ProjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C]

local instance : ChainComplex.kernelTailEmbedding.IsRelIff :=
  ComplexShape.instIsRelIffEmbeddingDown'Add 1 1

/-- The cross coefficient of the kernel-tail horseshoe in differential degree n+1. -/
def normalizationCrossSign (n : ℕ) : ℤ := (-1) ^ (n + 1)

/-- Consecutive original cross coefficients have opposite signs. -/
theorem normalizationCrossSign_succ (n : ℕ) :
    normalizationCrossSign (n + 1) = -normalizationCrossSign n := by
  simp only [normalizationCrossSign, pow_succ, mul_neg, mul_one]

/-- The original tail differential is the next original resolution differential. -/
theorem normalizationKernelTail_d {X : C} (P : ProjectiveResolution X) (n : ℕ) :
    (normalizationKernelTail P).complex.d (n + 1) n =
      (normalizationKernelTailXIso P (n + 1)).hom ≫ P.complex.d (n + 2) (n + 1) ≫
        (normalizationKernelTailXIso P n).inv :=
  P.complex.restriction_d_eq ChainComplex.kernelTailEmbedding
    (ChainComplex.kernelTailEmbedding_f (n + 1)) (ChainComplex.kernelTailEmbedding_f n)

/-- The cross map is the alternating identity in the original tail coordinates. -/
def normalizationCross {X : C} (P : ProjectiveResolution X) (n : ℕ) :
    P.complex.X (n + 1) ⟶ (normalizationKernelTail P).complex.X n :=
  normalizationCrossSign n • (normalizationKernelTailXIso P n).inv

set_option backward.isDefEq.respectTransparency false in
/-- The cross maps satisfy the chain relation with the original two differentials. -/
theorem normalizationCross_relation {X : C} (P : ProjectiveResolution X) (n : ℕ) :
    normalizationCross P (n + 1) ≫ (normalizationKernelTail P).complex.d (n + 1) n +
      P.complex.d (n + 2) (n + 1) ≫ normalizationCross P n = 0 := by
  rw [normalizationKernelTail_d]
  simp only [normalizationCross, normalizationCrossSign_succ, neg_zsmul,
    neg_comp, zsmul_comp, comp_zsmul, Iso.inv_hom_id_assoc,
    neg_add_cancel]

/-- The original signed horseshoe differential in endpoint biproduct coordinates. -/
def normalizationMiddleDifferential {X : C} (P : ProjectiveResolution X) (n : ℕ) :
    ((normalizationKernelTail P).complex.X (n + 1) ⊞ P.complex.X (n + 1)) ⟶
      ((normalizationKernelTail P).complex.X n ⊞ P.complex.X n) :=
  Biprod.ofComponents ((normalizationKernelTail P).complex.d (n + 1) n) 0
    (normalizationCross P n) (P.complex.d (n + 1) n)

/-- The signed middle differential squares to zero. -/
theorem normalizationMiddleDifferential_sq {X : C} (P : ProjectiveResolution X) (n : ℕ) :
    normalizationMiddleDifferential P (n + 1) ≫ normalizationMiddleDifferential P n = 0 := by
  rw [normalizationMiddleDifferential, normalizationMiddleDifferential, Biprod.ofComponents_comp]
  simp only [HomologicalComplex.d_comp_d, zero_comp, comp_zero, add_zero,
    normalizationCross_relation]
  ext <;> simp [Biprod.ofComponents]

/-- The signed kernel-tail horseshoe complex on the original endpoint objects. -/
def normalizationMiddleComplex {X : C} (P : ProjectiveResolution X) : ChainComplex C ℕ :=
  ChainComplex.of
    (fun n => (normalizationKernelTail P).complex.X n ⊞ P.complex.X n)
    (normalizationMiddleDifferential P) (normalizationMiddleDifferential_sq P)

/-- Its original differential is the explicit alternating-cross differential. -/
theorem normalizationMiddleComplex_d {X : C} (P : ProjectiveResolution X) (n : ℕ) :
    (normalizationMiddleComplex P).d (n + 1) n = normalizationMiddleDifferential P n := by
  dsimp only [normalizationMiddleComplex]
  exact ChainComplex.of_d _ _ n

end CategoryTheory.ProjectiveResolution
