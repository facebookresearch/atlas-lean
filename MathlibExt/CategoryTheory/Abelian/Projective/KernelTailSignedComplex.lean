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
# Alternating-cross kernel-tail horseshoe complex

For a projective resolution `P` in an abelian category, let `T` resolve
the kernel of `P₀ → X`, with `T_n ≅ P_(n+1)`. The middle complex has
term `T_n ⊞ P_n`. Its differential has the tail and original
differentials on the diagonal, zero from the left source to the right
target, and cross map `(-1)^(n+1) • (T_n ≅ P_(n+1))⁻¹` from
`P_(n+1)` to `T_n`. These differentials square to zero.
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

/-- For `n ∈ ℕ`, the integer cross coefficient of the kernel-tail
horseshoe differential from degree `n+1` to `n` is
`ε_n=(-1)^(n+1)`. -/
def normalizationCrossSign (n : ℕ) : ℤ := (-1) ^ (n + 1)

/-- For `n ∈ ℕ`, the integer cross coefficients
`ε_n=(-1)^(n+1)` satisfy `ε_(n+1)=-ε_n`. -/
theorem normalizationCrossSign_succ (n : ℕ) :
    normalizationCrossSign (n + 1) = -normalizationCrossSign n := by
  simp only [normalizationCrossSign, pow_succ, mul_neg, mul_one]

/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. Under the tail-coordinate isomorphisms, the differential
`T_(n+1) → T_n` is the original differential
`P_(n+2) → P_(n+1)`. -/
theorem normalizationKernelTail_d {X : C} (P : ProjectiveResolution X) (n : ℕ) :
    (normalizationKernelTail P).complex.d (n + 1) n =
      (normalizationKernelTailXIso P (n + 1)).hom ≫ P.complex.d (n + 2) (n + 1) ≫
        (normalizationKernelTailXIso P n).inv :=
  P.complex.restriction_d_eq ChainComplex.kernelTailEmbedding
    (ChainComplex.kernelTailEmbedding_f (n + 1)) (ChainComplex.kernelTailEmbedding_f n)

/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The cross map `P_(n+1) → T_n` is
`(-1)^(n+1) • (T_n ≅ P_(n+1))⁻¹`. -/
def normalizationCross {X : C} (P : ProjectiveResolution X) (n : ℕ) :
    P.complex.X (n + 1) ⟶ (normalizationKernelTail P).complex.X n :=
  normalizationCrossSign n • (normalizationKernelTailXIso P n).inv

set_option backward.isDefEq.respectTransparency false in
/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The cross maps `γ_n` satisfy
`γ_(n+1) ≫ d_T + d_P ≫ γ_n = 0`, as maps from `P_(n+2)` to `T_n`. -/
theorem normalizationCross_relation {X : C} (P : ProjectiveResolution X) (n : ℕ) :
    normalizationCross P (n + 1) ≫ (normalizationKernelTail P).complex.d (n + 1) n +
      P.complex.d (n + 2) (n + 1) ≫ normalizationCross P n = 0 := by
  rw [normalizationKernelTail_d]
  simp only [normalizationCross, normalizationCrossSign_succ, neg_zsmul,
    neg_comp, zsmul_comp, comp_zsmul, Iso.inv_hom_id_assoc,
    neg_add_cancel]

/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The middle differential `T_(n+1) ⊞ P_(n+1) → T_n ⊞ P_n`
has diagonal maps `d_T,d_P`, zero component `T_(n+1) → P_n`, and
cross component `γ_n : P_(n+1) → T_n` with coefficient `(-1)^(n+1)`. -/
def normalizationMiddleDifferential {X : C} (P : ProjectiveResolution X) (n : ℕ) :
    ((normalizationKernelTail P).complex.X (n + 1) ⊞ P.complex.X (n + 1)) ⟶
      ((normalizationKernelTail P).complex.X n ⊞ P.complex.X n) :=
  Biprod.ofComponents ((normalizationKernelTail P).complex.d (n + 1) n) 0
    (normalizationCross P n) (P.complex.d (n + 1) n)

/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The consecutive middle block differentials have zero
composite from `T_(n+2) ⊞ P_(n+2)` to `T_n ⊞ P_n`. -/
theorem normalizationMiddleDifferential_sq {X : C} (P : ProjectiveResolution X) (n : ℕ) :
    normalizationMiddleDifferential P (n + 1) ≫ normalizationMiddleDifferential P n = 0 := by
  rw [normalizationMiddleDifferential, normalizationMiddleDifferential, Biprod.ofComponents_comp]
  simp only [HomologicalComplex.d_comp_d, zero_comp, comp_zero, add_zero,
    normalizationCross_relation]
  ext <;> simp [Biprod.ofComponents]

/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The terms `T_n ⊞ P_n` with the diagonal differentials and
alternating cross maps form a nonnegative chain complex `M`. -/
def normalizationMiddleComplex {X : C} (P : ProjectiveResolution X) : ChainComplex C ℕ :=
  ChainComplex.of
    (fun n => (normalizationKernelTail P).complex.X n ⊞ P.complex.X n)
    (normalizationMiddleDifferential P) (normalizationMiddleDifferential_sq P)

/-- In an abelian category `C`, let `P` be a projective resolution
of `X`, `π₀ : P₀ → X` its augmentation, `K=ker(π₀)`, and `T` its
kernel-tail resolution with `T_n ≅ P_(n+1)`. The degree-`n+1` to degree-`n` differential of `M` is exactly
the block differential with diagonals `d_T,d_P`, zero left-to-right
component, and alternating cross map `γ_n`. -/
theorem normalizationMiddleComplex_d {X : C} (P : ProjectiveResolution X) (n : ℕ) :
    (normalizationMiddleComplex P).d (n + 1) n = normalizationMiddleDifferential P n := by
  dsimp only [normalizationMiddleComplex]
  exact ChainComplex.of_d _ _ n

end CategoryTheory.ProjectiveResolution
