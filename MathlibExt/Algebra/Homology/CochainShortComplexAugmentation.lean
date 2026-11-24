/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainShortComplexFlip
public import MathlibExt.Algebra.Homology.ShortComplex.ExactComponents
public import MathlibExt.Algebra.Homology.CochainCoaugmentationExact

/-!
## Exact original coaugmentations in the category of short complexes
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex C} {P : ShortComplex (CochainComplex C ℕ)}
variable (ι₁ : (CochainComplex.single₀ C).obj S.X₁ ⟶ P.X₁)
  (ι₂ : (CochainComplex.single₀ C).obj S.X₂ ⟶ P.X₂)
  (ι₃ : (CochainComplex.single₀ C).obj S.X₃ ⟶ P.X₃)
  (hf : ι₁.f 0 ≫ P.f.f 0 = S.f ≫ ι₂.f 0)
  (hg : ι₂.f 0 ≫ P.g.f 0 = S.g ≫ ι₃.f 0)

/-- The original three degree-zero coaugmentations form the exact augmentation diagram. -/
def cochainFlipCoaugmentationZero : S ⟶ P.cochainFlip.X 0 :=
  ShortComplex.homMk (ι₁.f 0) (ι₂.f 0) (ι₃.f 0) hf hg

/-- The original closed coaugmentations give one map from the single short complex. -/
def cochainFlipCoaugmentation :
    (CochainComplex.single₀ (ShortComplex C)).obj S ⟶ P.cochainFlip :=
  (CochainComplex.fromSingle₀Equiv P.cochainFlip S).symm
    ⟨cochainFlipCoaugmentationZero ι₁ ι₂ ι₃ hf hg, by
      apply ShortComplex.hom_ext
      · exact (CochainComplex.fromSingle₀Equiv P.X₁ S.X₁ ι₁).property
      · exact (CochainComplex.fromSingle₀Equiv P.X₂ S.X₂ ι₂).property
      · exact (CochainComplex.fromSingle₀Equiv P.X₃ S.X₃ ι₃).property⟩

/-- This coaugmentation keeps exactly the given degree-zero diagram. -/
theorem cochainFlipCoaugmentation_f_zero :
    (cochainFlipCoaugmentation ι₁ ι₂ ι₃ hf hg).f 0 =
      cochainFlipCoaugmentationZero ι₁ ι₂ ι₃ hf hg :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- Quasi-isomorphic coaugmentations give a monic diagram coaugmentation. -/
theorem cochainFlipCoaugmentation_mono [_root_.QuasiIso ι₁] [_root_.QuasiIso ι₂]
    [_root_.QuasiIso ι₃] :
    Mono ((cochainFlipCoaugmentation ι₁ ι₂ ι₃ hf hg).f 0) := by
  rw [cochainFlipCoaugmentation_f_zero]
  exact @mono_of_components C _ _ S (P.cochainFlip.X 0)
    (cochainFlipCoaugmentationZero ι₁ ι₂ ι₃ hf hg)
    (CochainComplex.coaugmentation_exact_and_mono ι₁).2
    (CochainComplex.coaugmentation_exact_and_mono ι₂).2
    (CochainComplex.coaugmentation_exact_and_mono ι₃).2

/-- The augmentation row is exact in ShortComplex C. -/
theorem cochainFlipCoaugmentation_exact [_root_.QuasiIso ι₁] [_root_.QuasiIso ι₂]
    [_root_.QuasiIso ι₃] :
    (ShortComplex.mk ((cochainFlipCoaugmentation ι₁ ι₂ ι₃ hf hg).f 0)
      (P.cochainFlip.d 0 1)
      (by rw [HomologicalComplex.Hom.comm, HomologicalComplex.single_obj_d, zero_comp])).Exact := by
  simp only [cochainFlipCoaugmentation_f_zero]
  exact exact_of_components _
    (CochainComplex.coaugmentation_exact_and_mono ι₁).1
    (CochainComplex.coaugmentation_exact_and_mono ι₂).1
    (CochainComplex.coaugmentation_exact_and_mono ι₃).1

omit hf hg in
/-- The original positive resolution rows are exact in ShortComplex C. -/
theorem cochainFlip_exact_succ [_root_.QuasiIso ι₁] [_root_.QuasiIso ι₂]
    [_root_.QuasiIso ι₃] (n : ℕ) :
    (ShortComplex.mk (P.cochainFlip.d n (n + 1)) (P.cochainFlip.d (n + 1) (n + 2))
      (P.cochainFlip.d_comp_d n (n + 1) (n + 2))).Exact :=
  exact_of_components _
    (CochainComplex.coaugmentation_exact_succ ι₁ n)
    (CochainComplex.coaugmentation_exact_succ ι₂ n)
    (CochainComplex.coaugmentation_exact_succ ι₃ n)

end CategoryTheory.ShortComplex
