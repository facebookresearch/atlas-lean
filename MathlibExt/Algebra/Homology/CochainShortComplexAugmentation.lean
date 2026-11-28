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
# Coaugmentation of a cochain complex of short complexes

In an abelian category, three coaugmentations of nonnegative cochain
complexes over a short complex, with commuting degree-zero squares,
give a single coaugmentation into the transposed cochain complex of
short complexes. If each coaugmentation is a quasi-isomorphism, the
degree-zero diagram map is mono, its first row is exact, and all
positive rows are exact in the category of short complexes.
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

/-- In an abelian category `C`, let `S : X₁ → X₂ → X₃` be a
short complex and `P₁ → P₂ → P₃` a short complex of nonnegative
cochain complexes. Choose coaugmentations `ι_k : X_k[0] → P_k`
whose degree-zero squares commute with both sequence maps. The three degree-zero components give a
morphism from `S`
to the degree-zero row of the transposed cochain complex of
short complexes. -/
def cochainFlipCoaugmentationZero : S ⟶ P.flip.X 0 :=
  ShortComplex.homMk (ι₁.f 0) (ι₂.f 0) (ι₃.f 0) hf hg

/-- In an abelian category `C`, let `S : X₁ → X₂ → X₃` be a
short complex and `P₁ → P₂ → P₃` a short complex of nonnegative
cochain complexes. Choose coaugmentations `ι_k : X_k[0] → P_k`
whose degree-zero squares commute with both sequence maps. The three closed coaugmentation maps
combine into a
cochain map `S[0] → P.flip` in the category of short complexes. -/
def cochainFlipCoaugmentation :
    (CochainComplex.single₀ (ShortComplex C)).obj S ⟶ P.flip :=
  (CochainComplex.fromSingle₀Equiv P.flip S).symm
    ⟨cochainFlipCoaugmentationZero ι₁ ι₂ ι₃ hf hg, by
      apply ShortComplex.hom_ext
      · exact (CochainComplex.fromSingle₀Equiv P.X₁ S.X₁ ι₁).property
      · exact (CochainComplex.fromSingle₀Equiv P.X₂ S.X₂ ι₂).property
      · exact (CochainComplex.fromSingle₀Equiv P.X₃ S.X₃ ι₃).property⟩

/-- In an abelian category `C`, let `S : X₁ → X₂ → X₃` be a
short complex and `P₁ → P₂ → P₃` a short complex of nonnegative
cochain complexes. Choose coaugmentations `ι_k : X_k[0] → P_k`
whose degree-zero squares commute with both sequence maps. The degree-zero component of the
combined coaugmentation
is the diagram map with components `ι₁⁰,ι₂⁰,ι₃⁰`. -/
theorem cochainFlipCoaugmentation_f_zero :
    (cochainFlipCoaugmentation ι₁ ι₂ ι₃ hf hg).f 0 =
      cochainFlipCoaugmentationZero ι₁ ι₂ ι₃ hf hg :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- In an abelian category `C`, let `S : X₁ → X₂ → X₃` be a
short complex and `P₁ → P₂ → P₃` a short complex of nonnegative
cochain complexes. Choose coaugmentations `ι_k : X_k[0] → P_k`
whose degree-zero squares commute with both sequence maps. If every `ι_k` is a quasi-isomorphism,
the degree-zero
coaugmentation `S → P.flip⁰` is mono in `ShortComplex C`. -/
theorem cochainFlipCoaugmentation_mono [_root_.QuasiIso ι₁] [_root_.QuasiIso ι₂]
    [_root_.QuasiIso ι₃] :
    Mono ((cochainFlipCoaugmentation ι₁ ι₂ ι₃ hf hg).f 0) := by
  rw [cochainFlipCoaugmentation_f_zero]
  exact @mono_of_components C _ _ S (P.flip.X 0)
    (cochainFlipCoaugmentationZero ι₁ ι₂ ι₃ hf hg)
    (CochainComplex.coaugmentation_exact_and_mono ι₁).2
    (CochainComplex.coaugmentation_exact_and_mono ι₂).2
    (CochainComplex.coaugmentation_exact_and_mono ι₃).2

/-- In an abelian category `C`, let `S : X₁ → X₂ → X₃` be a
short complex and `P₁ → P₂ → P₃` a short complex of nonnegative
cochain complexes. Choose coaugmentations `ι_k : X_k[0] → P_k`
whose degree-zero squares commute with both sequence maps. If every `ι_k` is a quasi-isomorphism,
the first row
`S → P.flip⁰ → P.flip¹` is exact in `ShortComplex C`. -/
theorem cochainFlipCoaugmentation_exact [_root_.QuasiIso ι₁] [_root_.QuasiIso ι₂]
    [_root_.QuasiIso ι₃] :
    (ShortComplex.mk ((cochainFlipCoaugmentation ι₁ ι₂ ι₃ hf hg).f 0)
      (P.flip.d 0 1)
      (by rw [HomologicalComplex.Hom.comm, HomologicalComplex.single_obj_d, zero_comp])).Exact := by
  simp only [cochainFlipCoaugmentation_f_zero]
  exact exact_of_components _
    (CochainComplex.coaugmentation_exact_and_mono ι₁).1
    (CochainComplex.coaugmentation_exact_and_mono ι₂).1
    (CochainComplex.coaugmentation_exact_and_mono ι₃).1

omit hf hg in
/-- In an abelian category `C`, let `S : X₁ → X₂ → X₃` be a
short complex and `P₁ → P₂ → P₃` a short complex of nonnegative
cochain complexes. Choose coaugmentations `ι_k : X_k[0] → P_k`
whose degree-zero squares commute with both sequence maps. If every `ι_k` is a quasi-isomorphism,
the row
`P.flipⁿ → P.flip^(n+1) → P.flip^(n+2)` is exact at its middle
object in `ShortComplex C` for every `n`. -/
theorem cochainFlip_exact_succ [_root_.QuasiIso ι₁] [_root_.QuasiIso ι₂]
    [_root_.QuasiIso ι₃] (n : ℕ) :
    (ShortComplex.mk (P.flip.d n (n + 1)) (P.flip.d (n + 1) (n + 2))
      (P.flip.d_comp_d n (n + 1) (n + 2))).Exact :=
  exact_of_components _
    (CochainComplex.coaugmentation_exact_succ ι₁ n)
    (CochainComplex.coaugmentation_exact_succ ι₂ n)
    (CochainComplex.coaugmentation_exact_succ ι₃ n)

end CategoryTheory.ShortComplex
