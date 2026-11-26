/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.Single

/-!
# Transposing short complexes of cochain complexes

In an abelian category, a short complex of nonnegative cochain
complexes can be transposed into a nonnegative cochain complex of
short complexes. Its degree-`n` row has the three original degree-`n`
objects and sequence maps, and its differential has the three
cochain differentials. Projection recovers each original complex;
a map between transposed complexes recovers a map of the original
short complexes with the same degree components.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- In an abelian category `C`, let `S` be a short complex of
nonnegative cochain complexes. Transposing gives a cochain complex whose degree-`n` object
is the short complex `S₁^n → S₂^n → S₃^n` and whose differential
has components `d_S₁,d_S₂,d_S₃`. -/
def cochainFlip (S : ShortComplex (CochainComplex C ℕ)) :
    CochainComplex (ShortComplex C) ℕ where
  X n := ShortComplex.mk (S.f.f n) (S.g.f n)
    (by simpa only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] using
      HomologicalComplex.congr_hom S.zero n)
  d i j :=
    { τ₁ := S.X₁.d i j
      τ₂ := S.X₂.d i j
      τ₃ := S.X₃.d i j
      comm₁₂ := (S.f.comm i j).symm
      comm₂₃ := (S.g.comm i j).symm }
  shape i j hij := by
    apply ShortComplex.hom_ext
    · exact S.X₁.shape i j hij
    · exact S.X₂.shape i j hij
    · exact S.X₃.shape i j hij
  d_comp_d' i j k _ _ := by
    apply ShortComplex.hom_ext
    · exact S.X₁.d_comp_d i j k
    · exact S.X₂.d_comp_d i j k
    · exact S.X₃.d_comp_d i j k

/-- In an abelian category `C`, let `S` be a short complex of
nonnegative cochain complexes. Projection to the first object of each transposed row
recovers the first cochain complex `S₁`. -/
theorem cochainFlip_π₁ (S : ShortComplex (CochainComplex C ℕ)) :
    ((ShortComplex.π₁ : ShortComplex C ⥤ C).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      S.cochainFlip = S.X₁ := rfl

/-- In an abelian category `C`, let `S` be a short complex of
nonnegative cochain complexes. Projection to the middle object of each transposed row
recovers the middle cochain complex `S₂`. -/
theorem cochainFlip_π₂ (S : ShortComplex (CochainComplex C ℕ)) :
    ((ShortComplex.π₂ : ShortComplex C ⥤ C).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      S.cochainFlip = S.X₂ := rfl

/-- In an abelian category `C`, let `S` be a short complex of
nonnegative cochain complexes. Projection to the third object of each transposed row
recovers the third cochain complex `S₃`. -/
theorem cochainFlip_π₃ (S : ShortComplex (CochainComplex C ℕ)) :
    ((ShortComplex.π₃ : ShortComplex C ⥤ C).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      S.cochainFlip = S.X₃ := rfl

/-- In an abelian category `C`, let `S,T` be short complexes of
nonnegative cochain complexes. A cochain map `a : S.flip → T.flip`
induces a morphism of the original short complexes, using its
three components in every degree. -/
def cochainUnflipHom {S T : ShortComplex (CochainComplex C ℕ)}
    (a : S.cochainFlip ⟶ T.cochainFlip) : S ⟶ T where
  τ₁ := ((ShortComplex.π₁ : ShortComplex C ⥤ C).mapHomologicalComplex (ComplexShape.up ℕ)).map a
  τ₂ := ((ShortComplex.π₂ : ShortComplex C ⥤ C).mapHomologicalComplex (ComplexShape.up ℕ)).map a
  τ₃ := ((ShortComplex.π₃ : ShortComplex C ⥤ C).mapHomologicalComplex (ComplexShape.up ℕ)).map a
  comm₁₂ := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact (a.f n).comm₁₂
  comm₂₃ := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact (a.f n).comm₂₃

/-- In an abelian category `C`, for `a : S.flip → T.flip`, the
first cochain component of the recovered short-complex map in
degree `n` is the first component of the row map `aⁿ`. -/
theorem cochainUnflipHom_τ₁_f {S T : ShortComplex (CochainComplex C ℕ)}
    (a : S.cochainFlip ⟶ T.cochainFlip) (n : ℕ) :
    (cochainUnflipHom a).τ₁.f n = (a.f n).τ₁ := rfl

/-- In an abelian category `C`, for `a : S.flip → T.flip`, the
middle cochain component of the recovered short-complex map in
degree `n` is the middle component of the row map `aⁿ`. -/
theorem cochainUnflipHom_τ₂_f {S T : ShortComplex (CochainComplex C ℕ)}
    (a : S.cochainFlip ⟶ T.cochainFlip) (n : ℕ) :
    (cochainUnflipHom a).τ₂.f n = (a.f n).τ₂ := rfl

/-- In an abelian category `C`, for `a : S.flip → T.flip`, the
third cochain component of the recovered short-complex map in
degree `n` is the third component of the row map `aⁿ`. -/
theorem cochainUnflipHom_τ₃_f {S T : ShortComplex (CochainComplex C ℕ)}
    (a : S.cochainFlip ⟶ T.cochainFlip) (n : ℕ) :
    (cochainUnflipHom a).τ₃.f n = (a.f n).τ₃ := rfl

end CategoryTheory.ShortComplex
