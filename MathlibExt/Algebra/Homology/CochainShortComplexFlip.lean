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
# Transposing short complexes of arbitrary-shape complexes

In a category with zero morphisms, a short complex of complexes of any shape
transposes into a complex of short complexes of the same shape. Its projections
recover the three input complexes, and a map of transposed complexes recovers
a map of the original short complexes. The cochain names also specialize to
natural or integer cochain shapes without an abelian-category assumption.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {ι : Type w} {c : ComplexShape ι}

/-- In a category with zero morphisms `C`, let `S` be a short complex of
complexes of arbitrary shape. Transposing gives a complex whose degree-`n` object
is the short complex `S₁^n → S₂^n → S₃^n` and whose differential
has components `d_S₁,d_S₂,d_S₃`. -/
def cochainFlip (S : ShortComplex (HomologicalComplex C c)) :
    HomologicalComplex (ShortComplex C) c where
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

/-- In a category with zero morphisms `C`, let `S` be a short complex of
complexes of arbitrary shape. Projection to the first object of each transposed row
recovers the first complex `S₁`. -/
theorem cochainFlip_π₁ (S : ShortComplex (HomologicalComplex C c)) :
    ((ShortComplex.π₁ : ShortComplex C ⥤ C).mapHomologicalComplex (c)).obj
      S.cochainFlip = S.X₁ := rfl

/-- In a category with zero morphisms `C`, let `S` be a short complex of
complexes of arbitrary shape. Projection to the middle object of each transposed row
recovers the middle complex `S₂`. -/
theorem cochainFlip_π₂ (S : ShortComplex (HomologicalComplex C c)) :
    ((ShortComplex.π₂ : ShortComplex C ⥤ C).mapHomologicalComplex (c)).obj
      S.cochainFlip = S.X₂ := rfl

/-- In a category with zero morphisms `C`, let `S` be a short complex of
complexes of arbitrary shape. Projection to the third object of each transposed row
recovers the third complex `S₃`. -/
theorem cochainFlip_π₃ (S : ShortComplex (HomologicalComplex C c)) :
    ((ShortComplex.π₃ : ShortComplex C ⥤ C).mapHomologicalComplex (c)).obj
      S.cochainFlip = S.X₃ := rfl

/-- In a category with zero morphisms `C`, let `S,T` be short complexes of
complexes of arbitrary shape. A map of complexes `a : S.cochainFlip → T.cochainFlip`
induces a morphism of the original short complexes, using its
three components in every degree. -/
def cochainUnflipHom {S T : ShortComplex (HomologicalComplex C c)}
    (a : S.cochainFlip ⟶ T.cochainFlip) : S ⟶ T where
  τ₁ := ((ShortComplex.π₁ : ShortComplex C ⥤ C).mapHomologicalComplex (c)).map a
  τ₂ := ((ShortComplex.π₂ : ShortComplex C ⥤ C).mapHomologicalComplex (c)).map a
  τ₃ := ((ShortComplex.π₃ : ShortComplex C ⥤ C).mapHomologicalComplex (c)).map a
  comm₁₂ := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact (a.f n).comm₁₂
  comm₂₃ := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact (a.f n).comm₂₃

/-- In a category with zero morphisms `C`, for `a : S.cochainFlip → T.cochainFlip`, the
first component of the recovered short-complex map in
degree `n` is the first component of the row map `aⁿ`. -/
theorem cochainUnflipHom_τ₁_f {S T : ShortComplex (HomologicalComplex C c)}
    (a : S.cochainFlip ⟶ T.cochainFlip) (n : ι) :
    (cochainUnflipHom a).τ₁.f n = (a.f n).τ₁ := rfl

/-- In a category with zero morphisms `C`, for `a : S.cochainFlip → T.cochainFlip`, the
middle component of the recovered short-complex map in
degree `n` is the middle component of the row map `aⁿ`. -/
theorem cochainUnflipHom_τ₂_f {S T : ShortComplex (HomologicalComplex C c)}
    (a : S.cochainFlip ⟶ T.cochainFlip) (n : ι) :
    (cochainUnflipHom a).τ₂.f n = (a.f n).τ₂ := rfl

/-- In a category with zero morphisms `C`, for `a : S.cochainFlip → T.cochainFlip`, the
third component of the recovered short-complex map in
degree `n` is the third component of the row map `aⁿ`. -/
theorem cochainUnflipHom_τ₃_f {S T : ShortComplex (HomologicalComplex C c)}
    (a : S.cochainFlip ⟶ T.cochainFlip) (n : ι) :
    (cochainUnflipHom a).τ₃.f n = (a.f n).τ₃ := rfl

end CategoryTheory.ShortComplex
