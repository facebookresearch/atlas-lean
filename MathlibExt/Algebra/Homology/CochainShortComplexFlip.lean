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
## Flip a short complex of cochain complexes to a cochain complex of short complexes
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex
variable {C : Type u} [Category.{v} C] [Abelian C]

/--
The original three cochain objects and differentials, regarded as a cochain complex of short
complexes.
-/
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

/-- The first projection of the flipped complex is literally its original first cochain complex. -/
theorem cochainFlip_π₁ (S : ShortComplex (CochainComplex C ℕ)) :
    ((ShortComplex.π₁ : ShortComplex C ⥤ C).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      S.cochainFlip = S.X₁ := rfl

/-- The middle projection retains the original middle cochain complex. -/
theorem cochainFlip_π₂ (S : ShortComplex (CochainComplex C ℕ)) :
    ((ShortComplex.π₂ : ShortComplex C ⥤ C).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      S.cochainFlip = S.X₂ := rfl

/-- The third projection retains the original third cochain complex. -/
theorem cochainFlip_π₃ (S : ShortComplex (CochainComplex C ℕ)) :
    ((ShortComplex.π₃ : ShortComplex C ⥤ C).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      S.cochainFlip = S.X₃ := rfl

/-- A map between flipped complexes gives strict original maps of all three cochain complexes. -/
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

/-- The map on the first coefficient in every original degree is unchanged. -/
theorem cochainUnflipHom_τ₁_f {S T : ShortComplex (CochainComplex C ℕ)}
    (a : S.cochainFlip ⟶ T.cochainFlip) (n : ℕ) :
    (cochainUnflipHom a).τ₁.f n = (a.f n).τ₁ := rfl

/-- The middle coefficient map is the original component of the strict flipped map. -/
theorem cochainUnflipHom_τ₂_f {S T : ShortComplex (CochainComplex C ℕ)}
    (a : S.cochainFlip ⟶ T.cochainFlip) (n : ℕ) :
    (cochainUnflipHom a).τ₂.f n = (a.f n).τ₂ := rfl

/-- The third coefficient map is the original component of the strict flipped map. -/
theorem cochainUnflipHom_τ₃_f {S T : ShortComplex (CochainComplex C ℕ)}
    (a : S.cochainFlip ⟶ T.cochainFlip) (n : ℕ) :
    (cochainUnflipHom a).τ₃.f n = (a.f n).τ₃ := rfl

end CategoryTheory.ShortComplex
