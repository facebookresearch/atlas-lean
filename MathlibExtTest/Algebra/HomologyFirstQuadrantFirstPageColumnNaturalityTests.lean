/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Data.ZMod.Basic
public import
  MathlibExt.Algebra.Homology.FirstQuadrantFirstPageColumnNaturality

/-! # Tests for direct first-page column naturality -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂.FirstQuadrantFirstPageColumnNaturalityTests

section DirectMap

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalDirectColumnCochainMap
#check horizontalDirectColumnCochainMap_f
#check horizontalDirectColumnCochainMap_id
#check horizontalDirectColumnCochainMap_comp

example (f : K ⟶ L) (p : ℕ) :
    horizontalDirectColumnCochain K p ⟶
      horizontalDirectColumnCochain L p :=
  horizontalDirectColumnCochainMap f p

example (f : K ⟶ L) (p q : ℕ) :
    (horizontalDirectColumnCochainMap f p).f (-(p : ℤ) - q) =
      (horizontalDirectColumnCochainXIso K p q).hom ≫
        (f.f p).f q ≫
      (horizontalDirectColumnCochainXIso L p q).inv :=
  horizontalDirectColumnCochainMap_f f p q

example (p : ℕ) :
    horizontalDirectColumnCochainMap (𝟙 K) p = 𝟙 _ :=
  horizontalDirectColumnCochainMap_id K p

example (f : K ⟶ L) (g : L ⟶ M) (p : ℕ) :
    horizontalDirectColumnCochainMap (f ≫ g) p =
      horizontalDirectColumnCochainMap f p ≫
        horizontalDirectColumnCochainMap g p :=
  horizontalDirectColumnCochainMap_comp f g p

example (f : K ⟶ L) :
    (horizontalDirectColumnCochainMap f 0).f 0 =
      (horizontalDirectColumnCochainXIso K 0 0).hom ≫
        (f.f 0).f 0 ≫
      (horizontalDirectColumnCochainXIso L 0 0).inv := by
  simpa using horizontalDirectColumnCochainMap_f f 0 0

example (p : ℕ) :
    horizontalDirectColumnCochainMap (0 : K ⟶ L) p = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  change
    (HomologicalComplex.extendMap (0 : K.X p ⟶ L.X p)
      (ComplexShape.embeddingUpIntLE (-(p : ℤ)))).f i = 0
  rw [HomologicalComplex.extendMap_zero]
  rfl

example (p : ℕ) :
    horizontalDirectColumnCochainMap
        (𝟙 (HomologicalComplex.zero :
          HomologicalComplex₂ C (ComplexShape.down ℕ)
          (ComplexShape.down ℕ))) p = 𝟙 _ :=
  horizontalDirectColumnCochainMap_id _ p

end DirectMap

section Homology

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

#check horizontalDirectColumnUntwistIso_hom_naturality
#check horizontalDirectColumnHomologyIso_hom_naturality

example (f : K ⟶ L) (p : ℕ) :
    horizontalDirectColumnCochainMap f p ≫
        (horizontalDirectColumnUntwistIso L p).hom =
      (horizontalDirectColumnUntwistIso K p).hom ≫
        HomologicalComplex.extendMap (f.f p)
          (ComplexShape.embeddingUpIntLE (-(p : ℤ))) :=
  horizontalDirectColumnUntwistIso_hom_naturality f p

example (f : K ⟶ L) (p q : ℕ) :
    HomologicalComplex.homologyMap
          (horizontalDirectColumnCochainMap f p) (-(p : ℤ) - q) ≫
        (horizontalDirectColumnHomologyIso L p q).hom =
      (horizontalDirectColumnHomologyIso K p q).hom ≫
        HomologicalComplex.homologyMap (f.f p) q :=
  horizontalDirectColumnHomologyIso_hom_naturality f p q

example (f : K ⟶ L) :
    horizontalDirectColumnCochainMap f 0 ≫
        (horizontalDirectColumnUntwistIso L 0).hom =
      (horizontalDirectColumnUntwistIso K 0).hom ≫
        HomologicalComplex.extendMap (f.f 0)
          (ComplexShape.embeddingUpIntLE 0) := by
  simpa using horizontalDirectColumnUntwistIso_hom_naturality f 0

example (f : K ⟶ L) (p : ℕ) :
    HomologicalComplex.homologyMap
          (horizontalDirectColumnCochainMap f p)
            (-(p : ℤ) - ((0 : ℕ) : ℤ)) ≫
        (horizontalDirectColumnHomologyIso L p 0).hom =
      (horizontalDirectColumnHomologyIso K p 0).hom ≫
        HomologicalComplex.homologyMap (f.f p) 0 := by
  simpa using horizontalDirectColumnHomologyIso_hom_naturality f p 0

example (f : K ⟶ L) :
    HomologicalComplex.homologyMap
          (horizontalDirectColumnCochainMap f 0) 0 ≫
        (horizontalDirectColumnHomologyIso L 0 0).hom =
      (horizontalDirectColumnHomologyIso K 0 0).hom ≫
        HomologicalComplex.homologyMap (f.f 0) 0 := by
  simpa using horizontalDirectColumnHomologyIso_hom_naturality f 0 0

end Homology

section ZeroRing

variable {K L : HomologicalComplex₂ (ModuleCat.{0} (ZMod 1))
  (ComplexShape.down ℕ) (ComplexShape.down ℕ)}

example (f : K ⟶ L) (p q : ℕ) :=
  horizontalDirectColumnHomologyIso_hom_naturality f p q

end ZeroRing

#print axioms horizontalDirectColumnCochainMap
#print axioms horizontalDirectColumnCochainMap_f
#print axioms horizontalDirectColumnCochainMap_id
#print axioms horizontalDirectColumnCochainMap_comp
#print axioms horizontalDirectColumnUntwistIso_hom_naturality
#print axioms horizontalDirectColumnHomologyIso_hom_naturality

end HomologicalComplex₂.FirstQuadrantFirstPageColumnNaturalityTests

end
