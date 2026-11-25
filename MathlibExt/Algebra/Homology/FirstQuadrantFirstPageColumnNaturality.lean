/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageColumn

/-!
# Naturality of the direct first-page column

A bicomplex map induces a map between the signed direct-column
presentations.  This map commutes with the sign-removing comparison to the
extended vertical column, and hence with the resulting vertical-homology
comparison.

No spectral-page comparison is constructed here.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

section DirectMap

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C]
variable {K L M : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- The map between signed direct-column presentations induced by a
bicomplex map. -/
noncomputable def horizontalDirectColumnCochainMap
    (f : K ⟶ L) (p : ℕ) :
    horizontalDirectColumnCochain K p ⟶
      horizontalDirectColumnCochain L p where
  f := (HomologicalComplex.extendMap (f.f p)
    (ComplexShape.embeddingUpIntLE (-(p : ℤ)))).f
  comm' := by
    intro i j _
    change
      (HomologicalComplex.extendMap (f.f p)
          (ComplexShape.embeddingUpIntLE (-(p : ℤ)))).f i ≫
          ((p : ℤ).negOnePow •
            ((L.X p).extend
              (ComplexShape.embeddingUpIntLE (-(p : ℤ)))).d i j) =
        ((p : ℤ).negOnePow •
            ((K.X p).extend
              (ComplexShape.embeddingUpIntLE (-(p : ℤ)))).d i j) ≫
          (HomologicalComplex.extendMap (f.f p)
            (ComplexShape.embeddingUpIntLE (-(p : ℤ)))).f j
    rw [Linear.comp_units_smul (R := ℤ),
      Linear.units_smul_comp (R := ℤ),
      (HomologicalComplex.extendMap (f.f p)
        (ComplexShape.embeddingUpIntLE (-(p : ℤ)))).comm]

/-- In a supported degree, the direct-column map is the corresponding
bicomplex-map component transported through the canonical extension
isomorphisms. -/
@[simp]
theorem horizontalDirectColumnCochainMap_f
    (f : K ⟶ L) (p q : ℕ) :
    (horizontalDirectColumnCochainMap f p).f (-(p : ℤ) - q) =
      (horizontalDirectColumnCochainXIso K p q).hom ≫
        (f.f p).f q ≫
      (horizontalDirectColumnCochainXIso L p q).inv := by
  change
    (HomologicalComplex.extendMap (f.f p)
      (ComplexShape.embeddingUpIntLE (-(p : ℤ)))).f (-(p : ℤ) - q) = _
  simpa only [horizontalDirectColumnCochainXIso] using
    (HomologicalComplex.extendMap_f
      (K := K.X p) (L := L.X p) (f.f p)
      (ComplexShape.embeddingUpIntLE (-(p : ℤ)))
      (i := q) (i' := -(p : ℤ) - q) (by simp))

@[simp]
theorem horizontalDirectColumnCochainMap_id
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (p : ℕ) :
    horizontalDirectColumnCochainMap (𝟙 K) p = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext i
  simpa only [horizontalDirectColumnCochain,
    horizontalDirectColumnCochainMap,
    HomologicalComplex.id_f] using
    (HomologicalComplex.extendMap_id_f (K.X p)
      (ComplexShape.embeddingUpIntLE (-(p : ℤ))) i)

@[reassoc, simp]
theorem horizontalDirectColumnCochainMap_comp
    (f : K ⟶ L) (g : L ⟶ M) (p : ℕ) :
    horizontalDirectColumnCochainMap (f ≫ g) p =
      horizontalDirectColumnCochainMap f p ≫
        horizontalDirectColumnCochainMap g p := by
  apply HomologicalComplex.Hom.ext
  funext i
  have h := congrArg (fun k ↦ k.f i)
    (HomologicalComplex.extendMap_comp (f.f p) (g.f p)
      (ComplexShape.embeddingUpIntLE (-(p : ℤ))))
  simpa only [horizontalDirectColumnCochainMap,
    HomologicalComplex.comp_f] using h

end DirectMap

section Homology

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- The sign-removing direct-column isomorphism is natural in the
bicomplex. -/
@[reassoc]
theorem horizontalDirectColumnUntwistIso_hom_naturality
    (f : K ⟶ L) (p : ℕ) :
    horizontalDirectColumnCochainMap f p ≫
        (horizontalDirectColumnUntwistIso L p).hom =
      (horizontalDirectColumnUntwistIso K p).hom ≫
        HomologicalComplex.extendMap (f.f p)
          (ComplexShape.embeddingUpIntLE (-(p : ℤ))) := by
  apply HomologicalComplex.Hom.ext
  funext i
  change
    (HomologicalComplex.extendMap (f.f p)
        (ComplexShape.embeddingUpIntLE (-(p : ℤ)))).f i ≫
        (((p : ℤ) * i).negOnePow • 𝟙 _) =
      (((p : ℤ) * i).negOnePow • 𝟙 _) ≫
        (HomologicalComplex.extendMap (f.f p)
          (ComplexShape.embeddingUpIntLE (-(p : ℤ)))).f i
  rw [Linear.comp_units_smul (R := ℤ),
    Linear.units_smul_comp (R := ℤ),
    Category.comp_id, Category.id_comp]

/-- Direct-column homology identifies naturally with vertical-column
homology under a bicomplex map. -/
@[reassoc]
theorem horizontalDirectColumnHomologyIso_hom_naturality
    (f : K ⟶ L) (p q : ℕ) :
    HomologicalComplex.homologyMap
          (horizontalDirectColumnCochainMap f p) (-(p : ℤ) - q) ≫
        (horizontalDirectColumnHomologyIso L p q).hom =
      (horizontalDirectColumnHomologyIso K p q).hom ≫
        HomologicalComplex.homologyMap (f.f p) q := by
  have hUntwist := congrArg
    (fun k ↦ HomologicalComplex.homologyMap k (-(p : ℤ) - q))
    (horizontalDirectColumnUntwistIso_hom_naturality f p)
  rw [HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp] at hUntwist
  have hExtend := HomologicalComplex.extendHomologyIso_hom_naturality
    (K := K.X p) (L := L.X p) (f.f p)
    (ComplexShape.embeddingUpIntLE (-(p : ℤ)))
    (j := q) (j' := -(p : ℤ) - q) (by simp)
  change
    HomologicalComplex.homologyMap
          (horizontalDirectColumnCochainMap f p) (-(p : ℤ) - q) ≫
        (HomologicalComplex.homologyMap
            (horizontalDirectColumnUntwistIso L p).hom
            (-(p : ℤ) - q) ≫
          ((L.X p).extendHomologyIso
            (ComplexShape.embeddingUpIntLE (-(p : ℤ)))
            (by simp)).hom) =
      (HomologicalComplex.homologyMap
          (horizontalDirectColumnUntwistIso K p).hom
          (-(p : ℤ) - q) ≫
        ((K.X p).extendHomologyIso
          (ComplexShape.embeddingUpIntLE (-(p : ℤ)))
          (by simp)).hom) ≫
        HomologicalComplex.homologyMap (f.f p) q
  calc
    _ = (HomologicalComplex.homologyMap
          (horizontalDirectColumnCochainMap f p) (-(p : ℤ) - q) ≫
        HomologicalComplex.homologyMap
          (horizontalDirectColumnUntwistIso L p).hom
          (-(p : ℤ) - q)) ≫
        ((L.X p).extendHomologyIso
          (ComplexShape.embeddingUpIntLE (-(p : ℤ)))
          (by simp)).hom := (Category.assoc _ _ _).symm
    _ = (HomologicalComplex.homologyMap
          (horizontalDirectColumnUntwistIso K p).hom
          (-(p : ℤ) - q) ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap (f.f p)
            (ComplexShape.embeddingUpIntLE (-(p : ℤ))))
          (-(p : ℤ) - q)) ≫
        ((L.X p).extendHomologyIso
          (ComplexShape.embeddingUpIntLE (-(p : ℤ)))
          (by simp)).hom := by
      rw [hUntwist]
    _ = HomologicalComplex.homologyMap
          (horizontalDirectColumnUntwistIso K p).hom
          (-(p : ℤ) - q) ≫
        (HomologicalComplex.homologyMap
            (HomologicalComplex.extendMap (f.f p)
              (ComplexShape.embeddingUpIntLE (-(p : ℤ))))
            (-(p : ℤ) - q) ≫
          ((L.X p).extendHomologyIso
            (ComplexShape.embeddingUpIntLE (-(p : ℤ)))
            (by simp)).hom) := Category.assoc _ _ _
    _ = HomologicalComplex.homologyMap
          (horizontalDirectColumnUntwistIso K p).hom
          (-(p : ℤ) - q) ≫
        (((K.X p).extendHomologyIso
            (ComplexShape.embeddingUpIntLE (-(p : ℤ)))
            (by simp)).hom ≫
          HomologicalComplex.homologyMap (f.f p) q) := by
      rw [hExtend]
    _ = (HomologicalComplex.homologyMap
          (horizontalDirectColumnUntwistIso K p).hom
          (-(p : ℤ) - q) ≫
        ((K.X p).extendHomologyIso
          (ComplexShape.embeddingUpIntLE (-(p : ℤ)))
          (by simp)).hom) ≫
        HomologicalComplex.homologyMap (f.f p) q :=
      (Category.assoc _ _ _).symm

end Homology

end HomologicalComplex₂

end
