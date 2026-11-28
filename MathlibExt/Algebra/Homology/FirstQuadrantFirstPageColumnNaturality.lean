/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageColumn

/-!
# Naturality of signed direct columns and their vertical homology

Let C be preadditive with a zero object, and let f : K → L be a map
of nonnegative homological bicomplexes. The direct column D_p is the
extension of K_p along q ↦ −p−q, with differential multiplied by
(−1)^p. Extending f_p gives D_p(f), preserving the same scalar sign.

In degree −p−q this map is the component f_(p,q) transported through
the extension identifications. It preserves identities and composition.
For abelian C, the degreewise sign-removing isomorphism
D_p ≅ extend(K_p) and the homology comparison
H_(−p−q)(D_p) ≅ H_q(K_p)
are natural in f. The category object and morphism worlds are independent.
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

/-- For a nonnegative homological bicomplex map f : K → L in
a preadditive category with a zero object, extending its column-p
chain map along q ↦ −p−q gives D_p(f) : D_p(K) → D_p(L).
Both column differentials carry the multiplier (−1)^p, so the
extended component maps commute with them. -/
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

/-- For a nonnegative homological bicomplex map f : K → L,
p,q ≥ 0 and i=−p−q, the component of D_p(f) is
α_L⁻¹ ∘ f_(p,q) ∘ α_K.
Here α_K : D_p(K)_i ≅ K_(p,q) and α_L are the canonical
extension object identifications in the preadditive target
category with a zero object. -/
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

/-- For a map f : K → L of nonnegative homological bicomplexes
in an abelian category and p ≥ 0, let u_K,u_L remove the
constant column sign by degreewise multiplication (−1)^(p i).
Then u_L ∘ D_p(f) = extend(f_p) ∘ u_K as cochain maps. -/
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

/-- For a nonnegative homological bicomplex map f : K → L
in an abelian category, the comparisons
χ_K : H_(−p−q)(D_p(K)) ≅ H_q(K_p) and χ_L satisfy
χ_L ∘ H_(−p−q)(D_p(f)) = H_q(f_p) ∘ χ_K.
This is a square between direct-column and vertical-column homology. -/
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
