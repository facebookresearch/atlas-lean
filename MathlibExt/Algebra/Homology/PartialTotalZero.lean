/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.PartialTotalSuccessor

/-!
# The zero stage of the partial-total filtration

The zeroth partial total is the signed zeroth row. Its component
identification gives a degreewise split short exact sequence
0 ⟶ partialTotal B 0 ⟶ totalRow B 0.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

local instance : HasFiniteBiproducts C :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

/-- At filtration degree zero, projection to the zeroth signed row followed
by its chosen degreewise section is the identity. -/
theorem partialTotalRowQuotientF_zero_comp_sectionF (n : ℕ) :
    B.partialTotalRowQuotientF 0 n ≫
      B.partialTotalRowQuotientSectionF 0 n = 𝟙 _ := by
  apply HomologicalComplex₂.total.hom_ext
  intro i j hij
  by_cases hi : i = 0
  · subst i
    rw [B.ιTotal_partialTotalRowQuotientF_assoc 0 j n hij,
      B.partialTotalRowQuotientSectionF_eq 0 j n hij]
    have hcancel := congrArg (fun f ↦ f.f j)
      (B.partialTotalLastRowIso 0).hom_inv_id
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hcancel
    rw [Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hcancel, Category.id_comp, Category.comp_id]
  · have hzero : IsZero (((B.firstStupidTrunc 0).X i).X j) := by
      apply (HomologicalComplex.eval C (ComplexShape.down ℕ) j).map_isZero
      apply B.isZero_stupidTrunc_X
        (ComplexShape.embeddingDownNatInitialSegment 0)
      intro a ha
      change a.1 = i at ha
      omega
    exact hzero.eq_of_src _ _

/-- The short complex `0 ⟶ partialTotal B 0 ⟶ totalRow B 0`. -/
noncomputable def partialTotalZeroShortComplex :
    ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk (0 : (0 : ChainComplex C ℕ) ⟶ B.partialTotal 0)
    (B.partialTotalRowQuotient 0) (by simp)

section Functoriality

variable {B B' B'' : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- A bicomplex morphism induces a morphism between the zero-stage
partial-total presentations. -/
noncomputable def partialTotalZeroShortComplexMap (φ : B ⟶ B') :
    B.partialTotalZeroShortComplex ⟶ B'.partialTotalZeroShortComplex where
  τ₁ := 0
  τ₂ := B.partialTotalHom φ 0
  τ₃ := totalRowMap φ 0
  comm₁₂ := (isZero_zero (ChainComplex C ℕ)).eq_of_src _ _
  comm₂₃ := B.partialTotalRowQuotient_naturality φ 0

@[simp]
theorem partialTotalZeroShortComplexMap_id
    (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    partialTotalZeroShortComplexMap (𝟙 B) = 𝟙 _ := by
  apply ShortComplex.Hom.ext
  · exact (isZero_zero (ChainComplex C ℕ)).eq_of_src _ _
  · exact B.partialTotalHom_id 0
  · exact totalRowMap_id B 0

@[reassoc]
theorem partialTotalZeroShortComplexMap_comp
    (φ : B ⟶ B') (ψ : B' ⟶ B'') :
    partialTotalZeroShortComplexMap (φ ≫ ψ) =
      partialTotalZeroShortComplexMap φ ≫
        partialTotalZeroShortComplexMap ψ := by
  apply ShortComplex.Hom.ext
  · exact (isZero_zero (ChainComplex C ℕ)).eq_of_src _ _
  · exact B.partialTotalHom_comp φ ψ 0
  · exact totalRowMap_comp φ ψ 0

end Functoriality

/-- The canonical degreewise splitting of the zero-stage short complex. -/
noncomputable def partialTotalZeroDegreeSplitting (n : ℕ) :
    ((B.partialTotalZeroShortComplex).map
      (HomologicalComplex.eval C (ComplexShape.down ℕ) n)).Splitting where
  r := 0
  s := B.partialTotalRowQuotientSectionF 0 n
  f_r := by
    have hzero : IsZero (B.partialTotalZeroShortComplex.X₁.X n) := by
      change IsZero ((HomologicalComplex.eval C (ComplexShape.down ℕ) n).obj
        (0 : ChainComplex C ℕ))
      exact (HomologicalComplex.eval C (ComplexShape.down ℕ) n).map_isZero
        (isZero_zero (ChainComplex C ℕ))
    exact hzero.eq_of_src _ _
  s_g := B.partialTotalRowQuotientSectionF_comp_quotientF 0 n
  id := by
    rw [zero_comp, zero_add]
    exact B.partialTotalRowQuotientF_zero_comp_sectionF n

/-- Every evaluated zero-stage short complex is short exact. -/
theorem partialTotalZeroDegreewiseShortExact (n : ℕ) :
    ((B.partialTotalZeroShortComplex).map
      (HomologicalComplex.eval C (ComplexShape.down ℕ) n)).ShortExact :=
  (B.partialTotalZeroDegreeSplitting n).shortExact

section Abelian

variable {D : Type u} [Category.{v} D] [Abelian D]

/-- In an abelian category, the zero-stage filtration sequence is short
exact as a sequence of chain complexes. -/
theorem partialTotalZeroShortExact
    (B : HomologicalComplex₂ D (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    B.partialTotalZeroShortComplex.ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    B.partialTotalZeroDegreewiseShortExact n

end Abelian

end HomologicalComplex₂

end
