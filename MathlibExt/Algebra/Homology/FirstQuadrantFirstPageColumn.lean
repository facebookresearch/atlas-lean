/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import MathlibExt.Algebra.Homology.FirstQuadrantGradedPieceCokernelIso

/-!
# The first page as vertical-column homology

The mapping cone of two consecutive horizontal filtration stages maps
quasi-isomorphically to their direct-column cokernel.  After removing the
constant totalization sign, the resulting homology object is the ordinary
vertical homology of that column.  This identifies every object on the first
page of the first-quadrant spectral sequence.  Compatibility with the actual
first-page differential is proved in `FirstQuadrantFirstPageDifferential`.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- The canonical map from the relative mapping cone to the direct shifted
column. -/
noncomputable def horizontalFirstPageMappingConeToDirectColumn (p : ℕ) :
    CochainComplex.mappingCone (horizontalFirstPageFiltrationMap K p) ⟶
      horizontalDirectColumnCochain K p :=
  CochainComplex.mappingCone.descShortComplex
    (horizontalFirstPageDirectColumnShortComplex K p)

/-- The mapping-cone comparison is a quasi-isomorphism. -/
theorem horizontalFirstPageMappingConeToDirectColumn_quasiIso (p : ℕ) :
    QuasiIso (horizontalFirstPageMappingConeToDirectColumn K p) :=
  CochainComplex.mappingCone.quasiIso_descShortComplex
    (horizontalFirstPageDirectColumnShortExact K p)

/-- Relative mapping-cone homology is the homology of the direct shifted
column. -/
noncomputable def horizontalFirstPageRelativeHomologyDirectColumnIso
    (p q : ℕ) :
    horizontalFirstPageRelativeHomology K p q ≅
      (horizontalDirectColumnCochain K p).homology (-(p : ℤ) - q) := by
  let n : ℤ := -(p : ℤ) - q
  let M := CochainComplex.mappingCone (horizontalFirstPageFiltrationMap K p)
  let g := horizontalFirstPageMappingConeToDirectColumn K p
  let hg : QuasiIso g :=
    horizontalFirstPageMappingConeToDirectColumn_quasiIso K p
  let _ := hg
  change ((HomotopyCategory.homologyFunctor C
      (ComplexShape.up ℤ) n).obj
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj M)) ≅
    (horizontalDirectColumnCochain K p).homology n
  exact (HomotopyCategory.homologyFunctorFactors C
      (ComplexShape.up ℤ) n).app M ≪≫
    isoOfQuasiIsoAt g n

/-- Degreewise sign isomorphism from the direct-column presentation to the
unscaled extension of the vertical column. -/
noncomputable def horizontalDirectColumnUntwistXIso (p : ℕ) (i : ℤ) :
    (horizontalDirectColumnCochain K p).X i ≅
      ((K.X p).extend
        (ComplexShape.embeddingUpIntLE (-(p : ℤ)))).X i := by
  change ((K.X p).extend
      (ComplexShape.embeddingUpIntLE (-(p : ℤ)))).X i ≅
    ((K.X p).extend
      (ComplexShape.embeddingUpIntLE (-(p : ℤ)))).X i
  exact
    { hom := ((p : ℤ) * i).negOnePow • 𝟙 _
      inv := ((p : ℤ) * i).negOnePow • 𝟙 _
      hom_inv_id := by
        rw [Linear.units_smul_comp (R := ℤ), Linear.comp_units_smul (R := ℤ),
          Category.id_comp, smul_smul, Int.units_mul_self, one_smul]
      inv_hom_id := by
        rw [Linear.units_smul_comp (R := ℤ), Linear.comp_units_smul (R := ℤ),
          Category.id_comp, smul_smul, Int.units_mul_self, one_smul] }

/-- Multiplication in degree `i` by `(-1)^(p*i)` removes the constant
`(-1)^p` from the direct-column differential. -/
noncomputable def horizontalDirectColumnUntwistIso (p : ℕ) :
    horizontalDirectColumnCochain K p ≅
      (K.X p).extend (ComplexShape.embeddingUpIntLE (-(p : ℤ))) :=
  HomologicalComplex.Hom.isoOfComponents
    (horizontalDirectColumnUntwistXIso K p)
    (by
      intro i j hij
      dsimp [horizontalDirectColumnUntwistXIso,
        horizontalDirectColumnCochain]
      rw [Linear.units_smul_comp (R := ℤ),
        Linear.comp_units_smul (R := ℤ), Category.id_comp,
        Category.comp_id, smul_smul]
      have hij' : i + 1 = j := by
        simpa only [ComplexShape.up_Rel] using hij
      subst j
      rw [mul_add, mul_one, Int.negOnePow_add, mul_assoc,
        Int.units_mul_self, mul_one])

/-- Direct-column homology in total degree `-(p+q)` is vertical homology in
degree `q`. -/
noncomputable def horizontalDirectColumnHomologyIso (p q : ℕ) :
    (horizontalDirectColumnCochain K p).homology (-(p : ℤ) - q) ≅
      (K.X p).homology q :=
  HomologicalComplex.homologyMapIso (horizontalDirectColumnUntwistIso K p)
      (-(p : ℤ) - q) ≪≫
    (K.X p).extendHomologyIso
      (ComplexShape.embeddingUpIntLE (-(p : ℤ))) (by simp)

/-- Relative homology of consecutive horizontal filtration stages is the
vertical homology of the new column. -/
noncomputable def horizontalFirstPageRelativeHomologyVerticalIso (p q : ℕ) :
    horizontalFirstPageRelativeHomology K p q ≅
      (K.X p).homology q :=
  horizontalFirstPageRelativeHomologyDirectColumnIso K p q ≪≫
    horizontalDirectColumnHomologyIso K p q

/-- Objectwise identification of the first spectral-sequence page with
vertical-column homology. -/
noncomputable def horizontalFirstPageVerticalHomologyIso (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).X (p, q) ≅
      (K.X p).homology q :=
  horizontalFirstPageXIso K p q ≪≫
    horizontalFirstPageRelativeHomologyVerticalIso K p q

end HomologicalComplex₂

end
