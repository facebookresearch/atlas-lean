/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import MathlibExt.Algebra.Homology.FirstQuadrantGradedPieceCokernelIso

/-!
# The first page as vertical homology of a signed shifted column

Let K be a nonnegative homological bicomplex in an abelian category C.
The consecutive filtration map F_(p−1) → F_p has cokernel D_p, the
direct cochain presentation of column p. It has K_(p,q) in degree
i=−p−q and zero objects for i>−p; its differential is (−1)^p times
the extended vertical differential.

The canonical map Cone(F_(p−1) → F_p) → D_p is a quasi-isomorphism.
Multiplication in cochain degree i by (−1)^(p i) gives an isomorphism
from D_p to the unscaled extension of the vertical column K_p.
Consequently
E¹_(p,q) ≅ H_(−p−q)(D_p) ≅ H_q(K_p)
for every p,q ≥ 0. The category object and morphism universes
remain independent.
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

/-- For a nonnegative homological bicomplex K in an abelian
category and p ≥ 0, the direct-column short exact sequence gives
the map Cone(F_(p−1) → F_p) → D_p.
It projects the upper filtration component to the column-p
cokernel and annihilates the lower cone component. -/
noncomputable def horizontalFirstPageMappingConeToDirectColumn (p : ℕ) :
    CochainComplex.mappingCone (horizontalFirstPageFiltrationMap K p) ⟶
      horizontalDirectColumnCochain K p :=
  CochainComplex.mappingCone.descShortComplex
    (horizontalFirstPageDirectColumnShortComplex K p)

/-- For a nonnegative homological bicomplex K in an abelian
category and p ≥ 0, the canonical projection
Cone(F_(p−1) → F_p) → D_p is a quasi-isomorphism.
Here D_p is the direct signed shifted-column cokernel of the
consecutive filtration inclusion. -/
theorem horizontalFirstPageMappingConeToDirectColumn_quasiIso (p : ℕ) :
    QuasiIso (horizontalFirstPageMappingConeToDirectColumn K p) :=
  CochainComplex.mappingCone.quasiIso_descShortComplex
    (horizontalFirstPageDirectColumnShortExact K p)

/-- For a nonnegative homological bicomplex K in an abelian
category and p,q ≥ 0, the mapping-cone comparison induces
H_(−p−q)(Cone(F_(p−1) → F_p)) ≅ H_(−p−q)(D_p).
The map is the homology map of the projection to the direct column. -/
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

/-- For a nonnegative homological bicomplex K in an abelian
category, column p and i ∈ ℤ, the degree-i direct-column object
is isomorphic to the degree-i object of the unscaled extension
of K_p along q ↦ −p−q. The forward and inverse maps are both
(−1)^(p i) times the identity. -/
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

/-- For a nonnegative homological bicomplex K in an abelian
category and p ≥ 0, multiplication in cochain degree i by
(−1)^(p i) identifies D_p with the extension of the vertical
chain column K_p along q ↦ −p−q.
It removes the constant (−1)^p multiplier from the differential,
and its inverse uses the same degreewise signs. -/
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

/-- For a nonnegative homological bicomplex K in an abelian
category and p,q ≥ 0, sign removal and extension homology give
H_(−p−q)(D_p) ≅ H_q(K_p).
The direct column has term K_(p,q) at degree −p−q and differential
scaled by (−1)^p before this comparison. -/
noncomputable def horizontalDirectColumnHomologyIso (p q : ℕ) :
    (horizontalDirectColumnCochain K p).homology (-(p : ℤ) - q) ≅
      (K.X p).homology q :=
  HomologicalComplex.homologyMapIso (horizontalDirectColumnUntwistIso K p)
      (-(p : ℤ) - q) ≪≫
    (K.X p).extendHomologyIso
      (ComplexShape.embeddingUpIntLE (-(p : ℤ))) (by simp)

/-- For a nonnegative homological bicomplex K in an abelian
category and p,q ≥ 0, the composite of the relative-cone projection,
column sign removal and extension comparison gives
H_(−p−q)(Cone(F_(p−1) → F_p)) ≅ H_q(K_p). -/
noncomputable def horizontalFirstPageRelativeHomologyVerticalIso (p q : ℕ) :
    horizontalFirstPageRelativeHomology K p q ≅
      (K.X p).homology q :=
  horizontalFirstPageRelativeHomologyDirectColumnIso K p q ≪≫
    horizontalDirectColumnHomologyIso K p q

/-- For a nonnegative homological bicomplex K in an abelian
category C, the canonical first-page object comparison is
E¹_(p,q) ≅ H_q(K_p), for all p,q ≥ 0.
It passes through the relative cone of F_(p−1) → F_p and the
signed direct-column presentation D_p. -/
noncomputable def horizontalFirstPageVerticalHomologyIso (p q : ℕ) :
    ((horizontalFirstQuadrantSpectralSequence K).page 1).X (p, q) ≅
      (K.X p).homology q :=
  horizontalFirstPageXIso K p q ≪≫
    horizontalFirstPageRelativeHomologyVerticalIso K p q

end HomologicalComplex₂

end
