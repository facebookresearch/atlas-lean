/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

import Mathlib.Tactic.Ring

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageConnectingCycles

/-!
# Horizontal maps in direct-column cycle coordinates

Let `K` be a first-quadrant bicomplex in an abelian category. Direct-column cycles at `(p,q)`
use cochain degree `-p-q`. Untwisting and extension compare them with ordinary vertical cycles
in `K_p`.

Transporting the horizontal map from column `p+1` to column `p` gives a direct-column cycle
map. On included representatives, it is the horizontal bicomplex map multiplied by
`(-1)^(q+1)`. Normalizing the cycle isomorphism by `(-1)^(p(-p-q))` cancels its untwisting
scalar, so its cycle inclusion is the direct-column degree identification.
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

/-- The horizontal map between direct-column cycle objects.

Untwist source cycles, identify them with ordinary vertical cycles, apply the horizontal chain
map, and transport back to target direct-column cycles. -/
noncomputable def horizontalDirectColumnHorizontalCyclesMap (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 1)).cycles
        (-((p + 1 : ℕ) : ℤ) - q) ⟶
      (horizontalDirectColumnCochain K p).cycles (-(p : ℤ) - q) :=
  HomologicalComplex.cyclesMap (horizontalDirectColumnUntwistIso K (p + 1)).hom
      (-((p + 1 : ℕ) : ℤ) - q) ≫
    ((K.X (p + 1)).extendCyclesIso
      (ComplexShape.embeddingUpIntLE (-((p + 1 : ℕ) : ℤ)))
      (by simp)).hom ≫
    HomologicalComplex.cyclesMap (K.d (p + 1) p) q ≫
    ((K.X p).extendCyclesIso
      (ComplexShape.embeddingUpIntLE (-(p : ℤ))) (by simp)).inv ≫
    HomologicalComplex.cyclesMap (horizontalDirectColumnUntwistIso K p).inv
      (-(p : ℤ) - q)

/-- The homology projection of a direct-column horizontal cycle map.

The cycle map followed by target homology projection equals source homology projection
followed by the ordinary horizontal homology map conjugated by the direct-column homology
isomorphisms. -/
theorem horizontalDirectColumnHorizontalCyclesMap_homologyπ (p q : ℕ) :
    horizontalDirectColumnHorizontalCyclesMap K p q ≫
        (horizontalDirectColumnCochain K p).homologyπ (-(p : ℤ) - q) =
      (horizontalDirectColumnCochain K (p + 1)).homologyπ
          (-((p + 1 : ℕ) : ℤ) - q) ≫
        (horizontalDirectColumnHomologyIso K (p + 1) q).hom ≫
        HomologicalComplex.homologyMap (K.d (p + 1) p) q ≫
        (horizontalDirectColumnHomologyIso K p q).inv := by
  dsimp [horizontalDirectColumnHorizontalCyclesMap,
    horizontalDirectColumnHomologyIso]
  simp only [Category.assoc]
  rw [← HomologicalComplex.homologyπ_naturality]
  rw [← HomologicalComplex.homologyπ_extendHomologyIso_inv_assoc]
  rw [← HomologicalComplex.homologyπ_naturality_assoc]
  rw [← HomologicalComplex.homologyπ_extendHomologyIso_hom_assoc]
  rw [← HomologicalComplex.homologyπ_naturality_assoc]
  rfl

/-- The representative sign of a direct-column horizontal cycle map.

After target cycle inclusion, the transported map is `(-1)^(q+1)` times the horizontal
bicomplex map through the direct-column degree identifications. -/
theorem horizontalDirectColumnHorizontalCyclesMap_iCycles (p q : ℕ) :
    horizontalDirectColumnHorizontalCyclesMap K p q ≫
        (horizontalDirectColumnCochain K p).iCycles (-(p : ℤ) - q) =
      ((q + 1 : ℕ) : ℤ).negOnePow •
        ((horizontalDirectColumnCochain K (p + 1)).iCycles
            (-((p + 1 : ℕ) : ℤ) - q) ≫
          (horizontalDirectColumnCochainXIso K (p + 1) q).hom ≫
          (K.d (p + 1) p).f q ≫
          (horizontalDirectColumnCochainXIso K p q).inv) := by
  dsimp [horizontalDirectColumnHorizontalCyclesMap]
  simp only [Category.assoc]
  rw [HomologicalComplex.cyclesMap_i]
  rw [HomologicalComplex.extendCyclesIso_inv_iCycles_assoc]
  rw [HomologicalComplex.cyclesMap_i_assoc]
  rw [HomologicalComplex.extendCyclesIso_hom_iCycles_assoc]
  rw [HomologicalComplex.cyclesMap_i_assoc]
  dsimp [horizontalDirectColumnUntwistIso,
    horizontalDirectColumnUntwistXIso]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp,
    Category.comp_id, smul_smul]
  have hsign :
      ((p : ℤ) * (-(p : ℤ) - q)).negOnePow *
          (((p : ℤ) + 1) * (-((p : ℤ) + 1) - q)).negOnePow =
        ((q : ℤ) + 1).negOnePow := by
    rw [← Int.negOnePow_add, Int.negOnePow_eq_iff]
    refine ⟨-((p : ℤ) * p + p + (p : ℤ) * q + q + 1), ?_⟩
    ring
  rw [hsign]
  dsimp [horizontalDirectColumnCochain, horizontalDirectColumnCochainXIso]
  simp

/-- The sign-normalized comparison of direct and vertical column cycles.

Multiply the untwisting cycle comparison by `(-1)^(p(-p-q))` and use extension to identify
direct-column cycles with vertical cycles in degree `q`. -/
noncomputable def horizontalDirectColumnVerticalCyclesIso (p q : ℕ) :
    (horizontalDirectColumnCochain K p).cycles (-(p : ℤ) - q) ≅
      (K.X p).cycles q :=
  (((p : ℤ) * (-(p : ℤ) - q)).negOnePow • Iso.refl _) ≪≫
    HomologicalComplex.cyclesMapIso (horizontalDirectColumnUntwistIso K p)
      (-(p : ℤ) - q) ≪≫
    (K.X p).extendCyclesIso
      (ComplexShape.embeddingUpIntLE (-(p : ℤ))) (by simp)

/-- The inclusion formula for normalized direct-column cycle comparison.

The normalized cycle isomorphism followed by vertical cycle inclusion equals direct-column
cycle inclusion followed by its degree-object isomorphism. -/
theorem horizontalDirectColumnVerticalCyclesIso_hom_iCycles (p q : ℕ) :
    (horizontalDirectColumnVerticalCyclesIso K p q).hom ≫
        (K.X p).iCycles q =
      (horizontalDirectColumnCochain K p).iCycles (-(p : ℤ) - q) ≫
        (horizontalDirectColumnCochainXIso K p q).hom := by
  dsimp [horizontalDirectColumnVerticalCyclesIso]
  simp only [Category.assoc, HomologicalComplex.cyclesMapIso_hom]
  rw [HomologicalComplex.extendCyclesIso_hom_iCycles]
  simp only [Linear.units_smul_comp]
  rw [HomologicalComplex.cyclesMap_i_assoc]
  dsimp [horizontalDirectColumnUntwistIso,
    horizontalDirectColumnUntwistXIso,
    horizontalDirectColumnCochainXIso]
  rw [← Category.assoc]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul,
    smul_smul, Int.units_mul_self, one_smul]
  dsimp [horizontalDirectColumnCochain]
  simp

end HomologicalComplex₂

end
