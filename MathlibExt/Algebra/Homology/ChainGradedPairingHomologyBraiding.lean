/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avocado
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import MathlibExt.Algebra.Homology.ChainGradedPairingHomology

/-!
# Braiding compatibility for homology pairings

This file descends a bidegree braiding formula for chain pairings to the
corresponding pairing on homology.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]


namespace ChainGradedPairing

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C]
  [(curriedTensor C).Additive]
  [∀ Z : C, ((curriedTensor C).obj Z).Additive]
  {K₁ K₂ K₃ L₃ : ChainComplex C ℕ}
  [K₁.HasTensor K₂] [K₂.HasTensor K₁]

omit [MonoidalPreadditive C] in
/-- A bidegree braiding formula for chain pairings descends to their cycle
pairings. -/
lemma pairCycles_braiding
    (P : ChainGradedPairing K₁ K₂ K₃) (D : HomologyDescentData P)
    (Q : ChainGradedPairing K₂ K₁ L₃) (E : HomologyDescentData Q)
    (f : K₃ ⟶ L₃) (z : ℤ) (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q]
    [K₃.HasHomology (p + q)]
    [L₃.HasHomology (q + p)] [L₃.HasHomology (p + q)]
    (hpair : P.pair p q ≫ f.f (p + q) =
      z • ((β_ (K₁.X p) (K₂.X q)).hom ≫ Q.pair q p ≫
        (L₃.XIsoOfEq (Nat.add_comm q p)).hom)) :
    pairCycles P D p q ≫ K₃.cyclesMap f (p + q) =
      z • ((β_ (K₁.cycles p) (K₂.cycles q)).hom ≫
        pairCycles Q E q p ≫
          (cyclesIsoOfEq L₃ (Nat.add_comm q p)).hom) := by
  rw [← cancel_mono (L₃.iCycles (p + q))]
  rw [Category.assoc, K₃.cyclesMap_i]
  rw [pairCycles_i_assoc]
  rw [hpair]
  rw [Preadditive.comp_zsmul]
  rw [Preadditive.zsmul_comp]
  simp only [Category.assoc]
  rw [cyclesIsoOfEq_hom_iCycles]
  rw [pairCycles_i_assoc]
  rw [← BraidedCategory.braiding_naturality_assoc]

/-- A bidegree braiding formula for chain pairings descends to their homology
pairings. -/
lemma pairHomology_braiding
    (P : ChainGradedPairing K₁ K₂ K₃) (D : HomologyDescentData P)
    (Q : ChainGradedPairing K₂ K₁ L₃) (E : HomologyDescentData Q)
    (f : K₃ ⟶ L₃) (z : ℤ) (p q : ℕ)
    [K₁.HasHomology p] [K₂.HasHomology q]
    [K₃.HasHomology (p + q)]
    [L₃.HasHomology (q + p)] [L₃.HasHomology (p + q)]
    [HasBinaryCoproduct
      (K₁.X (p + 1) ⊗ K₂.cycles q)
      (K₁.cycles p ⊗ K₂.X (q + 1))]
    [PreservesColimit
      (parallelPair (K₂.toCycles (q + 1) q) 0)
      (tensorLeft (K₁.homology p))]
    [PreservesColimit
      (parallelPair (K₁.toCycles (p + 1) p) 0)
      (tensorRight (K₂.cycles q))]
    [PreservesColimit
      (parallelPair (K₁.toCycles (p + 1) p) 0)
      (tensorRight (K₂.X (q + 1)))]
    [HasBinaryCoproduct
      (K₂.X (q + 1) ⊗ K₁.cycles p)
      (K₂.cycles q ⊗ K₁.X (p + 1))]
    [PreservesColimit
      (parallelPair (K₁.toCycles (p + 1) p) 0)
      (tensorLeft (K₂.homology q))]
    [PreservesColimit
      (parallelPair (K₂.toCycles (q + 1) q) 0)
      (tensorRight (K₁.cycles p))]
    [PreservesColimit
      (parallelPair (K₂.toCycles (q + 1) q) 0)
      (tensorRight (K₁.X (p + 1)))]
    (hpair : P.pair p q ≫ f.f (p + q) =
      z • ((β_ (K₁.X p) (K₂.X q)).hom ≫ Q.pair q p ≫
        (L₃.XIsoOfEq (Nat.add_comm q p)).hom)) :
    pairHomology P D p q ≫ K₃.homologyMap f (p + q) =
      z • ((β_ (K₁.homology p) (K₂.homology q)).hom ≫
        pairHomology Q E q p ≫
          (homologyIsoOfEq L₃ (Nat.add_comm q p)).hom) := by
  apply tensor_homologyπ_hom_ext (K₁ := K₁) (K₂ := K₂) p q
  rw [Preadditive.comp_zsmul]
  rw [tensor_homologyπ_comp_pairHomology_assoc]
  rw [K₃.homologyπ_naturality]
  rw [BraidedCategory.braiding_naturality_assoc]
  rw [tensor_homologyπ_comp_pairHomology_assoc]
  rw [homologyπ_comp_homologyIsoOfEq_hom]
  rw [← Category.assoc, pairCycles_braiding P D Q E f z p q hpair]
  simp only [Preadditive.zsmul_comp, Category.assoc]

end ChainGradedPairing

end HomologicalComplex

end
