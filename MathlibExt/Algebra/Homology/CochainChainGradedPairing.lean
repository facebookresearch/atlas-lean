/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Algebra.Homology.GradedPairing

@[expose] public section

noncomputable section

universe v u

open CategoryTheory MonoidalCategory

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- A degree-lowering pairing between a cochain complex and a chain complex.
The boundary formula is the signed cap-product Leibniz rule. -/
structure CochainChainGradedPairing
    (K : CochainComplex C ℕ) (L M : ChainComplex C ℕ) where
  /-- The degree-`p` pairing map. -/
  pair : ∀ p q, K.X p ⊗ L.X (p + q) ⟶ M.X q
  /-- The signed cap-product Leibniz rule. -/
  boundary : ∀ p q,
    pair p (q + 1) ≫ M.d (q + 1) q =
      ((-1 : ℤ) ^ p) •
        (((𝟙 (K.X p) ⊗ₘ L.d (p + (q + 1)) (p + q)) ≫ pair p q) -
          ((K.d p (p + 1) ⊗ₘ
              (L.XIsoOfEq (show (p + 1) + q = p + (q + 1) by omega)).inv) ≫
            pair (p + 1) q))

namespace CochainChainGradedPairing

variable [MonoidalPreadditive C]
  {K : CochainComplex C ℕ} {L M : ChainComplex C ℕ}

lemma pairCycles_d (P : CochainChainGradedPairing K L M) (p q : ℕ)
    [K.HasHomology p] [L.HasHomology (p + q)] :
    ((K.iCycles p ⊗ₘ L.iCycles (p + q)) ≫ P.pair p q) ≫
        M.d q ((ComplexShape.down ℕ).next q) = 0 := by
  cases q with
  | zero =>
      rw [M.shape 0 ((ComplexShape.down ℕ).next 0) (by simp [ComplexShape.down])]
      simp
  | succ q =>
      rw [show (ComplexShape.down ℕ).next (q + 1) = q by simp]
      simp only [Category.assoc, P.boundary]
      rw [Preadditive.comp_zsmul, Preadditive.comp_sub]
      have hleft :
          (K.iCycles p ⊗ₘ L.iCycles (p + (q + 1))) ≫
              (𝟙 (K.X p) ⊗ₘ L.d (p + (q + 1)) (p + q)) = 0 := by
        rw [MonoidalCategory.tensorHom_comp_tensorHom, L.iCycles_d]
        simp
      have hright :
          (K.iCycles p ⊗ₘ L.iCycles (p + (q + 1))) ≫
              (K.d p (p + 1) ⊗ₘ
                (L.XIsoOfEq
                  (show (p + 1) + q = p + (q + 1) by omega)).inv) = 0 := by
        rw [MonoidalCategory.tensorHom_comp_tensorHom, K.iCycles_d]
        simp
      simp only [← Category.assoc, hleft, hright, Limits.zero_comp, sub_self,
        smul_zero]

/-- Pair cocycles with cycles, before quotienting either input by boundaries. -/
noncomputable def pairCycles (P : CochainChainGradedPairing K L M) (p q : ℕ)
    [K.HasHomology p] [L.HasHomology (p + q)] [M.HasHomology q] :
    K.cycles p ⊗ L.cycles (p + q) ⟶ M.cycles q :=
  M.liftCycles
    ((K.iCycles p ⊗ₘ L.iCycles (p + q)) ≫ P.pair p q)
    ((ComplexShape.down ℕ).next q) rfl (P.pairCycles_d p q)

@[reassoc (attr := simp)]
lemma pairCycles_i (P : CochainChainGradedPairing K L M) (p q : ℕ)
    [K.HasHomology p] [L.HasHomology (p + q)] [M.HasHomology q] :
    P.pairCycles p q ≫ M.iCycles q =
      (K.iCycles p ⊗ₘ L.iCycles (p + q)) ≫ P.pair p q :=
  M.liftCycles_i _ _ rfl _

omit [MonoidalPreadditive C] in
/-- Cochain-side reading of the Leibniz law: the cochain-differential cap
is the chain-boundary cap minus the signed output boundary. -/
lemma boundary_cochainSide (P : CochainChainGradedPairing K L M) (p q : ℕ) :
    ((K.d p (p + 1) ⊗ₘ
          (L.XIsoOfEq (show (p + 1) + q = p + (q + 1) by omega)).inv) ≫
        P.pair (p + 1) q) =
      (((𝟙 (K.X p) ⊗ₘ L.d (p + (q + 1)) (p + q)) ≫ P.pair p q) -
        ((-1 : ℤ) ^ p) • (P.pair p (q + 1) ≫ M.d (q + 1) q)) := by
  have h := P.boundary p q
  have hs : ((-1 : ℤ) ^ p) * ((-1 : ℤ) ^ p) = 1 := by
    rw [← pow_add, ← two_mul]
    simp
  have hkey : ((-1 : ℤ) ^ p) • (P.pair p (q + 1) ≫ M.d (q + 1) q) =
      (((𝟙 (K.X p) ⊗ₘ L.d (p + (q + 1)) (p + q)) ≫ P.pair p q) -
        ((K.d p (p + 1) ⊗ₘ
            (L.XIsoOfEq (show (p + 1) + q = p + (q + 1) by omega)).inv) ≫
          P.pair (p + 1) q)) := by
    rw [h, smul_smul, hs, one_smul]
  rw [hkey]
  abel

omit [MonoidalPreadditive C] in
/-- Chain-side reading of the Leibniz law: the chain-boundary cap is the
signed output boundary plus the cochain-differential cap. -/
lemma boundary_chainSide (P : CochainChainGradedPairing K L M) (p q : ℕ) :
    (((𝟙 (K.X p) ⊗ₘ L.d (p + (q + 1)) (p + q)) ≫ P.pair p q) =
      ((-1 : ℤ) ^ p) • (P.pair p (q + 1) ≫ M.d (q + 1) q) +
        ((K.d p (p + 1) ⊗ₘ
            (L.XIsoOfEq (show (p + 1) + q = p + (q + 1) by omega)).inv) ≫
          P.pair (p + 1) q)) := by
  have h := P.boundary p q
  have hs : ((-1 : ℤ) ^ p) * ((-1 : ℤ) ^ p) = 1 := by
    rw [← pow_add, ← two_mul]
    simp
  have hkey : ((-1 : ℤ) ^ p) • (P.pair p (q + 1) ≫ M.d (q + 1) q) =
      (((𝟙 (K.X p) ⊗ₘ L.d (p + (q + 1)) (p + q)) ≫ P.pair p q) -
        ((K.d p (p + 1) ⊗ₘ
            (L.XIsoOfEq (show (p + 1) + q = p + (q + 1) by omega)).inv) ≫
          P.pair (p + 1) q)) := by
    rw [h, smul_smul, hs, one_smul]
  rw [hkey]
  abel

end CochainChainGradedPairing

end HomologicalComplex
