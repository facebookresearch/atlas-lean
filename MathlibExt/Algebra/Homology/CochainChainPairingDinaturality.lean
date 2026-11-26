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

public import MathlibExt.Algebra.Homology.CochainChainGradedPairingHomology
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Dinaturality of cochain–chain pairings on homology

Let R : Type u be a commutative ring and take cochain and chain complexes in ModuleCat.{u} R
indexed by ℕ. A cochain–chain pairing has components K^p⊗L_{p+q} → M_q and induces
H^p(K)⊗H_{p+q}(L) → H_q(M).

For a cochain map f_K : K → K′ and an oppositely directed chain map f_L : L′ → L,
compatibility of two pairings on chain terms implies the corresponding dinaturality equation
on homology.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace HomologicalComplex.CochainChainGradedPairing

variable (R : Type u) [CommRing R]

/-- Let R : Type u be a commutative ring, K,K′ cochain complexes and L,L′,M chain complexes in
ModuleCat.{u} R indexed by ℕ. Let P,Q have pairing maps K^p⊗L_{p+q} → M_q and K′^p⊗L′_{p+q} →
M_q. Suppose f_K : K → K′ and f_L : L′ → L satisfy (f_K,p⊗id) ≫ Q_{p,q} = (id⊗f_L,p+q) ≫
P_{p,q} for all p,q. Then the same equation holds on homology, with H^p(f_K), H_{p+q}(f_L),
and the induced pairings into H_q(M). -/
theorem pairHomology_dinaturality
    {K K' : CochainComplex (ModuleCat.{u} R) ℕ}
    {L L' M : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CochainChainGradedPairing K L M)
    (Q : CochainChainGradedPairing K' L' M)
    (fK : K ⟶ K') (fL : L' ⟶ L)
    (hpair : ∀ p q,
      (fK.f p ⊗ₘ 𝟙 (L'.X (p + q))) ≫ Q.pair p q =
        (𝟙 (K.X p) ⊗ₘ fL.f (p + q)) ≫ P.pair p q)
    (p q : ℕ) :
    (K.homologyMap fK p ⊗ₘ 𝟙 (L'.homology (p + q))) ≫
        Q.pairHomology p q =
      (𝟙 (K.homology p) ⊗ₘ L'.homologyMap fL (p + q)) ≫
        P.pairHomology p q := by
  have hcycles :
      (K.cyclesMap fK p ⊗ₘ 𝟙 (L'.cycles (p + q))) ≫
          Q.pairCycles p q =
        (𝟙 (K.cycles p) ⊗ₘ L'.cyclesMap fL (p + q)) ≫
          P.pairCycles p q := by
    apply (cancel_mono (M.iCycles q)).1
    simp only [Category.assoc]
    rw [Q.pairCycles_i, P.pairCycles_i]
    rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
    rw [cyclesMap_i, Category.id_comp]
    rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
    rw [cyclesMap_i, Category.id_comp]
    have h := congrArg
      (fun k => (K.iCycles p ⊗ₘ L'.iCycles (p + q)) ≫ k)
      (hpair p q)
    simpa only [Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      Category.comp_id] using h
  apply tensor_homologyπ_hom_ext (K := K) (L := L') p q
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  rw [homologyπ_naturality, Category.comp_id]
  rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  rw [Category.comp_id, homologyπ_naturality]
  calc
    ((K.cyclesMap fK p ≫ K'.homologyπ p) ⊗ₘ
          L'.homologyπ (p + q)) ≫ Q.pairHomology p q =
        (K.cyclesMap fK p ⊗ₘ 𝟙 _) ≫
          (K'.homologyπ p ⊗ₘ L'.homologyπ (p + q)) ≫
          Q.pairHomology p q := by
      rw [← Category.assoc,
        MonoidalCategory.tensorHom_comp_tensorHom]
      simp
    _ = (K.cyclesMap fK p ⊗ₘ 𝟙 _) ≫
          Q.pairCycles p q ≫ M.homologyπ q := by
      simp only [Q.tensor_homologyπ_comp_pairHomology]
    _ = (𝟙 _ ⊗ₘ L'.cyclesMap fL (p + q)) ≫
          P.pairCycles p q ≫ M.homologyπ q := by
      simpa only [Category.assoc] using
        congrArg (fun k => k ≫ M.homologyπ q) hcycles
    _ = (𝟙 _ ⊗ₘ L'.cyclesMap fL (p + q)) ≫
          (K.homologyπ p ⊗ₘ L.homologyπ (p + q)) ≫
          P.pairHomology p q := by
      simp only [P.tensor_homologyπ_comp_pairHomology]
    _ = (K.homologyπ p ⊗ₘ
          (L'.cyclesMap fL (p + q) ≫ L.homologyπ (p + q))) ≫
          P.pairHomology p q := by
      rw [← Category.assoc,
        MonoidalCategory.tensorHom_comp_tensorHom]
      simp

end HomologicalComplex.CochainChainGradedPairing

end
