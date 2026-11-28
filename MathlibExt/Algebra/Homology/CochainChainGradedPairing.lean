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

/-!
# Cochain–chain pairings and the signed boundary rule

Let C be a preadditive monoidal category, K a cochain complex indexed by ℕ, and L,M chain
complexes indexed by ℕ. A cochain–chain graded pairing has maps P_{p,q} : K^p⊗L_{p+q} → M_q.

Its boundary law is d_M P_{p,q+1}=(-1)^p(P_{p,q}(id⊗d_L)−P_{p+1,q}(d_K⊗id)), using the
canonical equality (p+1)+q=p+(q+1) to identify the chain term in the second summand. With
additive tensor functors, cocycles paired with cycles give cycles. The boundary rule can also
be rearranged separately in either input differential.
-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory MonoidalCategory

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- Let C be a preadditive monoidal category, K an ℕ-indexed cochain complex, and L,M ℕ-indexed
chain complexes. A cochain–chain graded pairing consists of maps P_{p,q} : K^p⊗L_{p+q} → M_q
satisfying d_M P_{p,q+1}=(-1)^p(P_{p,q}(id⊗d_L)−P_{p+1,q}(d_K⊗id)). The chain object in the
cochain-differential summand is transported along (p+1)+q=p+(q+1). -/
structure CochainChainGradedPairing
    (K : CochainComplex C ℕ) (L M : ChainComplex C ℕ) where
  /-- For a cochain–chain graded pairing in a preadditive monoidal category C, the component at p,q
∈ ℕ is a morphism K^p⊗L_{p+q} → M_q. It lowers the chain degree by the cochain degree p, with
cochain input first in the tensor product. -/
  pair : ∀ p q, K.X p ⊗ L.X (p + q) ⟶ M.X q
  /-- Let P be a cochain–chain pairing in a preadditive monoidal category. For p,q ∈ ℕ and e :
L_{(p+1)+q} ≅ L_{p+(q+1)} the index-equality isomorphism, P_{p,q+1}≫d_M
=(-1)^p·((id⊗d_L)≫P_{p,q}−(d_K⊗e.inv)≫P_{p+1,q}). The source is K^p⊗L_{p+(q+1)} and the target
is M_q; the minus sign is on the cochain-differential term. -/
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

/-- Let C be preadditive and monoidal with additive tensor functors, and P a pairing of K,L,M. For
p,q ∈ ℕ assume homology exists for K at p, L at p+q, and M at q. Restricting P_{p,q} to the
cocycle and cycle inclusions gives a map Z^p(K)⊗Z_{p+q}(L) → Z_q(M). The signed boundary rule
shows its composite with the output differential is zero. -/
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
/-- For a cochain–chain pairing P in a preadditive monoidal category and p,q ∈ ℕ, let e identify
L_{(p+1)+q} with L_{p+(q+1)}. Then (d_K⊗e.inv)≫P_{p+1,q} =
(id⊗d_L)≫P_{p,q}−(-1)^p·(P_{p,q+1}≫d_M). This is the rearranged signed boundary equation on
K^p⊗L_{p+(q+1)}. -/
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
/-- Let P be a cochain–chain pairing in a preadditive monoidal category and p,q ∈ ℕ. With e :
L_{(p+1)+q} ≅ L_{p+(q+1)}, one has (id⊗d_L)≫P_{p,q} =
(-1)^p·(P_{p,q+1}≫d_M)+(d_K⊗e.inv)≫P_{p+1,q}. Both summands have source K^p⊗L_{p+(q+1)} and
target M_q. -/
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
