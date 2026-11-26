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
# Braiding squares descend from chain pairings to cycles and homology

Let C be a preadditive braided monoidal category with tensor additive
in both variables. Let P pair K₁,K₂ into K₃ and Q pair K₂,K₁ into L₃,
for ℕ-indexed chain complexes whose indicated tensor products exist.
Give P and Q descent data: they send pairs of cycles to cycles,
and a boundary in either variable factors through a target boundary.

Fix p,q ≥ 0, an integer z and a chain map f : K₃ → L₃. Assume the
bidegree square
f_(p+q) ∘ P_(p,q) = z · (η_X ∘ Q_(q,p) ∘ β_X),
where β swaps the inputs and η reindexes L₃ from q+p to p+q.
When the indicated homologies exist, the same square holds for the
cycle pairings.

For homology pairings, also assume the two binary coproducts of the
boundary–cycle tensor objects exist, and that the six specified
tensor functors preserve the cycle-valued boundary cokernels.
Then H_(p+q)(f) ∘ P_H = z · (η_H ∘ Q_H ∘ β_H).
In particular the coefficient z, including a Koszul sign when chosen,
is preserved by descent.
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
/-- In a preadditive braided monoidal category with tensor
additive in both variables, let P : K₁,K₂ → K₃ and
Q : K₂,K₁ → L₃ be chain pairings with descent data, and assume
the two input tensor complexes exist. Fix p,q ≥ 0, z ∈ ℤ and
f : K₃ → L₃. Assume H_p(K₁), H_q(K₂), H_(p+q)(K₃) and
H_(q+p)(L₃), H_(p+q)(L₃) exist.
If f_(p+q) ∘ P_(p,q) = z·(η_X ∘ Q_(q,p) ∘ β_X), then
Z_(p+q)(f) ∘ P_Z = z·(η_Z ∘ Q_Z ∘ β_Z).
The maps η transport the equality q+p = p+q; the input square
is the premise and the cycle square is the conclusion. -/
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

/-- In a preadditive braided monoidal category with additive
tensor, let P : K₁,K₂ → K₃ and Q : K₂,K₁ → L₃ be chain pairings
with cycle and boundary descent data, and suppose both input tensor
complexes exist. Fix p,q ≥ 0, z ∈ ℤ and f : K₃ → L₃. Assume
the homologies of K₁ at p, K₂ at q, K₃ at p+q and L₃ at q+p,p+q
exist. Write Z₁ = Z_p(K₁), Z₂ = Z_q(K₂), H₁ = H_p(K₁), H₂ = H_q(K₂).

Assume the coproducts (K₁_(p+1)⊗Z₂) ⨁ (Z₁⊗K₂_(q+1)) and
(K₂_(q+1)⊗Z₁) ⨁ (Z₂⊗K₁_(p+1)) exist. Require the cokernel of
K₁_(p+1) → Z₁ to be preserved by −⊗Z₂, −⊗K₂_(q+1), H₂⊗−,
and the cokernel of K₂_(q+1) → Z₂ by −⊗Z₁, −⊗K₁_(p+1), H₁⊗−.
If f_(p+q) ∘ P_(p,q) = z·(η_X ∘ Q_(q,p) ∘ β_X), then
H_(p+q)(f) ∘ P_H = z·(η_H ∘ Q_H ∘ β_H).
Each η transports q+p = p+q, and β is the braiding at the
corresponding chain or homology objects. -/
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
