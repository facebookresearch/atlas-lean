/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Homology.GradedPairingHomology
public import MathlibExt.Algebra.Category.Grp.MonoidalPreadditive
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits

/-!
# Transport of a graded pairing by cochain isomorphisms

For nonnegative cochain complexes of abelian groups, a graded pairing
P:K₁⊗K₂ → K₃ and isomorphisms a:K₁ ≅ L₁, b:K₂ ≅ L₂, c:K₃ ≅ L₃
determine the transported pairing Q=c ∘ P ∘ (a⁻¹⊗b⁻¹).
The cohomology pairings commute with the induced maps H(a), H(b), H(c)
in every bidegree (p,q), with total degree p+q and tensor product over ℤ.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe s u w
open CategoryTheory MonoidalCategory

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency.types false in
/-- Let K₁,K₂,K₃ and L₁,L₂,L₃ be nonnegative cochain complexes of abelian
groups, P a graded pairing K₁⊗K₂ → K₃, and a:K₁ ≅ L₁,
b:K₂ ≅ L₂, c:K₃ ≅ L₃ cochain isomorphisms. Define the transported
pairing Q=c ∘ P ∘ (a⁻¹⊗b⁻¹). For p,q∈ℕ its cohomology
naturality square is
H^{p+q}(c) ∘ P_H = Q_H ∘ (Hᵖ(a)⊗Hᑫ(b)). -/
theorem originalGradedPairing_homology_iso_square
    {K₁ K₂ K₃ L₁ L₂ L₃ : CochainComplex AddCommGrpCat.{s} ℕ}
    (P : HomologicalComplex.CochainGradedPairing K₁ K₂ K₃)
    (a : K₁ ≅ L₁) (b : K₂ ≅ L₂) (c : K₃ ≅ L₃) (p q : ℕ) :
    (HomologicalComplex.homologyMap a.hom p ⊗ₘ HomologicalComplex.homologyMap b.hom q) ≫
        (P.whisker a.inv b.inv c.hom).pairHomology p q =
      P.pairHomology p q ≫ HomologicalComplex.homologyMap c.hom (p + q) := by
  apply HomologicalComplex.CochainGradedPairing.pairHomology_naturality
    P (P.whisker a.inv b.inv c.hom) a.hom b.hom c.hom
  intro i j
  rw [HomologicalComplex.CochainGradedPairing.whisker_pair]
  rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
  have ha : a.hom.f i ≫ a.inv.f i = 𝟙 _ :=
    congrArg (fun f : K₁ ⟶ K₁ => f.f i) a.hom_inv_id
  have hb : b.hom.f j ≫ b.inv.f j = 𝟙 _ :=
    congrArg (fun f : K₂ ⟶ K₂ => f.f j) b.hom_inv_id
  rw [ha, hb]
  simp only [tensorHom_id, id_whiskerRight, Category.id_comp]

end CategoryTheory
