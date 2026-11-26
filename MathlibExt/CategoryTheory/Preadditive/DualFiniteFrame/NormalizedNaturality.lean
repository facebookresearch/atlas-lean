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

public import MathlibExt.CategoryTheory.Preadditive.DualFiniteFrame.Pasting

/-!
# Naturality of normalized dual comparisons

Let P:C → D, R:C → A, S:D → B and Q:A → B form a functor square
ρ:S∘P ≅ Q∘R. Dual functors G,H,J,K on the four categories have
natural comparisons η_R:R∘G ≅ J∘Rᵒᵖ and
η_S:S∘H ≅ K∘Sᵒᵖ. A local comparison at R(M) can then be normalized
around this square to an isomorphism S(P(G(M))) ≅ S(H(P(M))).

For a map φ:M → N, a commuting square between the two local comparisons
gives the corresponding naturality square for the normalized comparisons.
The categories are arbitrary and have independent object and morphism
universes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory Opposite

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
namespace CategoryTheory.DualFiniteFrame

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {A : Type u₃} [Category.{v₃} A] {B : Type u₄} [Category.{v₄} B]

/-- Let P:C → D, R:C → A, S:D → B, Q:A → B and ρ:S∘P ≅ Q∘R.
Let G,H,J,K be contravariant functors on C,D,A,B, with
η_R:R∘G ≅ J∘Rᵒᵖ and η_S:S∘H ≅ K∘Sᵒᵖ.
For φ:M → N and local isomorphisms
c_X:Q(J(R(X))) ≅ K(Q(R(X))) for X=M,N, suppose
c_M∘Q(J((Rφ)ᵒᵖ))=K((Q(Rφ))ᵒᵖ)∘c_N.
Define E_X=η_S,PX⁻¹∘K(ρ_Xᵒᵖ)∘c_X∘Q(η_R,X)∘ρ_GX.
Then E_M∘S(P(G(φᵒᵖ)))=S(H((Pφ)ᵒᵖ))∘E_N. -/
theorem normalizedDualComparison_naturality
    (P : C ⥤ D) (R : C ⥤ A) (S : D ⥤ B) (Q : A ⥤ B) (ρ : P ⋙ S ≅ R ⋙ Q)
    (G : Cᵒᵖ ⥤ C) (H : Dᵒᵖ ⥤ D) (J : Aᵒᵖ ⥤ A) (K : Bᵒᵖ ⥤ B)
    (ηR : G ⋙ R ≅ R.op ⋙ J) (ηS : H ⋙ S ≅ S.op ⋙ K)
    (M N : C) (φ : M ⟶ N)
    (cM : Q.obj (J.obj (op (R.obj M))) ≅ K.obj (op (Q.obj (R.obj M))))
    (cN : Q.obj (J.obj (op (R.obj N))) ≅ K.obj (op (Q.obj (R.obj N))))
    (hc : Q.map (J.map (R.map φ).op) ≫ cM.hom = cN.hom ≫ K.map (Q.map (R.map φ)).op) :
    S.map (P.map (G.map φ.op)) ≫
      (normalizedDualComparison P R S Q ρ G H J K ηR ηS M cM).hom =
    (normalizedDualComparison P R S Q ρ G H J K ηR ηS N cN).hom ≫
      S.map (H.map (P.map φ).op) := by
  have hρG := ρ.hom.naturality (G.map φ.op)
  change S.map (P.map (G.map φ.op)) ≫ ρ.hom.app (G.obj (op M)) =
    ρ.hom.app (G.obj (op N)) ≫ Q.map (R.map (G.map φ.op)) at hρG
  have hR := ηR.hom.naturality φ.op
  change R.map (G.map φ.op) ≫ ηR.hom.app (op M) =
    ηR.hom.app (op N) ≫ J.map (R.map φ).op at hR
  have hS := ηS.inv.naturality (P.map φ).op
  change K.map (S.map (P.map φ)).op ≫ ηS.inv.app (op (P.obj M)) =
    ηS.inv.app (op (P.obj N)) ≫ S.map (H.map (P.map φ).op) at hS
  have hρφ := ρ.hom.naturality φ
  change S.map (P.map φ) ≫ ρ.hom.app N = ρ.hom.app M ≫ Q.map (R.map φ) at hρφ
  have hdual : K.map (Q.map (R.map φ)).op ≫ K.map (ρ.hom.app M).op =
      K.map (ρ.hom.app N).op ≫ K.map (S.map (P.map φ)).op := by
    simpa only [op_comp, Functor.map_comp] using congrArg (fun f => K.map f.op) hρφ.symm
  dsimp only [normalizedDualComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  change S.map (P.map (G.map φ.op)) ≫
      (ρ.hom.app (G.obj (op M)) ≫ Q.map (ηR.hom.app (op M)) ≫ cM.hom ≫
        K.map (ρ.hom.app M).op ≫ ηS.inv.app (op (P.obj M))) =
    (ρ.hom.app (G.obj (op N)) ≫ Q.map (ηR.hom.app (op N)) ≫ cN.hom ≫
      K.map (ρ.hom.app N).op ≫ ηS.inv.app (op (P.obj N))) ≫ S.map (H.map (P.map φ).op)
  simp only [Category.assoc]
  rw [reassoc_of% hρG]
  rw [← Q.map_comp_assoc, hR, Q.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hc]
  rw [reassoc_of% hdual]
  rw [hS]

end CategoryTheory.DualFiniteFrame
