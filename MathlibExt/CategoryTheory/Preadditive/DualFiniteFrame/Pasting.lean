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

public import Mathlib.CategoryTheory.Preadditive.Opposite
public import Mathlib.Tactic.CategoryTheory.Reassoc

/-!
# Normalization and pasting of local dual comparisons

For a functor square ρ:S∘P ≅ Q∘R, duality comparisons for R and S
turn a local comparison c:Q(J(R(M))) ≅ K(Q(R(M))) into
S(P(G(M))) ≅ S(H(P(M))).
The normalized map is the composite
η_S,PM⁻¹∘K(ρ_Mᵒᵖ)∘c∘Q(η_R,M)∘ρ_GM.

For two composable functor squares, compatible square comparisons,
restriction-duality comparisons and local comparisons identify successive
normalization with normalization around the outer square.
All six categories have independent object and morphism universes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory Opposite

universe u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆
namespace CategoryTheory.DualFiniteFrame

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {A : Type u₃} [Category.{v₃} A] {B : Type u₄} [Category.{v₄} B]
  {A' : Type u₅} [Category.{v₅} A'] {B' : Type u₆} [Category.{v₆} B']

/-- Let P:C → D, R:C → A, S:D → B, Q:A → B and ρ:S∘P ≅ Q∘R.
For contravariant functors G,H,J,K on C,D,A,B, take
η_R:R∘G ≅ J∘Rᵒᵖ, η_S:S∘H ≅ K∘Sᵒᵖ and
c:Q(J(R(M))) ≅ K(Q(R(M))).
The normalized isomorphism S(P(G(M))) ≅ S(H(P(M))) has forward
composite η_S,PM⁻¹∘K(ρ_Mᵒᵖ)∘c∘Q(η_R,M)∘ρ_GM. -/
def normalizedDualComparison (P : C ⥤ D) (R : C ⥤ A) (S : D ⥤ B) (Q : A ⥤ B)
    (ρ : P ⋙ S ≅ R ⋙ Q)
    (G : Cᵒᵖ ⥤ C) (H : Dᵒᵖ ⥤ D) (J : Aᵒᵖ ⥤ A) (K : Bᵒᵖ ⥤ B)
    (ηR : G ⋙ R ≅ R.op ⋙ J) (ηS : H ⋙ S ≅ S.op ⋙ K) (M : C)
    (c : Q.obj (J.obj (op (R.obj M))) ≅ K.obj (op (Q.obj (R.obj M)))) :
    S.obj (P.obj (G.obj (op M))) ≅ S.obj (H.obj (op (P.obj M))) :=
  ρ.app (G.obj (op M)) ≪≫ Q.mapIso (ηR.app (op M)) ≪≫ c ≪≫
    K.mapIso (ρ.app M).op ≪≫ (ηS.app (op (P.obj M))).symm

/-- Consider categories C,D,A,B,A′,B′ and functors
P:C → D, R:C → A, S:D → B, Q:A → B,
R′:A → A′, S′:B → B′, Q′:A′ → B′, R₁:C → A′, S₁:D → B′.
Take squares ρ:S∘P ≅ Q∘R, ρ′:S′∘Q ≅ Q′∘R′,
ρ₁:S₁∘P ≅ Q′∘R₁ and δ_R:R′∘R ≅ R₁, δ_S:S′∘S ≅ S₁.
Let G,H,J,K,J′,K′ be the six contravariant functors and η_X the natural
comparison X∘dual_source ≅ dual_target∘Xᵒᵖ for
X=R,S,R′,S′,R₁,S₁. At M choose c:Q(J(R(M))) ≅ K(Q(R(M))),
c′:Q′(J′(R′(R(M)))) ≅ K′(Q′(R′(R(M)))), and
c₁:Q′(J′(R₁(M))) ≅ K′(Q′(R₁(M))).

Assume the following compatibility equations, using forward maps:

ρ₁,N=Q′(δ_R,N)∘ρ′,RN∘S′(ρ_N)∘δ_S,PN⁻¹ for every N;
η_R′,RM∘R′(η_R,M)=J′(δ_R,Mᵒᵖ)∘η_R₁,M∘δ_R,GM;
η_S′,SPM∘S′(η_S,PM)=K′(δ_S,PMᵒᵖ)∘η_S₁,PM∘δ_S,HPM;
η_S′,QRM∘S′(c)=K′(ρ′,RMᵒᵖ)∘c′∘Q′(η_R′,RM)∘ρ′,JRM;
c′∘Q′(J′(δ_R,Mᵒᵖ))=K′((Q′(δ_R,M))ᵒᵖ)∘c₁.

Then normalization around the outer square equals
δ_S,HPM∘S′(E_M)∘δ_S,PGM⁻¹, where E_M is the normalized comparison
for the first square and c. -/
theorem normalizedDualComparison_pasting
    (P : C ⥤ D) (R : C ⥤ A) (S : D ⥤ B) (Q : A ⥤ B)
    (R' : A ⥤ A') (S' : B ⥤ B') (Q' : A' ⥤ B') (R₁ : C ⥤ A') (S₁ : D ⥤ B')
    (ρ : P ⋙ S ≅ R ⋙ Q) (ρ' : Q ⋙ S' ≅ R' ⋙ Q') (ρ₁ : P ⋙ S₁ ≅ R₁ ⋙ Q')
    (δR : R ⋙ R' ≅ R₁) (δS : S ⋙ S' ≅ S₁)
    (G : Cᵒᵖ ⥤ C) (H : Dᵒᵖ ⥤ D) (J : Aᵒᵖ ⥤ A) (K : Bᵒᵖ ⥤ B)
    (J' : A'ᵒᵖ ⥤ A') (K' : B'ᵒᵖ ⥤ B')
    (ηR : G ⋙ R ≅ R.op ⋙ J) (ηS : H ⋙ S ≅ S.op ⋙ K)
    (ηR' : J ⋙ R' ≅ R'.op ⋙ J') (ηS' : K ⋙ S' ≅ S'.op ⋙ K')
    (ηR₁ : G ⋙ R₁ ≅ R₁.op ⋙ J') (ηS₁ : H ⋙ S₁ ≅ S₁.op ⋙ K')
    (M : C)
    (c : Q.obj (J.obj (op (R.obj M))) ≅ K.obj (op (Q.obj (R.obj M))))
    (c' : Q'.obj (J'.obj (op (R'.obj (R.obj M)))) ≅ K'.obj (op (Q'.obj (R'.obj (R.obj M)))))
    (c₁ : Q'.obj (J'.obj (op (R₁.obj M))) ≅ K'.obj (op (Q'.obj (R₁.obj M))))
    (hρ : ∀ N : C, δS.inv.app (P.obj N) ≫ S'.map (ρ.hom.app N) ≫
      ρ'.hom.app (R.obj N) ≫ Q'.map (δR.hom.app N) = ρ₁.hom.app N)
    (hR : R'.map (ηR.hom.app (op M)) ≫ ηR'.hom.app (op (R.obj M)) =
      δR.hom.app (G.obj (op M)) ≫ ηR₁.hom.app (op M) ≫ J'.map (δR.hom.app M).op)
    (hS : S'.map (ηS.hom.app (op (P.obj M))) ≫ ηS'.hom.app (op (S.obj (P.obj M))) =
      δS.hom.app (H.obj (op (P.obj M))) ≫ ηS₁.hom.app (op (P.obj M)) ≫
        K'.map (δS.hom.app (P.obj M)).op)
    (hc : S'.map c.hom ≫ ηS'.hom.app (op (Q.obj (R.obj M))) =
      ρ'.hom.app (J.obj (op (R.obj M))) ≫ Q'.map (ηR'.hom.app (op (R.obj M))) ≫
        c'.hom ≫ K'.map (ρ'.hom.app (R.obj M)).op)
    (hc₁ : Q'.map (J'.map (δR.hom.app M).op) ≫ c'.hom =
      c₁.hom ≫ K'.map (Q'.map (δR.hom.app M)).op) :
    (δS.app (P.obj (G.obj (op M)))).symm ≪≫
      S'.mapIso (normalizedDualComparison P R S Q ρ G H J K ηR ηS M c) ≪≫
      δS.app (H.obj (op (P.obj M))) =
    normalizedDualComparison P R₁ S₁ Q' ρ₁ G H J' K' ηR₁ ηS₁ M c₁ := by
  let dS := K'.mapIso (δS.app (P.obj M)).op
  have hS₁ : δS.hom.app (H.obj (op (P.obj M))) ≫ ηS₁.hom.app (op (P.obj M)) =
      (S'.map (ηS.hom.app (op (P.obj M))) ≫ ηS'.hom.app (op (S.obj (P.obj M)))) ≫
        K'.map (δS.inv.app (P.obj M)).op := by
    have hh : S'.map (ηS.hom.app (op (P.obj M))) ≫ ηS'.hom.app (op (S.obj (P.obj M))) =
        (δS.hom.app (H.obj (op (P.obj M))) ≫ ηS₁.hom.app (op (P.obj M))) ≫ dS.hom :=
      hS.trans (Category.assoc _ _ _).symm
    have h := (Iso.eq_comp_inv dS.symm).mp hh
    exact h.symm
  have hnS := ηS'.hom.naturality (ρ.hom.app M).op
  change S'.map (K.map (ρ.hom.app M).op) ≫ ηS'.hom.app (op (S.obj (P.obj M))) =
    ηS'.hom.app (op (Q.obj (R.obj M))) ≫ K'.map (S'.map (ρ.hom.app M)).op at hnS
  have hnρ := ρ'.hom.naturality (ηR.hom.app (op M))
  change S'.map (Q.map (ηR.hom.app (op M))) ≫ ρ'.hom.app (J.obj (op (R.obj M))) =
    ρ'.hom.app (R.obj (G.obj (op M))) ≫ Q'.map (R'.map (ηR.hom.app (op M))) at hnρ
  have hRmap : Q'.map (R'.map (ηR.hom.app (op M))) ≫
      Q'.map (ηR'.hom.app (op (R.obj M))) =
      Q'.map (δR.hom.app (G.obj (op M))) ≫ Q'.map (ηR₁.hom.app (op M)) ≫
        Q'.map (J'.map (δR.hom.app M).op) := by
    simpa only [Functor.map_comp, Category.assoc] using congrArg Q'.map hR
  have hρDual : K'.map (Q'.map (δR.hom.app M)).op ≫
      K'.map (ρ'.hom.app (R.obj M)).op ≫ K'.map (S'.map (ρ.hom.app M)).op ≫
        K'.map (δS.inv.app (P.obj M)).op = K'.map (ρ₁.hom.app M).op := by
    simpa only [op_comp, Functor.map_comp, Category.assoc] using
      congrArg (fun a => K'.map a.op) (hρ M)
  apply Iso.ext
  apply (cancel_mono (ηS₁.hom.app (op (P.obj M)))).mp
  dsimp only [normalizedDualComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  change (δS.inv.app (P.obj (G.obj (op M))) ≫
    S'.map (ρ.hom.app (G.obj (op M)) ≫ Q.map (ηR.hom.app (op M)) ≫ c.hom ≫
      K.map (ρ.hom.app M).op ≫ ηS.inv.app (op (P.obj M))) ≫
        δS.hom.app (H.obj (op (P.obj M)))) ≫ ηS₁.hom.app (op (P.obj M)) =
    (ρ₁.hom.app (G.obj (op M)) ≫ Q'.map (ηR₁.hom.app (op M)) ≫ c₁.hom ≫
      K'.map (ρ₁.hom.app M).op ≫ ηS₁.inv.app (op (P.obj M))) ≫
      ηS₁.hom.app (op (P.obj M))
  simp only [Functor.map_comp, Category.assoc]
  rw [hS₁]
  simp only [Category.assoc]
  rw [← S'.map_comp_assoc (ηS.inv.app (op (P.obj M))) (ηS.hom.app (op (P.obj M)))]
  simp only [Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj, Functor.op_obj]
  rw [S'.map_id]
  simp only [Category.id_comp, Category.comp_id]
  rw [reassoc_of% hnS]
  rw [reassoc_of% hc]
  rw [reassoc_of% hnρ]
  rw [reassoc_of% hRmap]
  rw [reassoc_of% hc₁]
  have hρG := hρ (G.obj (op M))
  rw [reassoc_of% hρG]
  rw [hρDual]

end CategoryTheory.DualFiniteFrame
