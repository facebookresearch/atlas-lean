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

public import MathlibExt.CategoryTheory.Preadditive.DualFiniteFrame.Composition
public import MathlibExt.CategoryTheory.Preadditive.DualFiniteFrame.FunctorIso
public import MathlibExt.CategoryTheory.Preadditive.DualFiniteFrame.NatIso

/-!
# Finite-frame dual comparisons in an additive square

Let additive functors P:C → D, R:C → E, S:D → K and Q:E → K
between preadditive categories form a natural square S∘P ≅ Q∘R.
Choose finite biproduct frames of distinguished objects in the four
categories and compatible dual evaluations. Natural duality comparisons
for the vertical functors, normalized at these objects, make the canonical
finite-frame comparisons for P and Q commute around the square.
The coefficient-category and finite-index universes are independent.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ w
namespace CategoryTheory.DualFiniteFrame

open CategoryTheory.DualFiniteFrame

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E]
  {K : Type u₄} [Category.{v₄} K] [Preadditive K]

/-- Let C,D,E,K be preadditive and P:C → D, R:C → E, S:D → K,
Q:E → K additive, with ρ:S∘P ≅ Q∘R.
Let additive contravariant functors G,H,J,L have natural comparisons
η_R:R∘G ≅ J∘Rᵒᵖ and η_S:S∘H ≅ L∘Sᵒᵖ.
For finite I, choose I-fold biproducts of U∈C,V∈D,W∈E,Z∈K,
isomorphisms p:P(U) ≅ V, r:R(U) ≅ W, s:S(V) ≅ Z, q:Q(W) ≅ Z,
and evaluations e_G:G(U) ≅ U, e_H:H(V) ≅ V,
e_J:J(W) ≅ W, e_L:L(Z) ≅ Z. Assume
r∘R(e_G)=e_J∘J((r⁻¹)ᵒᵖ)∘η_R,U,
s∘S(e_H)=e_L∘L((s⁻¹)ᵒᵖ)∘η_S,V,
and q∘Q(r)∘ρ_U=s∘S(p).
For a bilimit frame b of copies of U, write A=b.pt and E_P,E_Q for
the canonical comparisons at b and its R-image frame.
Their forward maps satisfy
E_Q∘Q(η_R,A)∘ρ_GA
=L((ρ_A⁻¹)ᵒᵖ)∘η_S,PA∘S(E_P). -/
theorem finiteFrameDualComparisonIso_square
    (P : C ⥤ D) [P.Additive] (R : C ⥤ E) [R.Additive]
    (S : D ⥤ K) [S.Additive] (Q : E ⥤ K) [Q.Additive]
    (ρ : P ⋙ S ≅ R ⋙ Q)
    (G : Cᵒᵖ ⥤ C) [G.Additive] (H : Dᵒᵖ ⥤ D) [H.Additive]
    (J : Eᵒᵖ ⥤ E) [J.Additive] (L : Kᵒᵖ ⥤ K) [L.Additive]
    (ηR : G ⋙ R ≅ R.op ⋙ J) (ηS : H ⋙ S ≅ S.op ⋙ L)
    (I : Type w) [Fintype I]
    (U : C) [HasBiproduct (fun _ : I => U)]
    (V : D) [HasBiproduct (fun _ : I => V)]
    (W : E) [HasBiproduct (fun _ : I => W)]
    (Z : K) [HasBiproduct (fun _ : I => Z)]
    (p : P.obj U ≅ V) (r : R.obj U ≅ W)
    (s : S.obj V ≅ Z) (q : Q.obj W ≅ Z)
    (eG : G.obj (op U) ≅ U) (eH : H.obj (op V) ≅ V)
    (eJ : J.obj (op W) ≅ W) (eL : L.obj (op Z) ≅ Z)
    (hR : R.map eG.hom ≫ r.hom =
      ηR.hom.app (op U) ≫ J.map r.inv.op ≫ eJ.hom)
    (hS : S.map eH.hom ≫ s.hom =
      ηS.hom.app (op V) ≫ L.map s.inv.op ≫ eL.hom)
    (hu : ρ.hom.app U ≫ (Q.mapIso r ≪≫ q).hom = (S.mapIso p ≪≫ s).hom)
    (b : Bicone (fun _ : I => U)) (hb : b.IsBilimit) :
    ρ.hom.app (G.obj (op b.pt)) ≫ Q.map (ηR.hom.app (op b.pt)) ≫
      (finiteFrameDualComparisonIso Q J L I W Z q eJ eL
        (mapUnitBicone R I U W r b) (mapUnitBiconeIsBilimit R I U W r b hb)).hom =
    S.map (finiteFrameDualComparisonIso P G H I U V p eG eH b hb).hom ≫
      ηS.hom.app (op (P.obj b.pt)) ≫ L.map (ρ.inv.app b.pt).op := by
  have h := finiteFrameDualComparisonIso_functorIso (P ⋙ S) (R ⋙ Q) ρ G L I U Z
    (S.mapIso p ≪≫ s) (Q.mapIso r ≪≫ q) eG eL hu b hb
  rw [finiteFrameDualComparisonIso_comp R Q G J L I U W Z r q eG eJ eL b hb,
    finiteFrameDualComparisonIso_comp P S G H L I U V Z p s eG eH eL b hb] at h
  rw [finiteFrameDualComparisonIso_eq_natIso R G J ηR I U W r eG eJ hR b hb,
    finiteFrameDualComparisonIso_eq_natIso S H L ηS I V Z s eH eL hS
      (mapUnitBicone P I U V p b) (mapUnitBiconeIsBilimit P I U V p b hb)] at h
  simpa only [Category.assoc, mapUnitBicone] using h

end CategoryTheory.DualFiniteFrame
