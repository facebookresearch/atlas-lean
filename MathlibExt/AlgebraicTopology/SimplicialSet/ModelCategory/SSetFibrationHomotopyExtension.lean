/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import MathlibExt.AlgebraicTopology.SimplicialSet.MonoidalCompat
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetAnodyneLifting

/-!
# Homotopy extension against simplicial fibrations

Let i:K→L be monic and p:E→B a Kan fibration. A partial lift hE on K×Δ[1], a chosen lift f on
either endpoint of L, and a base homotopy hB on L×Δ[1] extend to a cylinder lift ψ whenever all
three overlap equations hold.

For endpoint e, the conditions are i≫f=ιe≫hE, ιe≫hB=f≫p and (i×id)≫hB=hE≫p. The extension
satisfies ιe≫ψ=f, (i×id)≫ψ=hE and ψ≫p=hB.

Endpoint zero is vertex zero, represented by δ₁; endpoint one is vertex one, represented by δ₀.
The simplicial-set universe u is arbitrary.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra Simplicial
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet

private theorem faceZero_mem_anodyneExtensions :
    anodyneExtensions
      (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι := by
  have h_eq :
      (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) =
        horn (n := 1) (0 : Fin 2) := by
    have h_fin : ({0} : Finset (Fin 2)) = {1}ᶜ := by decide
    calc
      (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) =
          stdSimplex.face ({1}ᶜ : Finset (Fin 2)) := by rw [h_fin]
      _ = horn (n := 1) (0 : Fin 2) := by
        ext m x
        simp [horn_eq_iSup]
  rw [h_eq]
  exact anodyneExtensions.horn_ι (0 : Fin 2)

private theorem faceOne_mem_anodyneExtensions :
    anodyneExtensions
      (stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι := by
  have h_eq :
      (stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex) =
        horn (n := 1) (1 : Fin 2) := by
    have h_fin : ({1} : Finset (Fin 2)) = {0}ᶜ := by decide
    calc
      (stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex) =
          stdSimplex.face ({0}ᶜ : Finset (Fin 2)) := by rw [h_fin]
      _ = horn (n := 1) (1 : Fin 2) := by
        ext m x
        simp [horn_eq_iSup]
  rw [h_eq]
  exact anodyneExtensions.horn_ι (1 : Fin 2)

private noncomputable def endpointZeroIso (X : SSet.{u}) :
    X ⊗ (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex) ≅ X :=
  ((Iso.refl X) ⊗ᵢ (stdSimplex.faceSingletonIso (0 : Fin 2)).symm) ≪≫
    stdSimplex.rightUnitor X

private noncomputable def endpointOneIso (X : SSet.{u}) :
    X ⊗ (stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex) ≅ X :=
  ((Iso.refl X) ⊗ᵢ (stdSimplex.faceSingletonIso (1 : Fin 2)).symm) ≪≫
    stdSimplex.rightUnitor X

private lemma endpointZeroIso_inv_face (X : SSet.{u}) :
    (endpointZeroIso X).inv ≫
        X ◁ (stdSimplex.face {0} : (Δ[1] : SSet.{u}).Subcomplex).ι =
      ι₀ := by
  rw [← stdSimplex.rightUnitor_inv_map_δ_one]
  simp only [endpointZeroIso, Iso.trans_inv, tensorIso_inv, Iso.refl_inv,
    Iso.symm_inv, id_tensorHom, Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp]
  rw [stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ]

private lemma endpointOneIso_inv_face (X : SSet.{u}) :
    (endpointOneIso X).inv ≫
        X ◁ (stdSimplex.face {1} : (Δ[1] : SSet.{u}).Subcomplex).ι =
      ι₁ := by
  rw [← stdSimplex.rightUnitor_inv_map_δ_zero]
  simp only [endpointOneIso, Iso.trans_inv, tensorIso_inv, Iso.refl_inv,
    Iso.symm_inv, id_tensorHom, Category.assoc]
  rw [← MonoidalCategory.whiskerLeft_comp]
  rw [stdSimplex.faceSingletonIso_one_hom_comp_ι_eq_δ]

/-- Let i:K→L be a simplicial monomorphism and p:E→B a Kan fibration. Fix hE:K×Δ[1]→E, an endpoint
map f:L→E and a base homotopy hB:L×Δ[1]→B. Assume i≫f=ι₀≫hE, ι₀≫hB=f≫p and (i×id)≫hB=hE≫p. Then
there is ψ:L×Δ[1]→E with ι₀≫ψ=f, (i×id)≫ψ=hE and ψ≫p=hB. Endpoint zero is δ₁. -/
theorem homotopy_extension_property₀ {B E K L : SSet.{u}} (i : K ⟶ L)
    (p : E ⟶ B) [Fibration p] [Mono i]
    (hE : K ⊗ Δ[1] ⟶ E) (f : L ⟶ E) (h₁ : i ≫ f = ι₀ ≫ hE)
    (hB : L ⊗ Δ[1] ⟶ B) (h₂ : ι₀ ≫ hB = f ≫ p)
    (h₃ : i ▷ (Δ[1] : SSet.{u}) ≫ hB = hE ≫ p) :
    ∃ ψ : L ⊗ Δ[1] ⟶ E,
      ι₀ ≫ ψ = f ∧ i ▷ (Δ[1] : SSet.{u}) ≫ ψ = hE ∧ ψ ≫ p = hB := by
  let A : L.Subcomplex := Subcomplex.range i
  let T : (Δ[1] : SSet.{u}).Subcomplex := stdSimplex.face {0}
  let eᵢ : K ≅ A := asIso (Subcomplex.toRange i)
  let e₀ : Δ[0] ≅ T := stdSimplex.faceSingletonIso (0 : Fin 2)
  let leftMap : L ⊗ (T : SSet.{u}) ⟶ E := (endpointZeroIso L).hom ≫ f
  let rightMap : (A : SSet.{u}) ⊗ Δ[1] ⟶ E :=
    (eᵢ.inv ▷ (Δ[1] : SSet.{u})) ≫ hE
  have hcompat :
      (A.ι ▷ (T : SSet.{u})) ≫ leftMap =
        ((A : SSet.{u}) ◁ T.ι) ≫ rightMap := by
    apply (cancel_epi (eᵢ.hom ▷ (T : SSet.{u}))).mp
    apply (cancel_epi (K ◁ e₀.hom)).mp
    calc
      (K ◁ e₀.hom) ≫ (eᵢ.hom ▷ (T : SSet.{u})) ≫
          (A.ι ▷ (T : SSet.{u})) ≫ leftMap =
          (stdSimplex.rightUnitor K).hom ≫ i ≫ f := by
            simp only [leftMap, endpointZeroIso, eᵢ, e₀, A, T,
              Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom,
              Iso.symm_hom, asIso_hom, Category.assoc]
            rw [MonoidalCategory.whisker_exchange_assoc,
              MonoidalCategory.whisker_exchange_assoc,
              ← MonoidalCategory.comp_whiskerRight_assoc,
              Subcomplex.toRange_ι,
              ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.hom_inv_id]
            simp
      _ = (stdSimplex.rightUnitor K).hom ≫ ι₀ ≫ hE := by rw [h₁]
      _ = (K ◁ e₀.hom) ≫ (eᵢ.hom ▷ (T : SSet.{u})) ≫
          ((A : SSet.{u}) ◁ T.ι) ≫ rightMap := by
            rw [stdSimplex.rightUnitor_hom_ι₀_assoc]
            symm
            simp only [rightMap, eᵢ, e₀, A, T]
            rw [MonoidalCategory.whisker_exchange_assoc,
              ← MonoidalCategory.whiskerLeft_comp_assoc,
              stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ,
              MonoidalCategory.whisker_exchange_assoc,
              ← MonoidalCategory.comp_whiskerRight_assoc, Iso.hom_inv_id]
            simp
  let unionMap : (A.unionProd T : SSet.{u}) ⟶ E :=
    (Subcomplex.unionProd.isPushout A T).desc leftMap rightMap hcompat
  have hleft : Subcomplex.unionProd.ι₁ A T ≫ unionMap = leftMap := by
    simp [unionMap]
  have hright : Subcomplex.unionProd.ι₂ A T ≫ unionMap = rightMap := by
    simp [unionMap]
  have hunionMap : unionMap ≫ p = (A.unionProd T).ι ≫ hB := by
    apply (Subcomplex.unionProd.isPushout A T).hom_ext
    · rw [← Category.assoc, hleft, Subcomplex.unionProd.ι₁_ι_assoc]
      apply (cancel_epi (endpointZeroIso L).inv).mp
      simp only [Category.assoc, Iso.inv_hom_id_assoc, leftMap]
      calc
        f ≫ p = ι₀ ≫ hB := h₂.symm
        _ = (endpointZeroIso L).inv ≫ (L ◁ T.ι) ≫ hB := by
          simpa only [T, Category.assoc] using
            congrArg (fun q => q ≫ hB) (endpointZeroIso_inv_face L).symm
    · rw [← Category.assoc, hright, Subcomplex.unionProd.ι₂_ι_assoc]
      apply (cancel_epi (eᵢ.hom ▷ (Δ[1] : SSet.{u}))).mp
      calc
        (eᵢ.hom ▷ (Δ[1] : SSet.{u})) ≫ rightMap ≫ p = hE ≫ p := by
          simp only [rightMap, Category.assoc]
          rw [← MonoidalCategory.comp_whiskerRight_assoc, Iso.hom_inv_id]
          simp
        _ = i ▷ (Δ[1] : SSet.{u}) ≫ hB := h₃.symm
        _ = (eᵢ.hom ▷ (Δ[1] : SSet.{u})) ≫
            (A.ι ▷ (Δ[1] : SSet.{u})) ≫ hB := by
          change i ▷ (Δ[1] : SSet.{u}) ≫ hB =
            (Subcomplex.toRange i ▷ (Δ[1] : SSet.{u})) ≫
              ((Subcomplex.range i).ι ▷ (Δ[1] : SSet.{u})) ≫ hB
          rw [← MonoidalCategory.comp_whiskerRight_assoc,
            Subcomplex.toRange_ι]
  let sq : CommSq unionMap (A.unionProd T).ι p hB := ⟨hunionMap⟩
  have hT : anodyneExtensions T.ι := by
    simpa [T] using faceZero_mem_anodyneExtensions
  have hAnodyne : anodyneExtensions (A.unionProd T).ι :=
    anodyneExtensions_unionProd_ι A T hT
  have hLift : sq.HasLift :=
    (anodyneExtensions.hasLeftLiftingProperty hAnodyne p).sq_hasLift sq
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · calc
      ι₀ ≫ sq.lift = (endpointZeroIso L).inv ≫
          (L ◁ T.ι) ≫ sq.lift := by
            simpa only [T, Category.assoc] using
              congrArg (fun q => q ≫ sq.lift) (endpointZeroIso_inv_face L).symm
      _ = (endpointZeroIso L).inv ≫ Subcomplex.unionProd.ι₁ A T ≫
          (A.unionProd T).ι ≫ sq.lift := by
            rw [Subcomplex.unionProd.ι₁_ι_assoc]
      _ = (endpointZeroIso L).inv ≫ Subcomplex.unionProd.ι₁ A T ≫
          unionMap := by rw [sq.fac_left]
      _ = (endpointZeroIso L).inv ≫ leftMap := by rw [hleft]
      _ = f := by simp [leftMap]
  · calc
      i ▷ (Δ[1] : SSet.{u}) ≫ sq.lift =
          (eᵢ.hom ▷ (Δ[1] : SSet.{u})) ≫
            (A.ι ▷ (Δ[1] : SSet.{u})) ≫ sq.lift := by
              change i ▷ (Δ[1] : SSet.{u}) ≫ sq.lift =
                (Subcomplex.toRange i ▷ (Δ[1] : SSet.{u})) ≫
                  ((Subcomplex.range i).ι ▷ (Δ[1] : SSet.{u})) ≫ sq.lift
              rw [← MonoidalCategory.comp_whiskerRight_assoc,
                Subcomplex.toRange_ι]
      _ = (eᵢ.hom ▷ (Δ[1] : SSet.{u})) ≫
          Subcomplex.unionProd.ι₂ A T ≫ (A.unionProd T).ι ≫ sq.lift := by
            rw [Subcomplex.unionProd.ι₂_ι_assoc]
      _ = (eᵢ.hom ▷ (Δ[1] : SSet.{u})) ≫
          Subcomplex.unionProd.ι₂ A T ≫ unionMap := by rw [sq.fac_left]
      _ = (eᵢ.hom ▷ (Δ[1] : SSet.{u})) ≫ rightMap := by
            rw [hright]
      _ = hE := by simp [rightMap]

/-- Let i:K→L be a simplicial monomorphism and p:E→B a Kan fibration. Fix hE:K×Δ[1]→E, an endpoint
map f:L→E and a base homotopy hB:L×Δ[1]→B. Assume i≫f=ι₁≫hE, ι₁≫hB=f≫p and (i×id)≫hB=hE≫p. Then
there is ψ:L×Δ[1]→E with ι₁≫ψ=f, (i×id)≫ψ=hE and ψ≫p=hB. Endpoint one is δ₀. -/
theorem homotopy_extension_property₁ {B E K L : SSet.{u}} (i : K ⟶ L)
    (p : E ⟶ B) [Fibration p] [Mono i]
    (hE : K ⊗ Δ[1] ⟶ E) (f : L ⟶ E) (h₁ : i ≫ f = ι₁ ≫ hE)
    (hB : L ⊗ Δ[1] ⟶ B) (h₂ : ι₁ ≫ hB = f ≫ p)
    (h₃ : i ▷ (Δ[1] : SSet.{u}) ≫ hB = hE ≫ p) :
    ∃ ψ : L ⊗ Δ[1] ⟶ E,
      ι₁ ≫ ψ = f ∧ i ▷ (Δ[1] : SSet.{u}) ≫ ψ = hE ∧ ψ ≫ p = hB := by
  let A : L.Subcomplex := Subcomplex.range i
  let T : (Δ[1] : SSet.{u}).Subcomplex := stdSimplex.face {1}
  let eᵢ : K ≅ A := asIso (Subcomplex.toRange i)
  let e₁ : Δ[0] ≅ T := stdSimplex.faceSingletonIso (1 : Fin 2)
  let leftMap : L ⊗ (T : SSet.{u}) ⟶ E := (endpointOneIso L).hom ≫ f
  let rightMap : (A : SSet.{u}) ⊗ Δ[1] ⟶ E :=
    (eᵢ.inv ▷ (Δ[1] : SSet.{u})) ≫ hE
  have hcompat :
      (A.ι ▷ (T : SSet.{u})) ≫ leftMap =
        ((A : SSet.{u}) ◁ T.ι) ≫ rightMap := by
    apply (cancel_epi (eᵢ.hom ▷ (T : SSet.{u}))).mp
    apply (cancel_epi (K ◁ e₁.hom)).mp
    calc
      (K ◁ e₁.hom) ≫ (eᵢ.hom ▷ (T : SSet.{u})) ≫
          (A.ι ▷ (T : SSet.{u})) ≫ leftMap =
          (stdSimplex.rightUnitor K).hom ≫ i ≫ f := by
            simp only [leftMap, endpointOneIso, eᵢ, e₁, A, T,
              Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom,
              Iso.symm_hom, asIso_hom, Category.assoc]
            rw [MonoidalCategory.whisker_exchange_assoc,
              MonoidalCategory.whisker_exchange_assoc,
              ← MonoidalCategory.comp_whiskerRight_assoc,
              Subcomplex.toRange_ι,
              ← MonoidalCategory.whiskerLeft_comp_assoc, Iso.hom_inv_id]
            simp
      _ = (stdSimplex.rightUnitor K).hom ≫ ι₁ ≫ hE := by rw [h₁]
      _ = (K ◁ e₁.hom) ≫ (eᵢ.hom ▷ (T : SSet.{u})) ≫
          ((A : SSet.{u}) ◁ T.ι) ≫ rightMap := by
            rw [stdSimplex.rightUnitor_hom_ι₁_assoc]
            symm
            simp only [rightMap, eᵢ, e₁, A, T]
            rw [MonoidalCategory.whisker_exchange_assoc,
              ← MonoidalCategory.whiskerLeft_comp_assoc,
              stdSimplex.faceSingletonIso_one_hom_comp_ι_eq_δ,
              MonoidalCategory.whisker_exchange_assoc,
              ← MonoidalCategory.comp_whiskerRight_assoc, Iso.hom_inv_id]
            simp
  let unionMap : (A.unionProd T : SSet.{u}) ⟶ E :=
    (Subcomplex.unionProd.isPushout A T).desc leftMap rightMap hcompat
  have hleft : Subcomplex.unionProd.ι₁ A T ≫ unionMap = leftMap := by
    simp [unionMap]
  have hright : Subcomplex.unionProd.ι₂ A T ≫ unionMap = rightMap := by
    simp [unionMap]
  have hunionMap : unionMap ≫ p = (A.unionProd T).ι ≫ hB := by
    apply (Subcomplex.unionProd.isPushout A T).hom_ext
    · rw [← Category.assoc, hleft, Subcomplex.unionProd.ι₁_ι_assoc]
      apply (cancel_epi (endpointOneIso L).inv).mp
      simp only [Category.assoc, Iso.inv_hom_id_assoc, leftMap]
      calc
        f ≫ p = ι₁ ≫ hB := h₂.symm
        _ = (endpointOneIso L).inv ≫ (L ◁ T.ι) ≫ hB := by
          simpa only [T, Category.assoc] using
            congrArg (fun q => q ≫ hB) (endpointOneIso_inv_face L).symm
    · rw [← Category.assoc, hright, Subcomplex.unionProd.ι₂_ι_assoc]
      apply (cancel_epi (eᵢ.hom ▷ (Δ[1] : SSet.{u}))).mp
      calc
        (eᵢ.hom ▷ (Δ[1] : SSet.{u})) ≫ rightMap ≫ p = hE ≫ p := by
          simp only [rightMap, Category.assoc]
          rw [← MonoidalCategory.comp_whiskerRight_assoc, Iso.hom_inv_id]
          simp
        _ = i ▷ (Δ[1] : SSet.{u}) ≫ hB := h₃.symm
        _ = (eᵢ.hom ▷ (Δ[1] : SSet.{u})) ≫
            (A.ι ▷ (Δ[1] : SSet.{u})) ≫ hB := by
          change i ▷ (Δ[1] : SSet.{u}) ≫ hB =
            (Subcomplex.toRange i ▷ (Δ[1] : SSet.{u})) ≫
              ((Subcomplex.range i).ι ▷ (Δ[1] : SSet.{u})) ≫ hB
          rw [← MonoidalCategory.comp_whiskerRight_assoc,
            Subcomplex.toRange_ι]
  let sq : CommSq unionMap (A.unionProd T).ι p hB := ⟨hunionMap⟩
  have hT : anodyneExtensions T.ι := by
    simpa [T] using faceOne_mem_anodyneExtensions
  have hAnodyne : anodyneExtensions (A.unionProd T).ι :=
    anodyneExtensions_unionProd_ι A T hT
  have hLift : sq.HasLift :=
    (anodyneExtensions.hasLeftLiftingProperty hAnodyne p).sq_hasLift sq
  refine ⟨sq.lift, ?_, ?_, sq.fac_right⟩
  · calc
      ι₁ ≫ sq.lift = (endpointOneIso L).inv ≫
          (L ◁ T.ι) ≫ sq.lift := by
            simpa only [T, Category.assoc] using
              congrArg (fun q => q ≫ sq.lift) (endpointOneIso_inv_face L).symm
      _ = (endpointOneIso L).inv ≫ Subcomplex.unionProd.ι₁ A T ≫
          (A.unionProd T).ι ≫ sq.lift := by
            rw [Subcomplex.unionProd.ι₁_ι_assoc]
      _ = (endpointOneIso L).inv ≫ Subcomplex.unionProd.ι₁ A T ≫
          unionMap := by rw [sq.fac_left]
      _ = (endpointOneIso L).inv ≫ leftMap := by rw [hleft]
      _ = f := by simp [leftMap]
  · calc
      i ▷ (Δ[1] : SSet.{u}) ≫ sq.lift =
          (eᵢ.hom ▷ (Δ[1] : SSet.{u})) ≫
            (A.ι ▷ (Δ[1] : SSet.{u})) ≫ sq.lift := by
              change i ▷ (Δ[1] : SSet.{u}) ≫ sq.lift =
                (Subcomplex.toRange i ▷ (Δ[1] : SSet.{u})) ≫
                  ((Subcomplex.range i).ι ▷ (Δ[1] : SSet.{u})) ≫ sq.lift
              rw [← MonoidalCategory.comp_whiskerRight_assoc,
                Subcomplex.toRange_ι]
      _ = (eᵢ.hom ▷ (Δ[1] : SSet.{u})) ≫
          Subcomplex.unionProd.ι₂ A T ≫ (A.unionProd T).ι ≫ sq.lift := by
            rw [Subcomplex.unionProd.ι₂_ι_assoc]
      _ = (eᵢ.hom ▷ (Δ[1] : SSet.{u})) ≫
          Subcomplex.unionProd.ι₂ A T ≫ unionMap := by rw [sq.fac_left]
      _ = (eᵢ.hom ▷ (Δ[1] : SSet.{u})) ≫ rightMap := by
            rw [hright]
      _ = hE := by simp [rightMap]

end SSet
