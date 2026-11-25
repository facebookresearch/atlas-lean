/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorComparison

/-!
# Associator Quad Tensor Hom

Original enriched Day objects, full Hom maps and chosen coend presentations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonoidalClosed
namespace CategoryTheory.EnrichedDayKernel.AssociatorQuadIndex
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]

/-- Tensor two morphisms from the monoidal unit, using the inverse unit unitor to supply
  the pair of unit inputs. -/
abbrev unitPair {A B : V} (f : 𝟙_ V ⟶ A) (g : 𝟙_ V ⟶ B) : 𝟙_ V ⟶ A ⊗ B :=
  (λ_ (𝟙_ V)).inv ≫ (f ⊗ₘ g)

/-- Actual two generalized identities compose on the complete two-factor Hom. -/
@[reassoc]
theorem unitPair_pre {A B : V} (f : 𝟙_ V ⟶ A) (g : 𝟙_ V ⟶ B) (P Q : V) :
    (λ_ (P ⊗ Q)).inv ≫ (unitPair f g ⊗ₘ 𝟙 (P ⊗ Q)) ≫ tensorμ A B P Q =
      (((λ_ P).inv ≫ (f ⊗ₘ 𝟙 P)) ⊗ₘ ((λ_ Q).inv ≫ (g ⊗ₘ 𝟙 Q))) := by
  have h : (λ_ (P ⊗ Q)).inv ≫ (λ_ (𝟙_ V)).inv ▷ (P ⊗ Q) ≫
      tensorμ (𝟙_ V) (𝟙_ V) P Q = (λ_ P).inv ⊗ₘ (λ_ Q).inv := by
    simp only [tensorμ, braiding_tensorUnit_left]
    monoidal
  simp only [unitPair, tensorHom_id, comp_whiskerRight, Category.assoc]
  rw [tensorμ_natural_left]
  simpa only [Category.assoc, tensorHom_comp_tensorHom, tensorHom_id] using
    congrArg (fun z => z ≫ (f ▷ P ⊗ₘ g ▷ Q)) h

/-- The same two generalized identities compose after the complete two-factor Hom. -/
@[reassoc]
theorem unitPair_post {A B : V} (f : 𝟙_ V ⟶ A) (g : 𝟙_ V ⟶ B) (P Q : V) :
    (ρ_ (P ⊗ Q)).inv ≫ (𝟙 (P ⊗ Q) ⊗ₘ unitPair f g) ≫ tensorμ P Q A B =
      (((ρ_ P).inv ≫ (𝟙 P ⊗ₘ f)) ⊗ₘ ((ρ_ Q).inv ≫ (𝟙 Q ⊗ₘ g))) := by
  have h : (ρ_ (P ⊗ Q)).inv ≫ (P ⊗ Q) ◁ (λ_ (𝟙_ V)).inv ≫
      tensorμ P Q (𝟙_ V) (𝟙_ V) = (ρ_ P).inv ⊗ₘ (ρ_ Q).inv := by
    simp only [tensorμ, braiding_tensorUnit_right]
    monoidal
  simp only [unitPair, id_tensorHom, whiskerLeft_comp, Category.assoc]
  rw [tensorμ_natural_right]
  simpa only [Category.assoc, tensorHom_comp_tensorHom, id_tensorHom] using
    congrArg (fun z => z ≫ (P ◁ f ⊗ₘ Q ◁ g)) h

variable {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] (d : EnrichedMonoidalCategoryData V I)

/-- The original full tensor Hom commutes with actual precomposition in both indices. -/
@[reassoc]
theorem tensor_pre {X₀ X X' Y₀ Y Y' : I} (a : X₀ ⟶ X) (b : Y₀ ⟶ Y) :
    (eHomWhiskerRight V a X' ⊗ₘ eHomWhiskerRight V b Y') ≫ d.tensorMap X₀ X' Y₀ Y' =
      d.tensorMap X X' Y Y' ≫ eHomWhiskerRight V (a ⊗ₘ b) (X' ⊗ Y') := by
  let P : V := X ⟶[V] X'
  let Q : V := Y ⟶[V] Y'
  let R : V := X₀ ⟶[V] X
  let S : V := Y₀ ⟶[V] Y
  let L : V := (X ⊗ Y) ⟶[V] (X' ⊗ Y')
  let f : 𝟙_ V ⟶ R := eHomEquiv V a
  let g : 𝟙_ V ⟶ S := eHomEquiv V b
  let q : 𝟙_ V ⟶ R ⊗ S := unitPair f g
  let pre : P ⊗ Q ⟶ (R ⊗ S) ⊗ (P ⊗ Q) := (λ_ (P ⊗ Q)).inv ≫ (q ⊗ₘ 𝟙 (P ⊗ Q))
  let l : P ⊗ Q ⟶ L := d.tensorMap X X' Y Y'
  let k : R ⊗ S ⟶ ((X₀ ⊗ Y₀) ⟶[V] (X ⊗ Y)) := d.tensorMap X₀ X Y₀ Y
  have hq : q ≫ k = eHomEquiv V (a ⊗ₘ b) := by
    simpa only [q, k, unitPair, f, g, Category.assoc] using d.tensorMap_eHomEquiv a b
  have hp : pre ≫ tensorμ R S P Q =
      (((λ_ P).inv ≫ (f ⊗ₘ 𝟙 P)) ⊗ₘ ((λ_ Q).inv ≫ (g ⊗ₘ 𝟙 Q))) := by
    simpa only [pre, q, Category.assoc] using unitPair_pre f g P Q
  have h := congrArg (fun z => pre ≫ z) (d.tensorMap_comp X₀ X X' Y₀ Y Y')
  have hleft : pre ≫ tensorμ R S P Q ≫
      (eComp V X₀ X X' ⊗ₘ eComp V Y₀ Y Y') ≫ d.tensorMap X₀ X' Y₀ Y' =
      (eHomWhiskerRight V a X' ⊗ₘ eHomWhiskerRight V b Y') ≫ d.tensorMap X₀ X' Y₀ Y' := by
    rw [← Category.assoc, ← Category.assoc, hp]
    simp only [eHomWhiskerRight, ← tensorHom_comp_tensorHom, Category.assoc, tensorHom_id]
    rfl
  have hright : pre ≫ (k ⊗ₘ l) ≫ eComp V (X₀ ⊗ Y₀) (X ⊗ Y) (X' ⊗ Y') =
      l ≫ eHomWhiskerRight V (a ⊗ₘ b) (X' ⊗ Y') := by
    simp only [pre, Category.assoc]
    rw [tensorHom_comp_tensorHom_assoc, hq, Category.id_comp]
    rw [leftUnitor_inv_comp_tensorHom_assoc]
    rfl
  have hc : pre ≫ tensorμ R S P Q ≫
      (eComp V X₀ X X' ⊗ₘ eComp V Y₀ Y Y') ≫ d.tensorMap X₀ X' Y₀ Y' =
      pre ≫ (k ⊗ₘ l) ≫ eComp V (X₀ ⊗ Y₀) (X ⊗ Y) (X' ⊗ Y') := by
    simpa only [Enriched.prodEComp, Category.assoc] using h
  exact hleft.symm.trans (hc.trans hright)

/-- The original full tensor Hom commutes with actual postcomposition in both indices. -/
@[reassoc]
theorem tensor_post {X X' X₁ Y Y' Y₁ : I} (a : X' ⟶ X₁) (b : Y' ⟶ Y₁) :
    (eHomWhiskerLeft V X a ⊗ₘ eHomWhiskerLeft V Y b) ≫ d.tensorMap X X₁ Y Y₁ =
      d.tensorMap X X' Y Y' ≫ eHomWhiskerLeft V (X ⊗ Y) (a ⊗ₘ b) := by
  let P : V := X ⟶[V] X'
  let Q : V := Y ⟶[V] Y'
  let R : V := X' ⟶[V] X₁
  let S : V := Y' ⟶[V] Y₁
  let L : V := (X ⊗ Y) ⟶[V] (X' ⊗ Y')
  let f : 𝟙_ V ⟶ R := eHomEquiv V a
  let g : 𝟙_ V ⟶ S := eHomEquiv V b
  let q : 𝟙_ V ⟶ R ⊗ S := unitPair f g
  let pre : P ⊗ Q ⟶ (P ⊗ Q) ⊗ (R ⊗ S) := (ρ_ (P ⊗ Q)).inv ≫ (𝟙 (P ⊗ Q) ⊗ₘ q)
  let l : P ⊗ Q ⟶ L := d.tensorMap X X' Y Y'
  let k : R ⊗ S ⟶ ((X' ⊗ Y') ⟶[V] (X₁ ⊗ Y₁)) := d.tensorMap X' X₁ Y' Y₁
  have hq : q ≫ k = eHomEquiv V (a ⊗ₘ b) := by
    simpa only [q, k, unitPair, f, g, Category.assoc] using d.tensorMap_eHomEquiv a b
  have hp : pre ≫ tensorμ P Q R S =
      (((ρ_ P).inv ≫ (𝟙 P ⊗ₘ f)) ⊗ₘ ((ρ_ Q).inv ≫ (𝟙 Q ⊗ₘ g))) := by
    simpa only [pre, q, Category.assoc] using unitPair_post f g P Q
  have h := congrArg (fun z => pre ≫ z) (d.tensorMap_comp X X' X₁ Y Y' Y₁)
  have hleft : pre ≫ tensorμ P Q R S ≫
      (eComp V X X' X₁ ⊗ₘ eComp V Y Y' Y₁) ≫ d.tensorMap X X₁ Y Y₁ =
      (eHomWhiskerLeft V X a ⊗ₘ eHomWhiskerLeft V Y b) ≫ d.tensorMap X X₁ Y Y₁ := by
    rw [← Category.assoc, ← Category.assoc, hp]
    simp only [eHomWhiskerLeft, ← tensorHom_comp_tensorHom, Category.assoc, id_tensorHom]
    rfl
  have hright : pre ≫ (l ⊗ₘ k) ≫ eComp V (X ⊗ Y) (X' ⊗ Y') (X₁ ⊗ Y₁) =
      l ≫ eHomWhiskerLeft V (X ⊗ Y) (a ⊗ₘ b) := by
    simp only [pre, Category.assoc]
    rw [tensorHom_comp_tensorHom_assoc, hq, Category.id_comp]
    rw [rightUnitor_inv_comp_tensorHom_assoc]
    rfl
  have hc : pre ≫ tensorμ P Q R S ≫
      (eComp V X X' X₁ ⊗ₘ eComp V Y Y' Y₁) ≫ d.tensorMap X X₁ Y Y₁ =
      pre ≫ (l ⊗ₘ k) ≫ eComp V (X ⊗ Y) (X' ⊗ Y') (X₁ ⊗ Y₁) := by
    simpa only [Enriched.prodEComp, Category.assoc] using h
  exact hleft.symm.trans (hc.trans hright)

/-- Full original tensor Hom conjugation uses both actual index isomorphisms. -/
@[reassoc]
theorem tensor_congr {X X' Y Y' X₁ X₁' Y₁ Y₁' : I}
    (a : X ≅ X₁) (a' : X' ≅ X₁') (b : Y ≅ Y₁) (b' : Y' ≅ Y₁') :
    ((Iso.eHomCongr V a a').hom ⊗ₘ (Iso.eHomCongr V b b').hom) ≫ d.tensorMap X₁ X₁' Y₁ Y₁' =
      d.tensorMap X X' Y Y' ≫ (Iso.eHomCongr V (a ⊗ᵢ b) (a' ⊗ᵢ b')).hom := by
  simp only [Iso.eHomCongr, tensorIso_hom, tensorIso_inv]
  rw [← tensorHom_comp_tensorHom_assoc, tensor_post, tensor_pre_assoc]

end CategoryTheory.EnrichedDayKernel.AssociatorQuadIndex
