/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryCohomology.RoosComplex
public import MathlibExt.CategoryTheory.Limits.Shapes.DiscreteCofree
public import Mathlib.Algebra.Homology.Homotopy
public import MathlibExt.CategoryTheory.ComposableArrows.PrecompFaces

/-!
# Contracting the Roos complex of cofree diagrams

For a cofree coefficient diagram, terminal insertion extends a weak chain and
evaluates the new target at its identity-arrow coordinate. The resulting extra
codegeneracy satisfies the coface identities. In degree zero it splits the
coefficient-product augmentation; in positive degrees it expresses cycles as
boundaries. The positive-degree vanishing statements retain their individual
homology-existence hypotheses.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped BigOperators

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryCohomology

/-- The object-index coefficient product is derived from the original
larger product premise. The index category pins its hom universe before
product search; direct large-index product instances retain priority. -/
@[nolint unusedArguments]
local instance (priority := 100) roosCofreeHasCoefficientProducts
    {J : Type u₁} [Category.{v₁} J]
    {B : Type u₂} [Category.{v₂} B] [HasProducts.{max u₁ v₁} B] :
    HasProductsOfShape J B :=
  (Limits.hasProducts_shrink.{u₁, v₁, v₂, u₂} (C := B)) J

variable {I : Type u₁} [Category.{v₁} I]
  {A : Type u₂} [Category.{v₂} A] [HasProducts.{max u₁ v₁} A]
  (V : Discrete I ⥤ A)

local notation "RV" => Functor.obj (discreteCofreeFunctor (I := I) A) V

/-- The given larger product premise supplies the object-indexed products. -/
theorem roosCofreeHasObjectProducts : HasProducts.{u₁} A :=
  Limits.hasProducts_shrink.{u₁, v₁, v₂, u₂} (C := A)

/-- A homogeneous coordinate at a fixed target, retaining the chain and outgoing arrow. -/
def roosCofreeCoordinate (n : ℕ) (j : I)
    (z : Σ H : ComposableArrows Iᵒᵖ n, H.left.unop ⟶ j) :
    (roosCosimplicial RV).obj (SimplexCategory.mk n) ⟶ V.obj (Discrete.mk j) :=
  roosπ RV z.1 ≫ discreteCofreeπ A V z.1.left.unop ⟨j, z.2⟩

/-- The homogeneous coordinates determine maps into a cofree Roos degree. -/
theorem roosCofreeCoordinate_hom_ext (n : ℕ) {Z : A}
    {f g : Z ⟶ (roosCosimplicial RV).obj (SimplexCategory.mk n)}
    (h : ∀ (j : I) (z : Σ H : ComposableArrows Iᵒᵖ n, H.left.unop ⟶ j),
      f ≫ roosCofreeCoordinate V n j z = g ≫ roosCofreeCoordinate V n j z) : f = g := by
  apply roos_hom_ext RV (n := n)
  intro F
  let X : A := (roosCosimplicial RV).obj (SimplexCategory.mk n)
  let Y : A := Functor.obj RV F.left.unop
  let e : Y ≅ ∏ᶜ (fun p : discreteCofreeIndex F.left.unop ↦ V.obj (Discrete.mk p.1)) :=
    discreteCofreeObjIso A V F.left.unop
  let q : X ⟶ Y := roosπ RV F
  apply (cancel_mono e.hom).1
  apply Pi.hom_ext
  intro p
  let π : (∏ᶜ (fun p : discreteCofreeIndex F.left.unop ↦ V.obj (Discrete.mk p.1))) ⟶
      V.obj (Discrete.mk p.1) := Pi.π _ p
  let c : Y ⟶ V.obj (Discrete.mk p.1) := discreteCofreeπ A V F.left.unop p
  have hc : e.hom ≫ π = c := discreteCofreeObjIso_hom_π A V F.left.unop p
  have hh : f ≫ (q ≫ c) = g ≫ (q ≫ c) := h p.1 ⟨F, p.2⟩
  change ((f ≫ q) ≫ e.hom) ≫ π = ((g ≫ q) ≫ e.hom) ≫ π
  calc
    ((f ≫ q) ≫ e.hom) ≫ π = f ≫ (q ≫ (e.hom ≫ π)) := by simp only [Category.assoc]
    _ = f ≫ (q ≫ c) := congrArg (fun k => f ≫ (q ≫ k)) hc
    _ = g ≫ (q ≫ c) := hh
    _ = g ≫ (q ≫ (e.hom ≫ π)) := congrArg (fun k => g ≫ (q ≫ k)) hc.symm
    _ = ((g ≫ q) ≫ e.hom) ≫ π := by simp only [Category.assoc]

/-- An coface composes the retained outgoing arrow with its endpoint map. -/
@[reassoc]
theorem roosCofreeCoordinate_coface {n : ℕ} (i : Fin (n + 2)) (j : I)
    (z : Σ H : ComposableArrows Iᵒᵖ (n + 1), H.left.unop ⟶ j) :
    (roosCosimplicial RV).map (SimplexCategory.δ i) ≫
        roosCofreeCoordinate V (n + 1) j z =
      roosCofreeCoordinate V n j
        ⟨(nerve Iᵒᵖ).δ i z.1, (CategoryHomology.faceLeftHom i z.1).unop ≫ z.2⟩ := by
  let H : ComposableArrows Iᵒᵖ (n + 1) := z.1
  let F : ComposableArrows Iᵒᵖ n := (nerve Iᵒᵖ).δ i H
  let X₀ : A := (roosCosimplicial RV).obj (SimplexCategory.mk n)
  let X₁ : A := (roosCosimplicial RV).obj (SimplexCategory.mk (n + 1))
  let d : X₀ ⟶ X₁ := (roosCosimplicial RV).map (SimplexCategory.δ i)
  let q : X₁ ⟶ Functor.obj RV H.left.unop := roosπ RV H
  let q₀ : X₀ ⟶ Functor.obj RV F.left.unop := roosπ RV F
  let a : F.left.unop ⟶ H.left.unop := (CategoryHomology.faceLeftHom i H).unop
  let c : Functor.obj RV H.left.unop ⟶ V.obj (Discrete.mk j) :=
    discreteCofreeπ A V H.left.unop ⟨j, z.2⟩
  let c₀ : Functor.obj RV F.left.unop ⟶ V.obj (Discrete.mk j) :=
    discreteCofreeπ A V F.left.unop ⟨j, a ≫ z.2⟩
  have hd : d ≫ q = q₀ ≫ Functor.map RV a := roos_coface_π RV i H
  have hc : Functor.map RV a ≫ c = c₀ := discreteCofree_transition_π A V a ⟨j, z.2⟩
  change d ≫ (q ≫ c) = q₀ ≫ c₀
  calc
    d ≫ (q ≫ c) = (d ≫ q) ≫ c := (Category.assoc d q c).symm
    _ = (q₀ ≫ Functor.map RV a) ≫ c := congrArg (fun k => k ≫ c) hd
    _ = q₀ ≫ (Functor.map RV a ≫ c) := Category.assoc _ _ _
    _ = q₀ ≫ c₀ := congrArg (fun k => q₀ ≫ k) hc

/-- The extra codegeneracy inserts the outgoing target and evaluates its identity slot. -/
def roosCofreeExtraCodegeneracy (n : ℕ) :
    (roosCosimplicial RV).obj (SimplexCategory.mk (n + 1)) ⟶
      (roosCosimplicial RV).obj (SimplexCategory.mk n) :=
  Pi.lift (fun F : ComposableArrows Iᵒᵖ n ↦
    Pi.lift (fun p : discreteCofreeIndex (F.left.unop) ↦
      roosπ RV (F.precomp p.2.op) ≫ discreteCofreeπ A V p.1 ⟨p.1, 𝟙 p.1⟩) ≫
        (discreteCofreeObjIso A V (F.left.unop)).inv) ≫ (roosObjIso RV n).inv

/-- The double coordinate is the inserted chain evaluated at the identity. -/
@[reassoc]
theorem roosCofreeExtraCodegeneracy_π {n : ℕ} (F : ComposableArrows Iᵒᵖ n)
    (p : discreteCofreeIndex (F.left.unop)) :
    roosCofreeExtraCodegeneracy V n ≫ roosπ RV F ≫
        discreteCofreeπ A V (F.left.unop) p =
      roosπ RV (F.precomp p.2.op) ≫ discreteCofreeπ A V p.1 ⟨p.1, 𝟙 p.1⟩ := by
  let X₀ : A := (roosCosimplicial RV).obj (SimplexCategory.mk n)
  let X₁ : A := (roosCosimplicial RV).obj (SimplexCategory.mk (n + 1))
  let inner : ∀ H : ComposableArrows Iᵒᵖ n,
      X₁ ⟶ ∏ᶜ (fun p : discreteCofreeIndex H.left.unop ↦ V.obj (Discrete.mk p.1)) :=
    fun H ↦ Pi.lift (fun p : discreteCofreeIndex H.left.unop ↦
      roosCofreeCoordinate V (n + 1) p.1 ⟨H.precomp p.2.op, 𝟙 p.1⟩)
  let l : ∀ H : ComposableArrows Iᵒᵖ n, X₁ ⟶ roosFamily RV n H :=
    fun H ↦ inner H ≫ (discreteCofreeObjIso A V H.left.unop).inv
  let t : X₁ ⟶ ∏ᶜ (roosFamily RV n) := Pi.lift l
  let eR : X₀ ≅ ∏ᶜ (roosFamily RV n) := roosObjIso RV n
  let qR : X₀ ⟶ Functor.obj RV F.left.unop := roosπ RV F
  let pR : (∏ᶜ (roosFamily RV n)) ⟶ Functor.obj RV F.left.unop := Pi.π (roosFamily RV n) F
  let eC : Functor.obj RV F.left.unop ≅
      ∏ᶜ (fun p : discreteCofreeIndex F.left.unop ↦ V.obj (Discrete.mk p.1)) :=
    discreteCofreeObjIso A V F.left.unop
  let qC : Functor.obj RV F.left.unop ⟶ V.obj (Discrete.mk p.1) :=
    discreteCofreeπ A V F.left.unop p
  let pC : (∏ᶜ (fun p : discreteCofreeIndex F.left.unop ↦ V.obj (Discrete.mk p.1))) ⟶
      V.obj (Discrete.mk p.1) := Pi.π _ p
  have hR : eR.hom ≫ pR = qR := roosObjIso_hom_π RV F
  have hC : eC.hom ≫ pC = qC := discreteCofreeObjIso_hom_π A V F.left.unop p
  have hRi : eR.inv ≫ qR = pR := by
    calc
      eR.inv ≫ qR = eR.inv ≫ (eR.hom ≫ pR) := congrArg (fun k => eR.inv ≫ k) hR.symm
      _ = (eR.inv ≫ eR.hom) ≫ pR := (Category.assoc _ _ _).symm
      _ = 𝟙 _ ≫ pR := congrArg (fun k => k ≫ pR) eR.inv_hom_id
      _ = pR := Category.id_comp _
  have hCi : eC.inv ≫ qC = pC := by
    calc
      eC.inv ≫ qC = eC.inv ≫ (eC.hom ≫ pC) := congrArg (fun k => eC.inv ≫ k) hC.symm
      _ = (eC.inv ≫ eC.hom) ≫ pC := (Category.assoc _ _ _).symm
      _ = 𝟙 _ ≫ pC := congrArg (fun k => k ≫ pC) eC.inv_hom_id
      _ = pC := Category.id_comp _
  have ht : t ≫ pR = l F := Pi.lift_comp_π (f := roosFamily RV n) l F
  have hi : inner F ≫ pC = roosCofreeCoordinate V (n + 1) p.1
      ⟨F.precomp p.2.op, 𝟙 p.1⟩ :=
    Pi.lift_comp_π (f := fun p : discreteCofreeIndex F.left.unop ↦ V.obj (Discrete.mk p.1))
      (fun p : discreteCofreeIndex F.left.unop ↦
        roosCofreeCoordinate V (n + 1) p.1 ⟨F.precomp p.2.op, 𝟙 p.1⟩) p
  change (t ≫ eR.inv) ≫ qR ≫ qC = roosCofreeCoordinate V (n + 1) p.1
    ⟨F.precomp p.2.op, 𝟙 p.1⟩
  calc
    (t ≫ eR.inv) ≫ qR ≫ qC = t ≫ (eR.inv ≫ qR) ≫ qC := by simp only [Category.assoc]
    _ = t ≫ pR ≫ qC := congrArg (fun k => t ≫ k ≫ qC) hRi
    _ = (t ≫ pR) ≫ qC := (Category.assoc _ _ _).symm
    _ = l F ≫ qC := congrArg (fun k => k ≫ qC) ht
    _ = inner F ≫ (eC.inv ≫ qC) := Category.assoc _ _ _
    _ = inner F ≫ pC := congrArg (fun k => inner F ≫ k) hCi
    _ = roosCofreeCoordinate V (n + 1) p.1 ⟨F.precomp p.2.op, 𝟙 p.1⟩ := hi

/-- Terminal insertion has the same homogeneous coordinate as its inserted identity slot. -/
@[reassoc]
theorem roosCofreeExtraCodegeneracy_coordinate (n : ℕ) (j : I)
    (z : Σ H : ComposableArrows Iᵒᵖ n, H.left.unop ⟶ j) :
    roosCofreeExtraCodegeneracy V n ≫ roosCofreeCoordinate V n j z =
      roosCofreeCoordinate V (n + 1) j ⟨z.1.precomp z.2.op, 𝟙 j⟩ :=
  roosCofreeExtraCodegeneracy_π V z.1 ⟨j, z.2⟩

/-- The first coface followed by terminal insertion is the identity. -/
theorem roosCofree_coface_zero_extra (n : ℕ) :
    (roosCosimplicial RV).map (SimplexCategory.δ (0 : Fin (n + 2))) ≫
        roosCofreeExtraCodegeneracy V n = 𝟙 _ := by
  apply roosCofreeCoordinate_hom_ext V n
  intro j z
  rcases z with ⟨F, f⟩
  let G : ComposableArrows Iᵒᵖ (n + 1) := F.precomp f.op
  have hG : (nerve Iᵒᵖ).δ (0 : Fin (n + 2)) G = F := by
    change G.δ₀ = F
    exact ComposableArrows.precomp_δ₀ F f.op
  have ha : HEq ((CategoryHomology.faceLeftHom (0 : Fin (n + 2)) G).unop ≫ 𝟙 j) f := by
    change HEq (f ≫ 𝟙 j) f
    exact heq_of_eq (Category.comp_id f)
  have hz : (⟨(nerve Iᵒᵖ).δ (0 : Fin (n + 2)) G,
      (CategoryHomology.faceLeftHom (0 : Fin (n + 2)) G).unop ≫ 𝟙 j⟩ :
      Σ H : ComposableArrows Iᵒᵖ n, H.left.unop ⟶ j) = ⟨F, f⟩ := Sigma.ext hG ha
  let d := (roosCosimplicial RV).map (SimplexCategory.δ (0 : Fin (n + 2)))
  let e := roosCofreeExtraCodegeneracy V n
  change (d ≫ e) ≫ roosCofreeCoordinate V n j ⟨F, f⟩ =
    𝟙 _ ≫ roosCofreeCoordinate V n j ⟨F, f⟩
  calc
    (d ≫ e) ≫ roosCofreeCoordinate V n j ⟨F, f⟩ =
        d ≫ (e ≫ roosCofreeCoordinate V n j ⟨F, f⟩) := Category.assoc _ _ _
    _ = d ≫ roosCofreeCoordinate V (n + 1) j ⟨G, 𝟙 j⟩ :=
      congrArg (fun k => d ≫ k) (roosCofreeExtraCodegeneracy_coordinate V n j ⟨F, f⟩)
    _ = roosCofreeCoordinate V n j
        ⟨(nerve Iᵒᵖ).δ (0 : Fin (n + 2)) G,
          (CategoryHomology.faceLeftHom (0 : Fin (n + 2)) G).unop ≫ 𝟙 j⟩ :=
      roosCofreeCoordinate_coface V (0 : Fin (n + 2)) j ⟨G, 𝟙 j⟩
    _ = roosCofreeCoordinate V n j ⟨F, f⟩ := congrArg (roosCofreeCoordinate V n j) hz
    _ = 𝟙 _ ≫ roosCofreeCoordinate V n j ⟨F, f⟩ := (Category.id_comp _).symm

/-- Every coface of the insertion is evaluated on the face of the longer chain. -/
theorem roosCofree_coface_extra_π {n : ℕ} (i : Fin (n + 2))
    (F : ComposableArrows Iᵒᵖ n) (p : discreteCofreeIndex (F.left.unop)) :
    (roosCosimplicial RV).map (SimplexCategory.δ i) ≫
        roosCofreeExtraCodegeneracy V n ≫ roosπ RV F ≫
          discreteCofreeπ A V (F.left.unop) p =
      roosπ RV ((nerve Iᵒᵖ).δ i (F.precomp p.2.op)) ≫
        Functor.map RV ((CategoryHomology.faceLeftHom i (F.precomp p.2.op)).unop) ≫
          discreteCofreeπ A V p.1 ⟨p.1, 𝟙 p.1⟩ := by
  let H : ComposableArrows Iᵒᵖ (n + 1) := F.precomp p.2.op
  let X₀ : A := (roosCosimplicial RV).obj (SimplexCategory.mk n)
  let X₁ : A := (roosCosimplicial RV).obj (SimplexCategory.mk (n + 1))
  let d : X₀ ⟶ X₁ := (roosCosimplicial RV).map (SimplexCategory.δ i)
  let e : X₁ ⟶ X₀ := roosCofreeExtraCodegeneracy V n
  let qF : X₀ ⟶ Functor.obj RV F.left.unop := roosπ RV F
  let cF : Functor.obj RV F.left.unop ⟶ V.obj (Discrete.mk p.1) :=
    discreteCofreeπ A V F.left.unop p
  let qH : X₁ ⟶ Functor.obj RV p.1 := roosπ RV H
  let cH : Functor.obj RV p.1 ⟶ V.obj (Discrete.mk p.1) := discreteCofreeπ A V p.1 ⟨p.1, 𝟙 p.1⟩
  let q₀ : X₀ ⟶ Functor.obj RV ((nerve Iᵒᵖ).δ i H).left.unop :=
    roosπ RV ((nerve Iᵒᵖ).δ i H)
  let a : ((nerve Iᵒᵖ).δ i H).left.unop ⟶ p.1 := (CategoryHomology.faceLeftHom i H).unop
  have he : e ≫ (qF ≫ cF) = qH ≫ cH := roosCofreeExtraCodegeneracy_π V F p
  have hd : d ≫ qH = q₀ ≫ Functor.map RV a := roos_coface_π RV i H
  change d ≫ (e ≫ (qF ≫ cF)) = q₀ ≫ (Functor.map RV a ≫ cH)
  calc
    d ≫ (e ≫ (qF ≫ cF)) = d ≫ (qH ≫ cH) := congrArg (fun k => d ≫ k) he
    _ = (d ≫ qH) ≫ cH := (Category.assoc _ _ _).symm
    _ = (q₀ ≫ Functor.map RV a) ≫ cH := congrArg (fun k => k ≫ cH) hd
    _ = q₀ ≫ (Functor.map RV a ≫ cH) := Category.assoc _ _ _

/-- Identity-slot evaluation from degree zero to the coefficient product. -/
def roosCofreeRetraction :
    (roosCosimplicial RV).obj (SimplexCategory.mk 0) ⟶
      ∏ᶜ fun j : I ↦ V.obj (Discrete.mk j) :=
  Pi.lift fun j ↦ roosπ RV (ComposableArrows.mk₀ (op j)) ≫
    discreteCofreeπ A V j ⟨j, 𝟙 j⟩

/-- Replicate the target coefficient at each outgoing coordinate of degree zero. -/
def roosCofreeSection : (∏ᶜ fun j : I ↦ V.obj (Discrete.mk j)) ⟶
    (roosCosimplicial RV).obj (SimplexCategory.mk 0) :=
  Pi.lift (fun F : ComposableArrows Iᵒᵖ 0 ↦
    Pi.lift (fun p : discreteCofreeIndex (F.left.unop) ↦ Pi.π _ p.1) ≫
      (discreteCofreeObjIso A V (F.left.unop)).inv) ≫ (roosObjIso RV 0).inv

/-- Projection at j of the degree-zero retraction evaluates the zero-chain coordinate at j and
then the outgoing identity-arrow coefficient. -/
@[reassoc]
theorem roosCofreeRetraction_π (j : I) :
    roosCofreeRetraction V ≫ Pi.π _ j =
      roosπ RV (ComposableArrows.mk₀ (op j)) ≫ discreteCofreeπ A V j ⟨j, 𝟙 j⟩ :=
  Pi.lift_comp_π _ j

/-- The degree-zero section followed by a zero-chain and outgoing-arrow coordinate is the
coefficient-product projection at that arrow’s target. -/
@[reassoc]
theorem roosCofreeSection_π (F : ComposableArrows Iᵒᵖ 0)
    (p : discreteCofreeIndex (F.left.unop)) :
    roosCofreeSection V ≫ roosπ RV F ≫ discreteCofreeπ A V (F.left.unop) p =
      Pi.π (fun j : I ↦ V.obj (Discrete.mk j)) p.1 := by
  let P : A := ∏ᶜ (fun j : I ↦ V.obj (Discrete.mk j))
  let X : A := (roosCosimplicial RV).obj (SimplexCategory.mk 0)
  let inner : ∀ H : ComposableArrows Iᵒᵖ 0,
      P ⟶ ∏ᶜ (fun p : discreteCofreeIndex H.left.unop ↦ V.obj (Discrete.mk p.1)) :=
    fun H ↦ Pi.lift (fun p : discreteCofreeIndex H.left.unop ↦
      Pi.π (fun j : I ↦ V.obj (Discrete.mk j)) p.1)
  let l : ∀ H : ComposableArrows Iᵒᵖ 0, P ⟶ roosFamily RV 0 H :=
    fun H ↦ inner H ≫ (discreteCofreeObjIso A V H.left.unop).inv
  let t : P ⟶ ∏ᶜ (roosFamily RV 0) := Pi.lift l
  let eR : X ≅ ∏ᶜ (roosFamily RV 0) := roosObjIso RV 0
  let qR : X ⟶ Functor.obj RV F.left.unop := roosπ RV F
  let pR : (∏ᶜ (roosFamily RV 0)) ⟶ Functor.obj RV F.left.unop := Pi.π (roosFamily RV 0) F
  let eC : Functor.obj RV F.left.unop ≅
      ∏ᶜ (fun p : discreteCofreeIndex F.left.unop ↦ V.obj (Discrete.mk p.1)) :=
    discreteCofreeObjIso A V F.left.unop
  let qC : Functor.obj RV F.left.unop ⟶ V.obj (Discrete.mk p.1) :=
    discreteCofreeπ A V F.left.unop p
  let pC : (∏ᶜ (fun p : discreteCofreeIndex F.left.unop ↦ V.obj (Discrete.mk p.1))) ⟶
      V.obj (Discrete.mk p.1) := Pi.π _ p
  have hR : eR.hom ≫ pR = qR := roosObjIso_hom_π RV F
  have hC : eC.hom ≫ pC = qC := discreteCofreeObjIso_hom_π A V F.left.unop p
  have hRi : eR.inv ≫ qR = pR := by
    calc
      eR.inv ≫ qR = eR.inv ≫ (eR.hom ≫ pR) := congrArg (fun k => eR.inv ≫ k) hR.symm
      _ = (eR.inv ≫ eR.hom) ≫ pR := (Category.assoc _ _ _).symm
      _ = 𝟙 _ ≫ pR := congrArg (fun k => k ≫ pR) eR.inv_hom_id
      _ = pR := Category.id_comp _
  have hCi : eC.inv ≫ qC = pC := by
    calc
      eC.inv ≫ qC = eC.inv ≫ (eC.hom ≫ pC) := congrArg (fun k => eC.inv ≫ k) hC.symm
      _ = (eC.inv ≫ eC.hom) ≫ pC := (Category.assoc _ _ _).symm
      _ = 𝟙 _ ≫ pC := congrArg (fun k => k ≫ pC) eC.inv_hom_id
      _ = pC := Category.id_comp _
  have ht : t ≫ pR = l F := Pi.lift_comp_π (f := roosFamily RV 0) l F
  have hi : inner F ≫ pC = Pi.π (fun j : I ↦ V.obj (Discrete.mk j)) p.1 :=
    Pi.lift_comp_π (f := fun p : discreteCofreeIndex F.left.unop ↦ V.obj (Discrete.mk p.1))
      (fun p : discreteCofreeIndex F.left.unop ↦
        Pi.π (fun j : I ↦ V.obj (Discrete.mk j)) p.1) p
  change (t ≫ eR.inv) ≫ qR ≫ qC = Pi.π (fun j : I ↦ V.obj (Discrete.mk j)) p.1
  calc
    (t ≫ eR.inv) ≫ qR ≫ qC = t ≫ (eR.inv ≫ qR) ≫ qC := by simp only [Category.assoc]
    _ = t ≫ pR ≫ qC := congrArg (fun k => t ≫ k ≫ qC) hRi
    _ = (t ≫ pR) ≫ qC := (Category.assoc _ _ _).symm
    _ = l F ≫ qC := congrArg (fun k => k ≫ qC) ht
    _ = inner F ≫ (eC.inv ≫ qC) := Category.assoc _ _ _
    _ = inner F ≫ pC := congrArg (fun k => inner F ≫ k) hCi
    _ = Pi.π (fun j : I ↦ V.obj (Discrete.mk j)) p.1 := hi

/-- The section repeats the target coordinate in every homogeneous slot. -/
@[reassoc]
theorem roosCofreeSection_coordinate (j : I)
    (z : Σ H : ComposableArrows Iᵒᵖ 0, H.left.unop ⟶ j) :
    roosCofreeSection V ≫ roosCofreeCoordinate V 0 j z =
      Pi.π (fun j : I ↦ V.obj (Discrete.mk j)) j :=
  roosCofreeSection_π V z.1 ⟨j, z.2⟩

/-- Repetition followed by identity-slot evaluation is the product identity. -/
theorem roosCofreeSection_retraction :
    roosCofreeSection V ≫ roosCofreeRetraction V = 𝟙 _ := by
  apply Pi.hom_ext
  intro j
  let X : A := (roosCosimplicial RV).obj (SimplexCategory.mk 0)
  let P : A := ∏ᶜ (fun j : I ↦ V.obj (Discrete.mk j))
  let a : P ⟶ X := roosCofreeSection V
  let b : X ⟶ P := roosCofreeRetraction V
  let π : P ⟶ V.obj (Discrete.mk j) := Pi.π _ j
  have hb : b ≫ π = roosCofreeCoordinate V 0 j ⟨ComposableArrows.mk₀ (op j), 𝟙 j⟩ :=
    roosCofreeRetraction_π V j
  have ha : a ≫ roosCofreeCoordinate V 0 j ⟨ComposableArrows.mk₀ (op j), 𝟙 j⟩ = π :=
    roosCofreeSection_coordinate V j ⟨ComposableArrows.mk₀ (op j), 𝟙 j⟩
  change (a ≫ b) ≫ π = 𝟙 P ≫ π
  exact (Category.assoc a b π).trans
    ((congrArg (fun k => a ≫ k) hb).trans (ha.trans (Category.id_comp π).symm))

/-- The other degree-zero coface is the repetition/evaluation end projector. -/
theorem roosCofree_coface_one_extra :
    (roosCosimplicial RV).map (SimplexCategory.δ (1 : Fin 2)) ≫
      roosCofreeExtraCodegeneracy V 0 = roosCofreeRetraction V ≫ roosCofreeSection V := by
  apply roosCofreeCoordinate_hom_ext V 0
  intro j z
  rcases z with ⟨F, f⟩
  let G : ComposableArrows Iᵒᵖ 1 := F.precomp f.op
  have hG : (nerve Iᵒᵖ).δ (1 : Fin 2) G = ComposableArrows.mk₀ (op j) :=
    ComposableArrows.ext₀ rfl
  have hg : CategoryHomology.faceLeftHom (1 : Fin 2) G = 𝟙 (op j) := by
    change G.map (𝟙 (0 : Fin 2)) = _
    exact G.map_id _
  have hu : ((CategoryHomology.faceLeftHom (1 : Fin 2) G).unop : j ⟶ j) = 𝟙 j :=
    congrArg (fun k : op j ⟶ op j => k.unop) hg
  have ha : HEq ((CategoryHomology.faceLeftHom (1 : Fin 2) G).unop ≫ 𝟙 j) (𝟙 j) :=
    heq_of_eq ((congrArg (fun k : j ⟶ j => k ≫ 𝟙 j) hu).trans (Category.id_comp _))
  have hz : (⟨(nerve Iᵒᵖ).δ (1 : Fin 2) G,
      (CategoryHomology.faceLeftHom (1 : Fin 2) G).unop ≫ 𝟙 j⟩ :
      Σ H : ComposableArrows Iᵒᵖ 0, H.left.unop ⟶ j) =
      ⟨ComposableArrows.mk₀ (op j), 𝟙 j⟩ := Sigma.ext hG ha
  let d := (roosCosimplicial RV).map (SimplexCategory.δ (1 : Fin 2))
  let e := roosCofreeExtraCodegeneracy V 0
  let r := roosCofreeRetraction V
  let a := roosCofreeSection V
  let π := Pi.π (fun j : I ↦ V.obj (Discrete.mk j)) j
  change (d ≫ e) ≫ roosCofreeCoordinate V 0 j ⟨F, f⟩ =
    (r ≫ a) ≫ roosCofreeCoordinate V 0 j ⟨F, f⟩
  calc
    (d ≫ e) ≫ roosCofreeCoordinate V 0 j ⟨F, f⟩ =
        d ≫ (e ≫ roosCofreeCoordinate V 0 j ⟨F, f⟩) := Category.assoc _ _ _
    _ = d ≫ roosCofreeCoordinate V 1 j ⟨G, 𝟙 j⟩ :=
      congrArg (fun k => d ≫ k) (roosCofreeExtraCodegeneracy_coordinate V 0 j ⟨F, f⟩)
    _ = roosCofreeCoordinate V 0 j
        ⟨(nerve Iᵒᵖ).δ (1 : Fin 2) G,
          (CategoryHomology.faceLeftHom (1 : Fin 2) G).unop ≫ 𝟙 j⟩ :=
      roosCofreeCoordinate_coface V (1 : Fin 2) j ⟨G, 𝟙 j⟩
    _ = roosCofreeCoordinate V 0 j ⟨ComposableArrows.mk₀ (op j), 𝟙 j⟩ :=
      congrArg (roosCofreeCoordinate V 0 j) hz
    _ = r ≫ π := (roosCofreeRetraction_π V j).symm
    _ = r ≫ (a ≫ roosCofreeCoordinate V 0 j ⟨F, f⟩) :=
      congrArg (fun k => r ≫ k) (roosCofreeSection_coordinate V j ⟨F, f⟩).symm
    _ = (r ≫ a) ≫ roosCofreeCoordinate V 0 j ⟨F, f⟩ := (Category.assoc _ _ _).symm

/-- Later cofaces commute with insertion, using the outgoing coordinate reindexing. -/
theorem roosCofree_coface_succ_extra (n : ℕ) (i : Fin (n + 2)) :
    (roosCosimplicial RV).map (SimplexCategory.δ i.succ) ≫
        roosCofreeExtraCodegeneracy V (n + 1) =
      roosCofreeExtraCodegeneracy V n ≫
        (roosCosimplicial RV).map (SimplexCategory.δ i) := by
  apply roosCofreeCoordinate_hom_ext V (n + 1)
  intro j z
  rcases z with ⟨F, f⟩
  let G : ComposableArrows Iᵒᵖ (n + 2) := F.precomp f.op
  let H : ComposableArrows Iᵒᵖ n := (nerve Iᵒᵖ).δ i F
  let a : H.left.unop ⟶ j := (CategoryHomology.faceLeftHom i F).unop ≫ f
  have hc : a.op = f.op ≫ CategoryHomology.faceLeftHom i F := by
    change ((CategoryHomology.faceLeftHom i F).unop ≫ f).op = _
    rw [op_comp, Quiver.Hom.op_unop]
  have hG : (nerve Iᵒᵖ).δ i.succ G = H.precomp a.op :=
    (ComposableArrows.nerve_δ_succ_precomp F f.op i).trans
      (congrArg (fun k : op j ⟶ H.left => H.precomp k) hc.symm)
  have hleft : G.left = ((nerve Iᵒᵖ).δ i.succ G).left :=
    CategoryHomology.face_left_eq_of_ne_zero (i := i.succ)
      (fun h => (Fin.succ_ne_zero i) (Fin.ext h)) G
  have e : (0 : Fin (n + 3)) = i.succ.succAbove (0 : Fin (n + 2)) :=
    (Fin.succ_succAbove_zero i).symm
  have hm : CategoryHomology.faceLeftHom i.succ G = eqToHom hleft := by
    change G.map (homOfLE (Fin.zero_le (i.succ.succAbove 0))) = _
    rw [show homOfLE (Fin.zero_le (i.succ.succAbove 0)) = eqToHom e from
      Subsingleton.elim _ _]
    exact eqToHom_map G e
  have hTransport : ∀ {X Y : Iᵒᵖ} (h : X = Y),
      HEq ((eqToHom h).unop ≫ 𝟙 X.unop) (𝟙 X.unop) := by
    intro X Y h
    cases h
    change HEq ((𝟙 X.unop) ≫ 𝟙 X.unop) (𝟙 X.unop)
    exact heq_of_eq (Category.id_comp _)
  have ha : HEq ((CategoryHomology.faceLeftHom i.succ G).unop ≫ 𝟙 j) (𝟙 j) :=
    (heq_of_eq (congrArg
      (fun k : G.left ⟶ ((nerve Iᵒᵖ).δ i.succ G).left => k.unop ≫ 𝟙 j) hm)).trans
      (hTransport hleft)
  have hz : (⟨(nerve Iᵒᵖ).δ i.succ G,
      (CategoryHomology.faceLeftHom i.succ G).unop ≫ 𝟙 j⟩ :
      Σ K : ComposableArrows Iᵒᵖ (n + 1), K.left.unop ⟶ j) =
      ⟨H.precomp a.op, 𝟙 j⟩ := Sigma.ext hG ha
  let d₀ := (roosCosimplicial RV).map (SimplexCategory.δ i)
  let d₁ := (roosCosimplicial RV).map (SimplexCategory.δ i.succ)
  let e₀ := roosCofreeExtraCodegeneracy V n
  let e₁ := roosCofreeExtraCodegeneracy V (n + 1)
  change (d₁ ≫ e₁) ≫ roosCofreeCoordinate V (n + 1) j ⟨F, f⟩ =
    (e₀ ≫ d₀) ≫ roosCofreeCoordinate V (n + 1) j ⟨F, f⟩
  calc
    (d₁ ≫ e₁) ≫ roosCofreeCoordinate V (n + 1) j ⟨F, f⟩ =
        d₁ ≫ (e₁ ≫ roosCofreeCoordinate V (n + 1) j ⟨F, f⟩) := Category.assoc _ _ _
    _ = d₁ ≫ roosCofreeCoordinate V (n + 2) j ⟨G, 𝟙 j⟩ :=
      congrArg (fun k => d₁ ≫ k) (roosCofreeExtraCodegeneracy_coordinate V (n + 1) j ⟨F, f⟩)
    _ = roosCofreeCoordinate V (n + 1) j
        ⟨(nerve Iᵒᵖ).δ i.succ G, (CategoryHomology.faceLeftHom i.succ G).unop ≫ 𝟙 j⟩ :=
      roosCofreeCoordinate_coface V i.succ j ⟨G, 𝟙 j⟩
    _ = roosCofreeCoordinate V (n + 1) j ⟨H.precomp a.op, 𝟙 j⟩ :=
      congrArg (roosCofreeCoordinate V (n + 1) j) hz
    _ = e₀ ≫ roosCofreeCoordinate V n j ⟨H, a⟩ :=
      (roosCofreeExtraCodegeneracy_coordinate V n j ⟨H, a⟩).symm
    _ = e₀ ≫ (d₀ ≫ roosCofreeCoordinate V (n + 1) j ⟨F, f⟩) :=
      congrArg (fun k => e₀ ≫ k) (roosCofreeCoordinate_coface V i j ⟨F, f⟩).symm
    _ = (e₀ ≫ d₀) ≫ roosCofreeCoordinate V (n + 1) j ⟨F, f⟩ := (Category.assoc _ _ _).symm

section Preadditive

variable [Preadditive A]

/-- The degree-zero contracting identity for the alternating-coface differential. -/
theorem roosCofree_d_zero_extra :
    (roosComplex RV).d 0 1 ≫
        (show (roosComplex RV).X 1 ⟶ (roosComplex RV).X 0 from roosCofreeExtraCodegeneracy V 0) =
      𝟙 ((roosComplex RV).X 0) -
        (show (roosComplex RV).X 0 ⟶ (roosComplex RV).X 0 from
          roosCofreeRetraction V ≫ roosCofreeSection V) := by
  let X₀ : A := (roosCosimplicial RV).obj (SimplexCategory.mk 0)
  let X₁ : A := (roosCosimplicial RV).obj (SimplexCategory.mk 1)
  let d : X₀ ⟶ X₁ := (roosComplex RV).d 0 1
  let e : X₁ ⟶ X₀ := roosCofreeExtraCodegeneracy V 0
  let c₀ : X₀ ⟶ X₁ := (roosCosimplicial RV).map (SimplexCategory.δ (0 : Fin 2))
  let c₁ : X₀ ⟶ X₁ := (roosCosimplicial RV).map (SimplexCategory.δ (1 : Fin 2))
  let q : X₀ ⟶ X₀ := roosCofreeRetraction V ≫ roosCofreeSection V
  have hd : d = ∑ i : Fin 2, (-1 : ℤ) ^ i.val •
      (roosCosimplicial RV).map (SimplexCategory.δ i) := roosComplex_d RV 0
  have hd' : d = c₀ - c₁ := by
    simpa only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
      one_zsmul, neg_one_zsmul, sub_eq_add_neg] using hd
  have h₀ : c₀ ≫ e = 𝟙 X₀ := roosCofree_coface_zero_extra V 0
  have h₁ : c₁ ≫ e = q := roosCofree_coface_one_extra V
  change d ≫ e = 𝟙 X₀ - q
  calc
    d ≫ e = (c₀ - c₁) ≫ e := congrArg (fun k : X₀ ⟶ X₁ => k ≫ e) hd'
    _ = c₀ ≫ e - c₁ ≫ e := by rw [Preadditive.sub_comp]
    _ = 𝟙 X₀ - q := by rw [h₀, h₁]

/-- The alternating differential contracts in every positive degree. -/
theorem roosCofree_d_succ_extra (n : ℕ) :
    (roosComplex RV).d (n + 1) (n + 2) ≫
        (show (roosComplex RV).X (n + 2) ⟶ (roosComplex RV).X (n + 1) from
          roosCofreeExtraCodegeneracy V (n + 1)) +
      (show (roosComplex RV).X (n + 1) ⟶ (roosComplex RV).X n from
        roosCofreeExtraCodegeneracy V n) ≫ (roosComplex RV).d n (n + 1) =
      𝟙 ((roosComplex RV).X (n + 1)) := by
  let X₀ : A := (roosCosimplicial RV).obj (SimplexCategory.mk n)
  let X₁ : A := (roosCosimplicial RV).obj (SimplexCategory.mk (n + 1))
  let X₂ : A := (roosCosimplicial RV).obj (SimplexCategory.mk (n + 2))
  let d₀ : X₀ ⟶ X₁ := (roosComplex RV).d n (n + 1)
  let d₁ : X₁ ⟶ X₂ := (roosComplex RV).d (n + 1) (n + 2)
  let e₀ : X₁ ⟶ X₀ := roosCofreeExtraCodegeneracy V n
  let e₁ : X₂ ⟶ X₁ := roosCofreeExtraCodegeneracy V (n + 1)
  let c₀ : X₁ ⟶ X₂ := (roosCosimplicial RV).map (SimplexCategory.δ (0 : Fin (n + 3)))
  let a : Fin (n + 2) → (X₀ ⟶ X₁) :=
    fun i ↦ (roosCosimplicial RV).map (SimplexCategory.δ i)
  let b : Fin (n + 3) → (X₁ ⟶ X₂) :=
    fun i ↦ (roosCosimplicial RV).map (SimplexCategory.δ i)
  let t : X₁ ⟶ X₁ := ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • (b i.succ ≫ e₁)
  have hd₀ : d₀ = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • a i := roosComplex_d RV n
  have hd₁ : d₁ = ∑ i : Fin (n + 3), (-1 : ℤ) ^ i.val • b i := roosComplex_d RV (n + 1)
  have he : ∀ i : Fin (n + 2), b i.succ ≫ e₁ = e₀ ≫ a i :=
    fun i ↦ roosCofree_coface_succ_extra V n i
  have ht : t = e₀ ≫ d₀ := by
    calc
      t = ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • (e₀ ≫ a i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun k : X₁ ⟶ X₁ => (-1 : ℤ) ^ i.val • k) (he i)
      _ = e₀ ≫ (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • a i) := by
        simp only [Preadditive.comp_sum, Preadditive.comp_zsmul]
      _ = e₀ ≫ d₀ := congrArg (fun k : X₀ ⟶ X₁ => e₀ ≫ k) hd₀.symm
  have hsplit : (∑ i : Fin (n + 3), (-1 : ℤ) ^ i.val • (b i ≫ e₁)) = c₀ ≫ e₁ - t := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, pow_zero, one_zsmul, pow_succ',
      neg_one_mul, neg_zsmul, Finset.sum_neg_distrib, sub_eq_add_neg]
    rfl
  have h₀ : c₀ ≫ e₁ = 𝟙 X₁ := roosCofree_coface_zero_extra V (n + 1)
  have hcontract : d₁ ≫ e₁ = 𝟙 X₁ - e₀ ≫ d₀ := by
    calc
      d₁ ≫ e₁ = (∑ i : Fin (n + 3), (-1 : ℤ) ^ i.val • b i) ≫ e₁ :=
        congrArg (fun k : X₁ ⟶ X₂ => k ≫ e₁) hd₁
      _ = ∑ i : Fin (n + 3), (-1 : ℤ) ^ i.val • (b i ≫ e₁) := by
        simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]
      _ = c₀ ≫ e₁ - t := hsplit
      _ = 𝟙 X₁ - e₀ ≫ d₀ := by rw [h₀, ht]
  change d₁ ≫ e₁ + e₀ ≫ d₀ = 𝟙 X₁
  exact (congrArg (fun k : X₁ ⟶ X₁ => k + e₀ ≫ d₀) hcontract).trans (sub_add_cancel _ _)

/-- The insertion restricted to the support of a cochain homotopy. -/
def roosCofreeSupportedHom :
    ∀ i j : ℕ, (ComplexShape.up ℕ).Rel j i →
      ((roosComplex RV).X i ⟶ (roosComplex RV).X j) :=
  fun i j hij ↦ by
    change j + 1 = i at hij
    subst i
    exact roosCofreeExtraCodegeneracy V j

/-- The end map defined from insertion, before computing its components. -/
def roosCofreeEndProjector : roosComplex RV ⟶ roosComplex RV :=
  𝟙 _ - Homotopy.nullHomotopicMap' (roosCofreeSupportedHom V)

/-- Its degree-zero component is the evaluation/repetition projector. -/
theorem roosCofreeEndProjector_f_zero :
    (roosCofreeEndProjector V).f 0 =
      (show (roosComplex RV).X 0 ⟶ (roosComplex RV).X 0 from
        roosCofreeRetraction V ≫ roosCofreeSection V) := by
  let X₀ : A := (roosCosimplicial RV).obj (SimplexCategory.mk 0)
  let X₁ : A := (roosCosimplicial RV).obj (SimplexCategory.mk 1)
  let d : X₀ ⟶ X₁ := (roosComplex RV).d 0 1
  let e : X₁ ⟶ X₀ := roosCofreeExtraCodegeneracy V 0
  let q : X₀ ⟶ X₀ := roosCofreeRetraction V ≫ roosCofreeSection V
  change 𝟙 ((roosComplex RV).X 0) -
    (Homotopy.nullHomotopicMap' (roosCofreeSupportedHom V)).f 0 = _
  rw [Homotopy.nullHomotopicMap'_f_of_not_rel_right
    (show (ComplexShape.up ℕ).Rel 0 1 from rfl)
    (fun l hl ↦ by change l + 1 = 0 at hl; omega) (roosCofreeSupportedHom V)]
  change 𝟙 X₀ - (d ≫ e) = q
  have hd : d ≫ e = 𝟙 X₀ - q := roosCofree_d_zero_extra V
  rw [hd]
  abel

/-- All positive components of that same end map vanish. -/
theorem roosCofreeEndProjector_f_succ (n : ℕ) :
    (roosCofreeEndProjector V).f (n + 1) = 0 := by
  let X₀ : A := (roosCosimplicial RV).obj (SimplexCategory.mk n)
  let X₁ : A := (roosCosimplicial RV).obj (SimplexCategory.mk (n + 1))
  let X₂ : A := (roosCosimplicial RV).obj (SimplexCategory.mk (n + 2))
  let d₀ : X₀ ⟶ X₁ := (roosComplex RV).d n (n + 1)
  let d₁ : X₁ ⟶ X₂ := (roosComplex RV).d (n + 1) (n + 2)
  let e₀ : X₁ ⟶ X₀ := roosCofreeExtraCodegeneracy V n
  let e₁ : X₂ ⟶ X₁ := roosCofreeExtraCodegeneracy V (n + 1)
  change 𝟙 ((roosComplex RV).X (n + 1)) -
    (Homotopy.nullHomotopicMap' (roosCofreeSupportedHom V)).f (n + 1) = 0
  rw [Homotopy.nullHomotopicMap'_f
    (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)
    (show (ComplexShape.up ℕ).Rel (n + 1) (n + 2) from rfl) (roosCofreeSupportedHom V)]
  change 𝟙 X₁ - (d₁ ≫ e₁ + e₀ ≫ d₀) = 0
  have hc : d₁ ≫ e₁ + e₀ ≫ d₀ = 𝟙 X₁ := roosCofree_d_succ_extra V n
  rw [hc, sub_self]

/-- Native insertion gives a homotopy from identity to the computed end projector. -/
def roosCofreeNativeHomotopy :
    Homotopy (𝟙 (roosComplex RV)) (roosCofreeEndProjector V) :=
  Homotopy.equivSubZero.symm
    ((Homotopy.ofEq (show 𝟙 (roosComplex RV) - roosCofreeEndProjector V =
        Homotopy.nullHomotopicMap' (roosCofreeSupportedHom V) by
      unfold roosCofreeEndProjector
      abel)).trans (Homotopy.nullHomotopy' (roosCofreeSupportedHom V)))

/-- Cofree positive cohomology vanishes whenever this degree homology exists. -/
theorem isZero_roosCofree_homology_succ (n : ℕ)
    [(roosComplex RV).HasHomology (n + 1)] :
    IsZero ((roosComplex RV).homology (n + 1)) := by
  let H : A := (roosComplex RV).homology (n + 1)
  let Z : A := (roosComplex RV).cycles (n + 1)
  let B : A := (roosComplex RV).opcycles (n + 1)
  let X : A := (roosComplex RV).X (n + 1)
  let π : Z ⟶ H := (roosComplex RV).homologyπ (n + 1)
  let ι : H ⟶ B := (roosComplex RV).homologyι (n + 1)
  let u : Z ⟶ X := (roosComplex RV).iCycles (n + 1)
  let v : X ⟶ B := (roosComplex RV).pOpcycles (n + 1)
  let f : X ⟶ X := (roosCofreeEndProjector V).f (n + 1)
  let e : H ⟶ H := HomologicalComplex.homologyMap
    (K := roosComplex RV) (L := roosComplex RV) (roosCofreeEndProjector V) (n + 1)
  have h : 𝟙 H = e :=
    (HomologicalComplex.homologyMap_id (roosComplex RV) (n + 1)).symm.trans
      ((roosCofreeNativeHomotopy V).homologyMap_eq (n + 1))
  have hp : π ≫ e ≫ ι = u ≫ f ≫ v :=
    ShortComplex.π_homologyMap_ι
      ((HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℕ) (n + 1)).map
        (roosCofreeEndProjector V))
  have hf : f = 0 := roosCofreeEndProjector_f_succ V n
  have hp₀ : π ≫ e ≫ ι = 0 := by
    calc
      π ≫ e ≫ ι = u ≫ f ≫ v := hp
      _ = u ≫ (0 : X ⟶ X) ≫ v := congrArg (fun k : X ⟶ X => u ≫ k ≫ v) hf
      _ = 0 := by simp only [zero_comp, comp_zero]
  have : Epi π := inferInstanceAs (Epi ((roosComplex RV).homologyπ (n + 1)))
  have : Mono ι := inferInstanceAs (Mono ((roosComplex RV).homologyι (n + 1)))
  have he : e = 0 := by
    apply (cancel_epi π).1
    apply (cancel_mono ι).1
    have hz : (π ≫ (0 : H ⟶ H)) ≫ ι = 0 := by rw [comp_zero, zero_comp]
    exact (Category.assoc π e ι).trans (hp₀.trans hz.symm)
  apply (IsZero.iff_id_eq_zero H).2
  exact h.trans he

end Preadditive

end CategoryTheory.CategoryCohomology

end
