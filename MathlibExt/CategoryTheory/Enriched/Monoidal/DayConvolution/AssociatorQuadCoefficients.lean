/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorQuadIndex
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.AssociatorQuadCoendMap

/-!
# Associator Quad Coefficients

Original enriched Day objects, full Hom maps and chosen coend presentations.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uA uB uC uD
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed
namespace CategoryTheory.EnrichedDayKernel.AssociatorQuadCoefficient
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed
  V]
  {A : Type uA} [EnrichedCategory V A] {B : Type uB} [EnrichedCategory V B]
  {C : Type uC} [EnrichedCategory V C] {D : Type uD} [EnrichedCategory V D]
  (F : EnrichedFunctor V A V) (G : EnrichedFunctor V B V)
  (H : EnrichedFunctor V C V) (J : EnrichedFunctor V D V)
attribute [local instance] Enriched.prodCategory
private abbrev selfHom (U W : V) : V :=
  @EnrichedCategory.Hom V _ _ V (inferInstance : EnrichedCategory V V) U W
/-- The full four-input product `((A × B) × C) × D` for the coefficient pentagon. -/
abbrev indices := ((A × B) × C) × D
/-- The enriched product of the four original coefficient functors, with the full
  four-input Hom action. -/
abbrev inputProduct : EnrichedFunctor V (indices (A := A) (B := B) (C := C) (D := D)) (((V × V) × V)
  × V) :=
  prodEnrichedFunctor (prodEnrichedFunctor (prodEnrichedFunctor F G) H) J
/-- The enriched monoidal data of the closed category `V` over itself. -/
abbrev selfData : EnrichedMonoidalCategoryData V V :=
  MonoidalClosed.enrichedMonoidalCategoryDataSelf V
/-- The fully left-associated external coefficient tensor `((F ⊗ G) ⊗ H) ⊗ J`. -/
abbrev coefficientA : EnrichedFunctor V (indices (A := A) (B := B) (C := C) (D := D)) V :=
  ((F.externalTensor G).externalTensor H).externalTensor J
/-- The fully left-associated coefficient tensor obtained by composing the four-input
  product with the self-enriched index tensor. -/
abbrev coefficientAprime : EnrichedFunctor V (indices (A := A) (B := B) (C := C) (D := D)) V :=
  (inputProduct F G H J).comp V (AssociatorQuadIndex.indexA (selfData (V := V)))
/-- The coefficient tensor with parenthesization `(F ⊗ G) ⊗ (H ⊗ J)`. -/
abbrev coefficientB : EnrichedFunctor V (indices (A := A) (B := B) (C := C) (D := D)) V :=
  (inputProduct F G H J).comp V (AssociatorQuadIndex.indexB (selfData (V := V)))
/-- The fully right-associated coefficient tensor `F ⊗ (G ⊗ (H ⊗ J))`. -/
abbrev coefficientC : EnrichedFunctor V (indices (A := A) (B := B) (C := C) (D := D)) V :=
  (inputProduct F G H J).comp V (AssociatorQuadIndex.indexC (selfData (V := V)))
/-- The coefficient tensor with parenthesization `(F ⊗ (G ⊗ H)) ⊗ J`. -/
abbrev coefficientD : EnrichedFunctor V (indices (A := A) (B := B) (C := C) (D := D)) V :=
  (inputProduct F G H J).comp V (AssociatorQuadIndex.indexD (selfData (V := V)))
/-- The coefficient tensor with parenthesization `F ⊗ ((G ⊗ H) ⊗ J)`. -/
abbrev coefficientE : EnrichedFunctor V (indices (A := A) (B := B) (C := C) (D := D)) V :=
  (inputProduct F G H J).comp V (AssociatorQuadIndex.indexE (selfData (V := V)))

/-- The coefficient associator from `((F ⊗ G) ⊗ H) ⊗ J` to `(F ⊗ G) ⊗ (H ⊗ J)`. -/
abbrev edgeAB (X : indices (A := A) (B := B) (C := C) (D := D)) :
    (coefficientA F G H J).obj X ≅ (coefficientB F G H J).obj X :=
  α_ (F.obj X.1.1.1 ⊗ G.obj X.1.1.2) (H.obj X.1.2) (J.obj X.2)
/-- The coefficient associator from `(F ⊗ G) ⊗ (H ⊗ J)` to `F ⊗ (G ⊗ (H ⊗ J))`. -/
abbrev edgeBC (X : indices (A := A) (B := B) (C := C) (D := D)) :
    (coefficientB F G H J).obj X ≅ (coefficientC F G H J).obj X :=
  α_ (F.obj X.1.1.1) (G.obj X.1.1.2) (H.obj X.1.2 ⊗ J.obj X.2)
/-- The first-three coefficient associator tensored with the identity of the fourth
  coefficient. -/
abbrev edgeAD (X : indices (A := A) (B := B) (C := C) (D := D)) :
    (coefficientA F G H J).obj X ≅ (coefficientD F G H J).obj X :=
  (α_ (F.obj X.1.1.1) (G.obj X.1.1.2) (H.obj X.1.2)) ⊗ᵢ Iso.refl (J.obj X.2)
/-- The coefficient associator from `(F ⊗ (G ⊗ H)) ⊗ J` to `F ⊗ ((G ⊗ H) ⊗ J)`. -/
abbrev edgeDE (X : indices (A := A) (B := B) (C := C) (D := D)) :
    (coefficientD F G H J).obj X ≅ (coefficientE F G H J).obj X :=
  α_ (F.obj X.1.1.1) (G.obj X.1.1.2 ⊗ H.obj X.1.2) (J.obj X.2)
/-- The final-three coefficient associator tensored on the left with the identity of the
  first coefficient. -/
abbrev edgeEC (X : indices (A := A) (B := B) (C := C) (D := D)) :
    (coefficientE F G H J).obj X ≅ (coefficientC F G H J).obj X :=
  Iso.refl (F.obj X.1.1.1) ⊗ᵢ (α_ (G.obj X.1.1.2) (H.obj X.1.2) (J.obj X.2))

/-- The original external coefficient word retains precisely the full composed four-input tensor
  map. -/
theorem coefficientA_map (X Y : indices (A := A) (B := B) (C := C) (D := D)) :
    (coefficientA F G H J).map X Y = (coefficientAprime F G H J).map X Y := by
  let A₁ : V := selfHom (F.obj X.1.1.1) (F.obj Y.1.1.1)
  let A₂ : V := selfHom (G.obj X.1.1.2) (G.obj Y.1.1.2)
  let A₃ : V := selfHom (H.obj X.1.2) (H.obj Y.1.2)
  let A₄ : V := selfHom (J.obj X.2) (J.obj Y.2)
  let A₁₂ : V := selfHom (F.obj X.1.1.1 ⊗ G.obj X.1.1.2) (F.obj Y.1.1.1 ⊗ G.obj Y.1.1.2)
  let A₁₂₃ : V := selfHom ((F.obj X.1.1.1 ⊗ G.obj X.1.1.2) ⊗ H.obj X.1.2)
    ((F.obj Y.1.1.1 ⊗ G.obj Y.1.1.2) ⊗ H.obj Y.1.2)
  let f : (X.1.1.1 ⟶[V] Y.1.1.1) ⟶ A₁ := F.map X.1.1.1 Y.1.1.1
  let g : (X.1.1.2 ⟶[V] Y.1.1.2) ⟶ A₂ := G.map X.1.1.2 Y.1.1.2
  let h : (X.1.2 ⟶[V] Y.1.2) ⟶ A₃ := H.map X.1.2 Y.1.2
  let j : (X.2 ⟶[V] Y.2) ⟶ A₄ := J.map X.2 Y.2
  let t : A₁ ⊗ A₂ ⟶ A₁₂ := (selfData (V := V)).tensorMap (F.obj X.1.1.1) (F.obj Y.1.1.1) (G.obj
    X.1.1.2) (G.obj Y.1.1.2)
  let u : A₁₂ ⊗ A₃ ⟶ A₁₂₃ := (selfData (V := V)).tensorMap
    (F.obj X.1.1.1 ⊗ G.obj X.1.1.2) (F.obj Y.1.1.1 ⊗ G.obj Y.1.1.2) (H.obj X.1.2) (H.obj Y.1.2)
  let v : A₁₂₃ ⊗ A₄ ⟶ selfHom (((F.obj X.1.1.1 ⊗ G.obj X.1.1.2) ⊗ H.obj X.1.2) ⊗ J.obj X.2)
    (((F.obj Y.1.1.1 ⊗ G.obj Y.1.1.2) ⊗ H.obj Y.1.2) ⊗ J.obj Y.2) := (selfData (V := V)).tensorMap
      ((F.obj X.1.1.1 ⊗ G.obj X.1.1.2) ⊗ H.obj X.1.2) ((F.obj Y.1.1.1 ⊗ G.obj Y.1.1.2) ⊗ H.obj
        Y.1.2)
      (J.obj X.2) (J.obj Y.2)
  change (((((f ⊗ₘ g) ≫ t) ⊗ₘ h) ≫ u) ⊗ₘ j) ≫ v =
    (((f ⊗ₘ g) ⊗ₘ h) ⊗ₘ j) ≫ (((t ⊗ₘ 𝟙 A₃) ≫ u) ⊗ₘ 𝟙 A₄) ≫ v
  simp only [tensorHom_comp_tensorHom_assoc, Category.comp_id]

/-- A complete original index Hom square remains complete after four genuine coefficient maps. -/
theorem precompose_map_congr
    (L R : EnrichedFunctor V (((V × V) × V) × V) V) (e : ∀ Z, L.obj Z ≅ R.obj Z)
    (h : ∀ Z W, R.map Z W = L.map Z W ≫ (Iso.eHomCongr V (e Z) (e W)).hom)
    (X Y : indices (A := A) (B := B) (C := C) (D := D)) :
    ((inputProduct F G H J).comp V R).map X Y =
      ((inputProduct F G H J).comp V L).map X Y ≫
        (Iso.eHomCongr V (e ((inputProduct F G H J).obj X)) (e ((inputProduct F G H J).obj Y))).hom
          := by
  let P : V := X ⟶[V] Y
  let S : V := ((inputProduct F G H J).obj X) ⟶[V] ((inputProduct F G H J).obj Y)
  let t : P ⟶ S := (inputProduct F G H J).map X Y
  let l : S ⟶ selfHom (L.obj ((inputProduct F G H J).obj X)) (L.obj ((inputProduct F G H J).obj Y))
    :=
    L.map ((inputProduct F G H J).obj X) ((inputProduct F G H J).obj Y)
  let r : S ⟶ selfHom (R.obj ((inputProduct F G H J).obj X)) (R.obj ((inputProduct F G H J).obj Y))
    :=
    R.map ((inputProduct F G H J).obj X) ((inputProduct F G H J).obj Y)
  let q := (Iso.eHomCongr V (e ((inputProduct F G H J).obj X)) (e ((inputProduct F G H J).obj
    Y))).hom
  have hr : r = l ≫ q := h _ _
  change t ≫ r = (t ≫ l) ≫ q
  rw [hr, Category.assoc]


/-- AB preserves the original complete four-input coefficient Hom action. -/
theorem edgeAB_map (X Y : indices (A := A) (B := B) (C := C) (D := D)) :
    (coefficientB F G H J).map X Y = (coefficientA F G H J).map X Y ≫
      (Iso.eHomCongr V (edgeAB F G H J X) (edgeAB F G H J Y)).hom := by
  let L : V := ((F.obj X.1.1.1 ⊗ G.obj X.1.1.2) ⊗ H.obj X.1.2) ⊗ J.obj X.2
  let M : V := ((F.obj Y.1.1.1 ⊗ G.obj Y.1.1.2) ⊗ H.obj Y.1.2) ⊗ J.obj Y.2
  let L' : V := (F.obj X.1.1.1 ⊗ G.obj X.1.1.2) ⊗ (H.obj X.1.2 ⊗ J.obj X.2)
  let M' : V := (F.obj Y.1.1.1 ⊗ G.obj Y.1.1.2) ⊗ (H.obj Y.1.2 ⊗ J.obj Y.2)
  let P : V := X ⟶[V] Y
  let l : P ⟶ selfHom L M := (coefficientA F G H J).map X Y
  let l' : P ⟶ selfHom L M := (coefficientAprime F G H J).map X Y
  let r : P ⟶ selfHom L' M' := (coefficientB F G H J).map X Y
  let q : selfHom L M ⟶ selfHom L' M' :=
    (Iso.eHomCongr V (edgeAB F G H J X) (edgeAB F G H J Y)).hom
  have h : r = l' ≫ q := precompose_map_congr F G H J
    (AssociatorQuadIndex.indexA (selfData (V := V))) (AssociatorQuadIndex.indexB (selfData (V :=
      V)))
    (AssociatorQuadIndex.edgeAB (selfData (V := V))) (AssociatorQuadIndex.edgeAB_map (selfData (V :=
      V))) X Y
  have hl : l = l' := coefficientA_map F G H J X Y
  change r = l ≫ q
  exact h.trans (congrArg (fun z => z ≫ q) hl.symm)

/-- AD preserves the original complete four-input coefficient Hom action. -/
theorem edgeAD_map (X Y : indices (A := A) (B := B) (C := C) (D := D)) :
    (coefficientD F G H J).map X Y = (coefficientA F G H J).map X Y ≫
      (Iso.eHomCongr V (edgeAD F G H J X) (edgeAD F G H J Y)).hom := by
  let L : V := ((F.obj X.1.1.1 ⊗ G.obj X.1.1.2) ⊗ H.obj X.1.2) ⊗ J.obj X.2
  let M : V := ((F.obj Y.1.1.1 ⊗ G.obj Y.1.1.2) ⊗ H.obj Y.1.2) ⊗ J.obj Y.2
  let L' : V := (F.obj X.1.1.1 ⊗ (G.obj X.1.1.2 ⊗ H.obj X.1.2)) ⊗ J.obj X.2
  let M' : V := (F.obj Y.1.1.1 ⊗ (G.obj Y.1.1.2 ⊗ H.obj Y.1.2)) ⊗ J.obj Y.2
  let P : V := X ⟶[V] Y
  let l : P ⟶ selfHom L M := (coefficientA F G H J).map X Y
  let l' : P ⟶ selfHom L M := (coefficientAprime F G H J).map X Y
  let r : P ⟶ selfHom L' M' := (coefficientD F G H J).map X Y
  let q : selfHom L M ⟶ selfHom L' M' :=
    (Iso.eHomCongr V (edgeAD F G H J X) (edgeAD F G H J Y)).hom
  have h : r = l' ≫ q := precompose_map_congr F G H J
    (AssociatorQuadIndex.indexA (selfData (V := V))) (AssociatorQuadIndex.indexD (selfData (V :=
      V)))
    (AssociatorQuadIndex.edgeAD (selfData (V := V))) (AssociatorQuadIndex.edgeAD_map (selfData (V :=
      V))) X Y
  have hl : l = l' := coefficientA_map F G H J X Y
  change r = l ≫ q
  exact h.trans (congrArg (fun z => z ≫ q) hl.symm)

/-- BC preserves the original complete four-input coefficient Hom action. -/
theorem edgeBC_map (X Y : indices (A := A) (B := B) (C := C) (D := D)) :
    (coefficientC F G H J).map X Y = (coefficientB F G H J).map X Y ≫
      (Iso.eHomCongr V (edgeBC F G H J X) (edgeBC F G H J Y)).hom := by
  exact precompose_map_congr F G H J
    (AssociatorQuadIndex.indexB (selfData (V := V))) (AssociatorQuadIndex.indexC (selfData (V :=
      V)))
    (AssociatorQuadIndex.edgeBC (selfData (V := V))) (AssociatorQuadIndex.edgeBC_map (selfData (V :=
      V))) X Y

/-- DE preserves the original complete four-input coefficient Hom action. -/
theorem edgeDE_map (X Y : indices (A := A) (B := B) (C := C) (D := D)) :
    (coefficientE F G H J).map X Y = (coefficientD F G H J).map X Y ≫
      (Iso.eHomCongr V (edgeDE F G H J X) (edgeDE F G H J Y)).hom := by
  exact precompose_map_congr F G H J
    (AssociatorQuadIndex.indexD (selfData (V := V))) (AssociatorQuadIndex.indexE (selfData (V :=
      V)))
    (AssociatorQuadIndex.edgeDE (selfData (V := V))) (AssociatorQuadIndex.edgeDE_map (selfData (V :=
      V))) X Y

/-- EC preserves the original complete four-input coefficient Hom action. -/
theorem edgeEC_map (X Y : indices (A := A) (B := B) (C := C) (D := D)) :
    (coefficientC F G H J).map X Y = (coefficientE F G H J).map X Y ≫
      (Iso.eHomCongr V (edgeEC F G H J X) (edgeEC F G H J Y)).hom := by
  exact precompose_map_congr F G H J
    (AssociatorQuadIndex.indexE (selfData (V := V))) (AssociatorQuadIndex.indexC (selfData (V :=
      V)))
    (AssociatorQuadIndex.edgeEC (selfData (V := V))) (AssociatorQuadIndex.edgeEC_map (selfData (V :=
      V))) X Y

/-- AB is natural on every whole four-input coefficient Hom, without a unit separator. -/
@[reassoc]
theorem edgeAB_naturality (X Y : indices (A := A) (B := B) (C := C) (D := D)) :
    MonoidalClosed.uncurry ((coefficientA F G H J).map X Y) ≫ (edgeAB F G H J Y).hom =
      ((edgeAB F G H J X).hom ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry ((coefficientB F G H J).map X Y) :=
  AssociatorQuadMaps.coefficient_naturality (coefficientA F G H J) (coefficientB F G H J)
    (edgeAB F G H J) (edgeAB_map F G H J) X Y

/-- AD is natural on every whole four-input coefficient Hom, without a unit separator. -/
@[reassoc]
theorem edgeAD_naturality (X Y : indices (A := A) (B := B) (C := C) (D := D)) :
    MonoidalClosed.uncurry ((coefficientA F G H J).map X Y) ≫ (edgeAD F G H J Y).hom =
      ((edgeAD F G H J X).hom ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry ((coefficientD F G H J).map X Y) :=
  AssociatorQuadMaps.coefficient_naturality (coefficientA F G H J) (coefficientD F G H J)
    (edgeAD F G H J) (edgeAD_map F G H J) X Y

/-- BC is natural on every whole four-input coefficient Hom, without a unit separator. -/
@[reassoc]
theorem edgeBC_naturality (X Y : indices (A := A) (B := B) (C := C) (D := D)) :
    MonoidalClosed.uncurry ((coefficientB F G H J).map X Y) ≫ (edgeBC F G H J Y).hom =
      ((edgeBC F G H J X).hom ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry ((coefficientC F G H J).map X Y) :=
  AssociatorQuadMaps.coefficient_naturality (coefficientB F G H J) (coefficientC F G H J)
    (edgeBC F G H J) (edgeBC_map F G H J) X Y

/-- DE is natural on every whole four-input coefficient Hom, without a unit separator. -/
@[reassoc]
theorem edgeDE_naturality (X Y : indices (A := A) (B := B) (C := C) (D := D)) :
    MonoidalClosed.uncurry ((coefficientD F G H J).map X Y) ≫ (edgeDE F G H J Y).hom =
      ((edgeDE F G H J X).hom ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry ((coefficientE F G H J).map X Y) :=
  AssociatorQuadMaps.coefficient_naturality (coefficientD F G H J) (coefficientE F G H J)
    (edgeDE F G H J) (edgeDE_map F G H J) X Y

/-- EC is natural on every whole four-input coefficient Hom, without a unit separator. -/
@[reassoc]
theorem edgeEC_naturality (X Y : indices (A := A) (B := B) (C := C) (D := D)) :
    MonoidalClosed.uncurry ((coefficientE F G H J).map X Y) ≫ (edgeEC F G H J Y).hom =
      ((edgeEC F G H J X).hom ⊗ₘ 𝟙 (X ⟶[V] Y)) ≫
        MonoidalClosed.uncurry ((coefficientC F G H J).map X Y) :=
  AssociatorQuadMaps.coefficient_naturality (coefficientE F G H J) (coefficientC F G H J)
    (edgeEC F G H J) (edgeEC_map F G H J) X Y

/-- The same five original positive coefficient maps satisfy the full original coefficient pentagon.
-/
theorem edge_pentagon (X : indices (A := A) (B := B) (C := C) (D := D)) :
    (edgeAB F G H J X).hom ≫ (edgeBC F G H J X).hom =
      (edgeAD F G H J X).hom ≫ (edgeDE F G H J X).hom ≫ (edgeEC F G H J X).hom := by
  change (α_ (F.obj X.1.1.1 ⊗ G.obj X.1.1.2) (H.obj X.1.2) (J.obj X.2)).hom ≫
      (α_ (F.obj X.1.1.1) (G.obj X.1.1.2) (H.obj X.1.2 ⊗ J.obj X.2)).hom =
    ((α_ (F.obj X.1.1.1) (G.obj X.1.1.2) (H.obj X.1.2)).hom ⊗ₘ 𝟙 (J.obj X.2)) ≫
      (α_ (F.obj X.1.1.1) (G.obj X.1.1.2 ⊗ H.obj X.1.2) (J.obj X.2)).hom ≫
      (𝟙 (F.obj X.1.1.1) ⊗ₘ (α_ (G.obj X.1.1.2) (H.obj X.1.2) (J.obj X.2)).hom)
  simp only [tensorHom_id, id_tensorHom]
  monoidal
end CategoryTheory.EnrichedDayKernel.AssociatorQuadCoefficient
