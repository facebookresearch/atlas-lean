/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.Closed
public import MathlibExt.Topology.Category.PointedCGWH.Zero
public import MathlibExt.Topology.Category.PointedCGWH.Separator

/-!
# Generalized points of pointed CGWH spaces

Maps from the smash unit select the points of a pointed CGWH space. The
selected finite unit point and the free-point adjunction identify their
values. Pairing these maps uses the chosen smash unitors and tensor product;
the resulting value, zero, naturality, associativity, and extensionality laws
apply to arbitrary pointed CGWH objects.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v r

open CategoryTheory CategoryTheory.Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed ZeroObject

attribute [local instance] HasZeroObject.zeroMorphismsOfZeroObject

namespace PointedCGWH

/-- The original nonbasepoint of the native smash unit. -/
def unitFinite : (𝟙_ PointedCGWH.{u, v}).right :=
  (coprod.inr : CGWH.point.{u, v} ⟶
    CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) PUnit.unit

/-- Evaluate a generalized native point at the original finite unit point. -/
def pointValue {X : PointedCGWH.{u, v}} (p : 𝟙_ PointedCGWH.{u, v} ⟶ X) : X.right :=
  p.right unitFinite

/-- The original free-point adjunction selects every point of a native pointed object. -/
def pointAt (X : PointedCGWH.{u, v}) (x : X.right) : 𝟙_ PointedCGWH.{u, v} ⟶ X :=
  Under.homMk (coprod.desc X.hom ((CGWH.pointHomEquiv X.right).symm x)) (by
    have h : (𝟙_ PointedCGWH.{u, v}).hom =
        (coprod.inl : CGWH.point.{u, v} ⟶ CGWH.point.{u, v} ⨿ CGWH.point.{u, v}) :=
      (Under.costar_obj_hom CGWH.point CGWH.point).trans (coprod.inl_desc _ _)
    exact (congrArg (fun g => g ≫
      coprod.desc X.hom ((CGWH.pointHomEquiv X.right).symm x)) h).trans
      (coprod.inl_desc _ _))

@[simp]
theorem pointAt_value (X : PointedCGWH.{u, v}) (x : X.right) : pointValue (pointAt X x) = x := by
  let f : CGWH.point.{u, v} ⟶ X.right := (CGWH.pointHomEquiv X.right).symm x
  have h := ConcreteCategory.congr_hom (coprod.inr_desc X.hom f)
    (show CGWH.point.{u, v} from PUnit.unit)
  rw [ConcreteCategory.comp_apply] at h
  change pointValue (pointAt X x) = f PUnit.unit at h
  exact h.trans (CGWH.pointHomEquiv_symm_apply_apply X.right x PUnit.unit)

/-- The actual finite unit point determines every native generalized point map. -/
theorem pointValue_injective (X : PointedCGWH.{u, v}) :
    Function.Injective (pointValue (X := X)) := by
  intro f g h
  let E := (Under.costarAdjForget CGWH.point.{u, v}).homEquiv CGWH.point.{u, v} X
  apply E.injective
  apply (CGWH.pointHomEquiv X.right).injective
  exact h

@[simp]
theorem pointValue_comp {X Y : PointedCGWH.{u, v}}
    (p : 𝟙_ PointedCGWH.{u, v} ⟶ X) (f : X ⟶ Y) :
    pointValue (p ≫ f) = f.right (pointValue p) := rfl

/-- Point selection is natural for the original native continuous based maps. -/
theorem pointAt_naturality {X Y : PointedCGWH.{u, v}}
    (f : X ⟶ Y) (x : X.right) : pointAt X x ≫ f = pointAt Y (f.right x) := by
  apply pointValue_injective Y
  simp only [pointValue_comp, pointAt_value]

/-- The categorical zero generalized point has the actual original basepoint value. -/
theorem pointValue_zero (X : PointedCGWH.{u, v}) :
    pointValue (0 : 𝟙_ PointedCGWH.{u, v} ⟶ X) = X.hom PUnit.unit := by
  let Z : PointedCGWH.{u, v} := Under.mk (𝟙 CGWH.point.{u, v})
  let p : 𝟙_ PointedCGWH.{u, v} ⟶ Z :=
    Under.homMk (CGWH.point_isTerminal.from (𝟙_ PointedCGWH.{u, v}).right)
      (CGWH.point_isTerminal.hom_ext _ _)
  let q : Z ⟶ X := Under.homMk X.hom (by simp [Z])
  have hZ : IsZero Z := (show IsInitial Z from Under.mkIdInitial).isZero
  have hpq : p ≫ q = 0 := by rw [hZ.eq_zero_of_src q, comp_zero]
  rw [← hpq, pointValue_comp]
  change X.hom ((CGWH.point_isTerminal.from (𝟙_ PointedCGWH.{u, v}).right) unitFinite) = _
  congr 1

/-- The selected point map of the actual basepoint is the categorical zero. -/
theorem pointAt_basepoint (X : PointedCGWH.{u, v}) :
    pointAt X (X.hom PUnit.unit) = 0 := by
  apply pointValue_injective X
  rw [pointAt_value, pointValue_zero]

/-- Pair two generalized points using the chosen smash unitor and tensor product. -/
def pointPair {X Y : PointedCGWH.{u, r}}
    (x : 𝟙_ PointedCGWH.{u, r} ⟶ X)
    (y : 𝟙_ PointedCGWH.{u, r} ⟶ Y) :
    𝟙_ PointedCGWH.{u, r} ⟶ X ⊗ Y :=
  (λ_ (𝟙_ PointedCGWH.{u, r})).inv ≫ (x ⊗ₘ y)

/-- The chosen pairing is natural in both pointed maps. -/
theorem pointPairNatural {X Y X' Y' : PointedCGWH.{u, r}}
    (x : 𝟙_ PointedCGWH.{u, r} ⟶ X)
    (y : 𝟙_ PointedCGWH.{u, r} ⟶ Y) (f : X ⟶ X') (g : Y ⟶ Y') :
    pointPair x y ≫ (f ⊗ₘ g) = pointPair (x ≫ f) (y ≫ g) := by
  dsimp only [pointPair]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun q => (λ_ (𝟙_ PointedCGWH.{u, r})).inv ≫ q)
      (tensorHom_comp_tensorHom x y f g))

/-- Point tensor factors through the original right unitor, without a new pairing map. -/
theorem pointPair_factor_right {X Y : PointedCGWH.{u, v}}
    (p : 𝟙_ PointedCGWH.{u, v} ⟶ X) (q : 𝟙_ PointedCGWH.{u, v} ⟶ Y) :
    pointPair p q = p ≫ (ρ_ X).inv ≫ X ◁ q := by
  simpa only [pointPair, unitors_inv_equal] using
    rightUnitor_inv_comp_tensorHom p q

/-- Point tensor also factors through the original left unitor. -/
theorem pointPair_factor_left {X Y : PointedCGWH.{u, v}}
    (p : 𝟙_ PointedCGWH.{u, v} ⟶ X) (q : 𝟙_ PointedCGWH.{u, v} ⟶ Y) :
    pointPair p q = q ≫ (λ_ Y).inv ≫ (p ⊗ₘ 𝟙 Y) := by
  simpa only [pointPair, tensorHom_id] using leftUnitor_inv_comp_tensorHom p q

/-- Nested point pairings follow the chosen smash associator. -/
theorem pointPair_associator_inv {X Y Z : PointedCGWH.{u, v}}
    (p : 𝟙_ PointedCGWH.{u, v} ⟶ X) (q : 𝟙_ PointedCGWH.{u, v} ⟶ Y)
    (r : 𝟙_ PointedCGWH.{u, v} ⟶ Z) :
    pointPair p (pointPair q r) ≫ (α_ X Y Z).inv = pointPair (pointPair p q) r := by
  let I := 𝟙_ PointedCGWH.{u, v}
  have hleft : p ⊗ₘ ((λ_ I).inv ≫ (q ⊗ₘ r)) =
      (𝟙 I ⊗ₘ (λ_ I).inv) ≫ (p ⊗ₘ (q ⊗ₘ r)) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  have hright : ((λ_ I).inv ≫ (p ⊗ₘ q)) ⊗ₘ r =
      ((λ_ I).inv ⊗ₘ 𝟙 I) ≫ ((p ⊗ₘ q) ⊗ₘ r) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  have hunit : (λ_ I).inv ≫ (𝟙 I ⊗ₘ (λ_ I).inv) ≫ (α_ I I I).inv =
      (λ_ I).inv ≫ ((λ_ I).inv ⊗ₘ 𝟙 I) := by monoidal
  simp only [pointPair]
  rw [hleft, hright]
  simp only [Category.assoc]
  rw [associator_inv_naturality]
  exact congrArg (fun f => f ≫ ((p ⊗ₘ q) ⊗ₘ r)) hunit

@[simp]
theorem pointPair_zero_left {X Y : PointedCGWH.{u, v}}
    (q : 𝟙_ PointedCGWH.{u, v} ⟶ Y) : pointPair (0 : 𝟙_ PointedCGWH.{u, v} ⟶ X) q = 0 := by
  let _ : (tensorRight (𝟙_ PointedCGWH.{u, v})).PreservesZeroMorphisms := inferInstance
  rw [pointPair, tensorHom_def]
  change (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
    (tensorRight (𝟙_ PointedCGWH.{u, v})).map 0 ≫ _ = 0
  rw [Functor.map_zero, zero_comp, comp_zero]

@[simp]
theorem pointPair_zero_right {X Y : PointedCGWH.{u, v}}
    (p : 𝟙_ PointedCGWH.{u, v} ⟶ X) : pointPair p (0 : 𝟙_ PointedCGWH.{u, v} ⟶ Y) = 0 := by
  let _ : (tensorLeft (𝟙_ PointedCGWH.{u, v})).PreservesZeroMorphisms := inferInstance
  rw [pointPair, tensorHom_def']
  change (λ_ (𝟙_ PointedCGWH.{u, v})).inv ≫
    (tensorLeft (𝟙_ PointedCGWH.{u, v})).map 0 ≫ _ = 0
  rw [Functor.map_zero, zero_comp, comp_zero]

/-- Testing all actual left unit points determines maps from a native smash tensor. -/
theorem tensorLeftPoint_hom_ext {X Y Z : PointedCGWH.{u, v}}
    {f g : X ⊗ Y ⟶ Z}
    (h : ∀ p : 𝟙_ PointedCGWH.{u, v} ⟶ X,
      (λ_ Y).inv ≫ (p ⊗ₘ 𝟙 Y) ≫ f = (λ_ Y).inv ≫ (p ⊗ₘ 𝟙 Y) ≫ g) : f = g := by
  apply (cancel_epi (β_ Y X).hom).1
  apply MonoidalClosed.curry_injective
  apply PointedCGWH.isSeparator_tensorUnit.def
  intro p
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry]
  apply (cancel_epi (ρ_ Y).inv).1
  rw [braiding_naturality_right_assoc, braiding_naturality_right_assoc,
    braiding_tensorUnit_right]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [tensorHom_id] using h p

/-- The two independent native point parameters determine every map from the full smash. -/
theorem tensorPoint_hom_ext {X Y Z : PointedCGWH.{u, v}}
    {f g : X ⊗ Y ⟶ Z}
    (h : ∀ (p : 𝟙_ PointedCGWH.{u, v} ⟶ X) (q : 𝟙_ PointedCGWH.{u, v} ⟶ Y),
      pointPair p q ≫ f = pointPair p q ≫ g) : f = g := by
  apply tensorLeftPoint_hom_ext
  intro p
  apply PointedCGWH.isSeparator_tensorUnit.def
  intro q
  simpa only [pointPair_factor_left, Category.assoc] using h p q

/-- Three independent point parameters determine maps from a nested smash product. -/
theorem tensorTriplePoint_hom_ext {X Y Z T : PointedCGWH.{u, v}}
    {f g : X ⊗ (Y ⊗ Z) ⟶ T}
    (h : ∀ (p : 𝟙_ PointedCGWH.{u, v} ⟶ X)
      (q : 𝟙_ PointedCGWH.{u, v} ⟶ Y) (r : 𝟙_ PointedCGWH.{u, v} ⟶ Z),
      pointPair p (pointPair q r) ≫ f = pointPair p (pointPair q r) ≫ g) : f = g := by
  apply tensorLeftPoint_hom_ext
  intro p
  apply tensorPoint_hom_ext
  intro q r
  simpa only [pointPair_factor_left, Category.assoc] using h p q r

/-- The canonical native product point is the original chosen product preimage. -/
theorem canonicalProduct_choose (X Y : CGWH.{u, v}) (x : X) (y : Y) :
    Classical.choose ((CGWH.prodComparisonToTop_bijective X Y).2 (x, y)) =
      (CGWH.tensorEquivProd X Y).symm (x, y) := by
  apply (CGWH.prodComparisonToTop_bijective X Y).1
  have hc := Classical.choose_spec ((CGWH.prodComparisonToTop_bijective X Y).2 (x, y))
  rw [← CGWH.tensorEquivProd_eq_prodComparisonToTop]
  exact hc.trans ((CGWH.tensorEquivProd X Y).apply_symm_apply (x, y)).symm

/-- The native smash-unit point tensor has its exact original smash-presentation value. -/
theorem pointPair_value {X Y : PointedCGWH.{u, v}}
    (p : 𝟙_ PointedCGWH.{u, v} ⟶ X) (q : 𝟙_ PointedCGWH.{u, v} ⟶ Y) :
    pointValue (pointPair p q) =
      (CategoryTheory.Pointed.smashPresentation CGWH.point CGWH.point_isTerminal X Y).2.1.inl
        ((CGWH.tensorEquivProd X.right Y.right).symm (pointValue p, pointValue q)) := by
  let _ : BraidedCategory CGWH.{u, v} := BraidedCategory.ofCartesianMonoidalCategory
  let _ : SymmetricCategory CGWH.{u, v} := inferInstance
  let P := CGWH.point.{u, v}
  let U := 𝟙_ PointedCGWH.{u, v}
  let pUnit := CGWH.point_isTerminal.uniqueUpToIso
    CartesianMonoidalCategory.isTerminalTensorUnit
  let free : P ⟶ U.right := coprod.inr
  let qU : U.right ⊗ U.right ⟶ (U ⊗ U).right :=
    (CategoryTheory.Pointed.smashPresentation P CGWH.point_isTerminal U U).2.1.inl
  let qXY : X.right ⊗ Y.right ⟶ (X ⊗ Y).right :=
    (CategoryTheory.Pointed.smashPresentation P CGWH.point_isTerminal X Y).2.1.inl
  let cU := (CGWH.tensorEquivProd U.right U.right).symm (unitFinite, unitFinite)
  have hInput : (λ_ U).inv.right unitFinite = qU cU := by
    have h := ConcreteCategory.congr_hom
      (CategoryTheory.Pointed.smashLeftUnitor_inv_free P CGWH.point_isTerminal U) unitFinite
    let w0 := (λ_ U.right).inv unitFinite
    let w1 := (pUnit.inv ▷ U.right) w0
    let w2 := (free ▷ U.right) w1
    have hc : w2 = cU := by
      apply (CGWH.tensorEquivProd U.right U.right).injective
      have hCU : CGWH.tensorEquivProd U.right U.right cU = (unitFinite, unitFinite) :=
        (CGWH.tensorEquivProd U.right U.right).apply_symm_apply (unitFinite, unitFinite)
      rw [hCU]
      apply Prod.ext
      · rw [CGWH.tensorEquivProd_apply_fst]
        have h1 := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.whiskerRight_fst free U.right) w1
        have h0 := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.whiskerRight_fst pUnit.inv U.right) w0
        simp only [ConcreteCategory.comp_apply] at h1 h0
        rw [h1, h0]
        change (coprod.inr : P ⟶ P ⨿ P) _ = unitFinite
        congr 1
      · rw [CGWH.tensorEquivProd_apply_snd]
        have h1 := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.whiskerRight_snd free U.right) w1
        have h0 := ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.whiskerRight_snd pUnit.inv U.right) w0
        simp only [ConcreteCategory.comp_apply] at h1 h0
        rw [h1, h0]
        exact ConcreteCategory.congr_hom
          (CartesianMonoidalCategory.leftUnitor_inv_snd U.right) unitFinite
    have hAt : (λ_ U).inv.right unitFinite = qU w2 := h
    exact hAt.trans (congrArg (fun x => qU x) hc)
  have hn := ConcreteCategory.congr_hom
    (CategoryTheory.Pointed.smashQuotient_naturality P CGWH.point_isTerminal p q) cU
  have hc := CGWH.tensorEquivProd_symm_map p.right q.right unitFinite unitFinite
  change (p ⊗ₘ q).right (qU cU) =
    qXY ((p.right ⊗ₘ q.right) cU) at hn
  change (p ⊗ₘ q).right ((λ_ U).inv.right unitFinite) = _
  rw [hInput, hn, hc]
  rfl

end PointedCGWH
