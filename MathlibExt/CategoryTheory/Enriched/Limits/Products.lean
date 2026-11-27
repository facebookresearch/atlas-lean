/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Enriched.Limits.HasConicalProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Basic.Finite.Sigma
public import MathlibExt.CategoryTheory.Enriched.Ordinary.Basic

public import MathlibExt.CategoryTheory.Limits.Shapes.IteratedProducts

namespace CategoryTheory.Enriched

universe w w' v' v u u'

open CategoryTheory Limits

/-- A category has finite conical products when every finite discrete diagram has a conical limit.

As for `Limits.HasFiniteProducts`, it is enough to require the diagrams indexed by `Fin n`;
conical limits over arbitrary finite types are transported along an equivalence. -/
public class HasFiniteConicalProducts
    (V : outParam <| Type u') [Category.{v'} V] [MonoidalCategory V]
    (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C] : Prop where
  /-- Conical products indexed by `Fin n` exist for every `n`. -/
  conicalOut (n : ℕ) : HasConicalLimitsOfShape (Discrete (Fin n)) V C

public instance hasConicalLimitsOfShape_discrete_of_finite
    (V : Type u') [Category.{v'} V] [MonoidalCategory V]
    (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]
    [HasFiniteConicalProducts V C] (I : Type w) [Finite I] :
    HasConicalLimitsOfShape (Discrete I) V C := by
  rcases Finite.exists_equiv_fin I with ⟨n, ⟨e⟩⟩
  let : HasConicalLimitsOfShape (Discrete (Fin n)) V C :=
    HasFiniteConicalProducts.conicalOut n
  exact HasConicalLimitsOfShape.of_equiv V C (Discrete.equivalence e.symm).functor

public instance hasFiniteProducts_of_hasFiniteConicalProducts
    (V : outParam <| Type u') [Category.{v'} V] [MonoidalCategory V]
    (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]
    [h : HasFiniteConicalProducts V C] : HasFiniteProducts C where
  out n := by
    let _ : HasConicalLimitsOfShape (Discrete (Fin n)) V C := h.conicalOut n
    exact ⟨fun _ => inferInstance⟩

/-- All conical products in the base universe imply finite conical products. -/
public instance (priority := 10) hasFiniteConicalProducts_of_hasConicalProducts
    (V : Type u') [Category.{v'} V] [MonoidalCategory V]
    (C : Type u) [Category.{v} C] [EnrichedOrdinaryCategory V C]
    [HasConicalProducts.{0} V C] : HasFiniteConicalProducts V C where
  conicalOut _ := inferInstance

private theorem hasProduct_eCoyoneda_obj
    (V : Type u') [Category.{v'} V] [MonoidalCategory V]
    {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]
    {I : Type w} (X : C) (Y : I → C)
    [HasConicalProduct V Y] :
    HasProduct fun i => (eCoyoneda V X).obj (Y i) := by
  have _ : HasLimit ((Discrete.functor Y) ⋙ eCoyoneda V X) := inferInstance
  exact hasLimit_of_iso (Discrete.compNatIsoDiscrete Y (eCoyoneda V X))

/-- A conical product in `C` induces the corresponding product of enriched hom objects because
`eCoyoneda` preserves conical limits. -/
public instance hasProduct_eHom_of_hasConicalProduct
    (V : Type u') [Category.{v'} V] [MonoidalCategory V]
    {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]
    {I : Type w} (X : C) (Y : I → C)
    [HasConicalProduct V Y] : HasProduct fun i => (X ⟶[V] Y i) := by
  have h : (fun i => (eCoyoneda V X).obj (Y i)) =
      fun i => (X ⟶[V] Y i) := by
    ext i
    simp [eCoyoneda, eHomFunctor]
  exact h ▸ hasProduct_eCoyoneda_obj V X Y

variable (V : Type u') [Category.{v'} V] [MonoidalCategory V]
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory V C]
variable {I : Type w}

/-- The canonical comparison between `X ⟶[V] ∏ᶜ Y` and `∏ᶜ X ⟶[V] Y`,
obtained from preservation of conical products by `eCoyoneda`. -/
public noncomputable def eHomProductIso
    (X : C) (Y : I → C)
    [HasConicalProduct V Y] :
    (X ⟶[V] ∏ᶜ Y) ≅ ∏ᶜ fun i => (X ⟶[V] Y i) := by
  let _ : HasProduct (fun i => (eCoyoneda V X).obj (Y i)) :=
    hasProduct_eCoyoneda_obj V X Y
  exact PreservesProduct.iso (eCoyoneda V X) Y

/-- The forward direction of `eHomProductIso` composed with a product
projection equals the enriched whiskering of the ordinary projection. -/
public lemma eHomProductIso_hom_π
    (X : C) (Y : I → C)
    [HasConicalProduct V Y] (i : I) :
    (eHomProductIso V X Y).hom ≫ Pi.π (fun j => (X ⟶[V] Y j)) i =
      eHomWhiskerLeft V X (Pi.π Y i) := by
  let _ : HasProduct (fun i => (eCoyoneda V X).obj (Y i)) :=
    hasProduct_eCoyoneda_obj V X Y
  have h_comp :
      piComparison (eCoyoneda V X) Y ≫
          Pi.π (fun j => (eCoyoneda V X).obj (Y j)) i =
        (eCoyoneda V X).map (Pi.π Y i) :=
    piComparison_comp_π (eCoyoneda V X) Y i
  have h_iso :
      (eHomProductIso V X Y).hom =
        piComparison (eCoyoneda V X) Y := by
    dsimp [eHomProductIso]
  have h :
      piComparison (eCoyoneda V X) Y ≫
          Pi.π (fun j => (X ⟶[V] Y j)) i =
        eHomWhiskerLeft V X (Pi.π Y i) := by
    simpa [eCoyoneda, eHomFunctor] using h_comp
  have h1 :
      (eHomProductIso V X Y).hom ≫ Pi.π (fun j => (X ⟶[V] Y j)) i =
        piComparison (eCoyoneda V X) Y ≫
          Pi.π (fun j => (X ⟶[V] Y j)) i :=
    congrArg (· ≫ Pi.π (fun j => (X ⟶[V] Y j)) i) h_iso
  exact h1.trans h

/-- The inverse direction of `eHomProductIso` composed with enriched
whiskering recovers the product projection. -/
public lemma eHomProductIso_inv_eHomWhiskerLeft
    (X : C) (Y : I → C)
    [HasConicalProduct V Y] (i : I) :
    (eHomProductIso V X Y).inv ≫ eHomWhiskerLeft V X (Pi.π Y i) =
      Pi.π (fun j => (X ⟶[V] Y j)) i := by
  let _ : HasProduct (fun i => (eCoyoneda V X).obj (Y i)) :=
    hasProduct_eCoyoneda_obj V X Y
  have h1 := eHomProductIso_hom_π V X Y i
  calc (eHomProductIso V X Y).inv ≫ eHomWhiskerLeft V X (Pi.π Y i)
      = (eHomProductIso V X Y).inv ≫
          (eHomProductIso V X Y).hom ≫
          Pi.π (fun j => (X ⟶[V] Y j)) i := by
        rw [h1]
      _ = Pi.π (fun j => (X ⟶[V] Y j)) i := by
        simp

/-- Lift a family `f i : Z ⟶ X ⟶[V] Y i` to a map into
`X ⟶[V] ∏ᶜ Y` via `eHomProductIso`. -/
public noncomputable def eHomProductLift
    {Z : V} (X : C) (Y : I → C)
    [HasConicalProduct V Y]
    (f : ∀ i, Z ⟶ (X ⟶[V] Y i)) :
    Z ⟶ (X ⟶[V] ∏ᶜ Y) :=
  Pi.lift f ≫ (eHomProductIso V X Y).inv

/-- The lifted map composed with whiskered projection recovers the
original components. -/
public lemma eHomProductLift_comp_eHomWhiskerLeft
    {Z : V} (X : C) (Y : I → C)
    [HasConicalProduct V Y]
    (f : ∀ i, Z ⟶ (X ⟶[V] Y i)) (i : I) :
    eHomProductLift V X Y f ≫ eHomWhiskerLeft V X (Pi.π Y i) = f i := by
  let _ : HasProduct (fun i => (eCoyoneda V X).obj (Y i)) := by
    exact hasProduct_eCoyoneda_obj V X Y
  simp [eHomProductLift, eHomProductIso_inv_eHomWhiskerLeft]

/-- Ordinary precomposition naturality for `eHomProductLift`:
postcomposing the source with `g` before lifting equals lifting the
family `g ≫ f i`. -/
@[reassoc]
public theorem comp_eHomProductLift
    {Z Z' : V} (X : C) (Y : I → C)
    [HasConicalProduct V Y]
    (g : Z ⟶ Z') (f : ∀ i, Z' ⟶ (X ⟶[V] Y i)) :
    g ≫ eHomProductLift V X Y f =
      eHomProductLift V X Y (fun i => g ≫ f i) := by
  have hLift : g ≫ Pi.lift f = Pi.lift (fun i => g ≫ f i) := by
    apply Pi.hom_ext
    intro i
    simp
  calc g ≫ eHomProductLift V X Y f
      = g ≫ (Pi.lift f ≫ (eHomProductIso V X Y).inv) := rfl
    _ = (g ≫ Pi.lift f) ≫ (eHomProductIso V X Y).inv := by
        rw [← Category.assoc]
    _ = Pi.lift (fun i => g ≫ f i) ≫ (eHomProductIso V X Y).inv := by
        rw [hLift]
    _ = eHomProductLift V X Y (fun i => g ≫ f i) := rfl

/-- Precomposition/source-whiskering naturality for `eHomProductLift`:
whiskering on the enriched source commutes with the product lift.
This is the first generic law needed for endomorphism-operad substitution. -/
public lemma eHomProductLift_eHomWhiskerRight
    {Z : V} (X X' : C) (Y : I → C)
    [HasConicalProduct V Y]
    (g : X' ⟶ X) (f : ∀ i, Z ⟶ (X ⟶[V] Y i)) :
    eHomProductLift V X Y f ≫ eHomWhiskerRight V g (∏ᶜ Y) =
      eHomProductLift V X' Y
        (fun i => f i ≫ eHomWhiskerRight V g (Y i)) := by
  have hEq : (eHomProductLift V X Y f ≫ eHomWhiskerRight V g (∏ᶜ Y) ≫
      (eHomProductIso V X' Y).hom) =
      (eHomProductLift V X' Y
        (fun i => f i ≫ eHomWhiskerRight V g (Y i)) ≫
      (eHomProductIso V X' Y).hom) := by
    apply Pi.hom_ext
    intro i
    have lhs : ((eHomProductLift V X Y f ≫ eHomWhiskerRight V g (∏ᶜ Y) ≫
        (eHomProductIso V X' Y).hom) ≫ Pi.π _ i) =
        f i ≫ eHomWhiskerRight V g (Y i) := by
      calc ((eHomProductLift V X Y f ≫ eHomWhiskerRight V g (∏ᶜ Y) ≫
          (eHomProductIso V X' Y).hom) ≫ Pi.π _ i)
          = (eHomProductLift V X Y f ≫ eHomWhiskerRight V g (∏ᶜ Y)) ≫
            ((eHomProductIso V X' Y).hom ≫ Pi.π _ i) := by
            simp only [Category.assoc]
        _ = (eHomProductLift V X Y f ≫ eHomWhiskerRight V g (∏ᶜ Y)) ≫
            eHomWhiskerLeft V X' (Pi.π Y i) := by
            simp only [eHomProductIso_hom_π]
        _ = eHomProductLift V X Y f ≫
            (eHomWhiskerRight V g (∏ᶜ Y) ≫
              eHomWhiskerLeft V X' (Pi.π Y i)) := by
            simp only [Category.assoc]
        _ = eHomProductLift V X Y f ≫
            (eHomWhiskerLeft V X (Pi.π Y i) ≫
              eHomWhiskerRight V g (Y i)) := by
            rw [← eHom_whisker_exchange]
        _ = (eHomProductLift V X Y f ≫
            eHomWhiskerLeft V X (Pi.π Y i)) ≫
            eHomWhiskerRight V g (Y i) := by
            simp only [Category.assoc]
        _ = f i ≫ eHomWhiskerRight V g (Y i) := by
            simp only [eHomProductLift_comp_eHomWhiskerLeft]
    have rhs : ((eHomProductLift V X' Y
        (fun j => f j ≫ eHomWhiskerRight V g (Y j)) ≫
        (eHomProductIso V X' Y).hom) ≫ Pi.π _ i) =
        f i ≫ eHomWhiskerRight V g (Y i) := by
      calc ((eHomProductLift V X' Y
          (fun j => f j ≫ eHomWhiskerRight V g (Y j)) ≫
          (eHomProductIso V X' Y).hom) ≫ Pi.π _ i)
          = eHomProductLift V X' Y
            (fun j => f j ≫ eHomWhiskerRight V g (Y j)) ≫
            ((eHomProductIso V X' Y).hom ≫ Pi.π _ i) := by
            simp only [Category.assoc]
        _ = eHomProductLift V X' Y
            (fun j => f j ≫ eHomWhiskerRight V g (Y j)) ≫
            eHomWhiskerLeft V X' (Pi.π Y i) := by
            simp only [eHomProductIso_hom_π]
        _ = f i ≫ eHomWhiskerRight V g (Y i) := by
            simp only [eHomProductLift_comp_eHomWhiskerLeft]
    rw [lhs, rhs]
  calc eHomProductLift V X Y f ≫ eHomWhiskerRight V g (∏ᶜ Y)
      = (eHomProductLift V X Y f ≫ eHomWhiskerRight V g (∏ᶜ Y) ≫
        (eHomProductIso V X' Y).hom) ≫ (eHomProductIso V X' Y).inv := by
        simp
    _ = (eHomProductLift V X' Y
          (fun i => f i ≫ eHomWhiskerRight V g (Y i)) ≫
        (eHomProductIso V X' Y).hom) ≫ (eHomProductIso V X' Y).inv := by
        rw [hEq]
    _ = eHomProductLift V X' Y
        (fun i => f i ≫ eHomWhiskerRight V g (Y i)) := by
        simp

/-- Postcomposition/reindexed-product law via `Pi.map'`:
`eHomProductLift` commutes with enriched post-whiskering of a reindexed product map.
This is the second generic law needed for endomorphism-operad substitution. -/
public lemma eHomProductLift_comp_eHomWhiskerLeft_piMap'
    {Z : V} (X : C) {J : Type w'}
    (Y : I → C) (Y' : J → C)
    [HasConicalProduct V Y] [HasConicalProduct V Y']
    (p : J → I) (q : ∀ j, Y (p j) ⟶ Y' j)
    (f : ∀ i, Z ⟶ (X ⟶[V] Y i)) :
    eHomProductLift V X Y f ≫ eHomWhiskerLeft V X (Pi.map' p q) =
      eHomProductLift V X Y'
        (fun j => f (p j) ≫ eHomWhiskerLeft V X (q j)) := by
  have hEq : (eHomProductLift V X Y f ≫
      eHomWhiskerLeft V X (Pi.map' p q) ≫
      (eHomProductIso V X Y').hom) =
      (eHomProductLift V X Y'
        (fun j => f (p j) ≫ eHomWhiskerLeft V X (q j)) ≫
      (eHomProductIso V X Y').hom) := by
    apply Pi.hom_ext
    intro j
    have lhs : ((eHomProductLift V X Y f ≫
        eHomWhiskerLeft V X (Pi.map' p q) ≫
        (eHomProductIso V X Y').hom) ≫ Pi.π _ j) =
        f (p j) ≫ eHomWhiskerLeft V X (q j) := by
      calc ((eHomProductLift V X Y f ≫
          eHomWhiskerLeft V X (Pi.map' p q) ≫
          (eHomProductIso V X Y').hom) ≫ Pi.π _ j)
          = (eHomProductLift V X Y f ≫
            eHomWhiskerLeft V X (Pi.map' p q)) ≫
            ((eHomProductIso V X Y').hom ≫ Pi.π _ j) := by
            simp only [Category.assoc]
        _ = (eHomProductLift V X Y f ≫
            eHomWhiskerLeft V X (Pi.map' p q)) ≫
            eHomWhiskerLeft V X (Pi.π Y' j) := by
            simp only [eHomProductIso_hom_π]
        _ = eHomProductLift V X Y f ≫
            (eHomWhiskerLeft V X (Pi.map' p q) ≫
              eHomWhiskerLeft V X (Pi.π Y' j)) := by
            simp only [Category.assoc]
        _ = eHomProductLift V X Y f ≫
            eHomWhiskerLeft V X (Pi.map' p q ≫ Pi.π Y' j) := by
            simp only [← eHomWhiskerLeft_comp]
        _ = eHomProductLift V X Y f ≫
            eHomWhiskerLeft V X (Pi.π Y (p j) ≫ q j) := by
            simp only [Limits.Pi.map'_comp_π]
        _ = eHomProductLift V X Y f ≫
            (eHomWhiskerLeft V X (Pi.π Y (p j)) ≫
              eHomWhiskerLeft V X (q j)) := by
            simp only [eHomWhiskerLeft_comp]
        _ = (eHomProductLift V X Y f ≫
            eHomWhiskerLeft V X (Pi.π Y (p j))) ≫
            eHomWhiskerLeft V X (q j) := by
            simp only [Category.assoc]
        _ = f (p j) ≫ eHomWhiskerLeft V X (q j) := by
            simp only [eHomProductLift_comp_eHomWhiskerLeft]
    have rhs : ((eHomProductLift V X Y'
        (fun k => f (p k) ≫ eHomWhiskerLeft V X (q k)) ≫
        (eHomProductIso V X Y').hom) ≫ Pi.π _ j) =
        f (p j) ≫ eHomWhiskerLeft V X (q j) := by
      calc ((eHomProductLift V X Y'
          (fun k => f (p k) ≫ eHomWhiskerLeft V X (q k)) ≫
          (eHomProductIso V X Y').hom) ≫ Pi.π _ j)
          = eHomProductLift V X Y'
            (fun k => f (p k) ≫ eHomWhiskerLeft V X (q k)) ≫
            ((eHomProductIso V X Y').hom ≫ Pi.π _ j) := by
            simp only [Category.assoc]
        _ = eHomProductLift V X Y'
            (fun k => f (p k) ≫ eHomWhiskerLeft V X (q k)) ≫
            eHomWhiskerLeft V X (Pi.π Y' j) := by
            simp only [eHomProductIso_hom_π]
        _ = f (p j) ≫ eHomWhiskerLeft V X (q j) := by
            simp only [eHomProductLift_comp_eHomWhiskerLeft]
    rw [lhs, rhs]
  calc eHomProductLift V X Y f ≫ eHomWhiskerLeft V X (Pi.map' p q)
      = (eHomProductLift V X Y f ≫
        eHomWhiskerLeft V X (Pi.map' p q) ≫
        (eHomProductIso V X Y').hom) ≫
        (eHomProductIso V X Y').inv := by
        simp
    _ = (eHomProductLift V X Y'
          (fun j => f (p j) ≫ eHomWhiskerLeft V X (q j)) ≫
        (eHomProductIso V X Y').hom) ≫
        (eHomProductIso V X Y').inv := by
        rw [hEq]
    _ = eHomProductLift V X Y'
        (fun j => f (p j) ≫ eHomWhiskerLeft V X (q j)) := by
        simp

/-- Componentwise naturality of enriched product lifts under simultaneous source and
target-product transport. -/
public theorem eHomProductLift_naturality
    {J : Type w'} {X X' : C} {Y : I → C} {Y' : J → C}
    [HasConicalProduct V Y] [HasConicalProduct V Y']
    {T : V} (e : I ≃ J) (g : X' ⟶ X)
    (q : ∀ i, Y i ⟶ Y' (e i))
    (k : (∏ᶜ Y) ⟶ ∏ᶜ Y')
    (hk : ∀ i, k ≫ Pi.π Y' (e i) = Pi.π Y i ≫ q i)
    (f : ∀ i, T ⟶ (X ⟶[V] Y i))
    (f' : ∀ j, T ⟶ (X' ⟶[V] Y' j))
    (hf : ∀ i, f' (e i) =
      (f i ≫ eHomWhiskerRight V g (Y i)) ≫
        eHomWhiskerLeft V X' (q i)) :
    eHomProductLift V X' Y' f' =
      (eHomProductLift V X Y f ≫ eHomWhiskerRight V g (∏ᶜ Y)) ≫
        eHomWhiskerLeft V X' k := by
  apply (cancel_mono (eHomProductIso V X' Y').hom).1
  apply Pi.hom_ext
  intro j
  obtain ⟨i, rfl⟩ := e.surjective j
  simp only [Category.assoc, eHomProductIso_hom_π,
    eHomProductLift_comp_eHomWhiskerLeft]
  rw [← eHomWhiskerLeft_comp, hk i, eHomWhiskerLeft_comp]
  rw [← eHom_whisker_exchange_assoc V g (Pi.π Y i)]
  simp only [← Category.assoc, eHomProductLift_comp_eHomWhiskerLeft]
  exact hf i

/-- The enriched lift of `eHomEquiv V (f i)` coincides with the enriched
representative of the ordinary product lift `Pi.lift f`. -/
@[reassoc]
public theorem eHomProductLift_eHomEquiv
    (X : C) (Y : I → C)
    [HasConicalProduct V Y]
    (f : ∀ i, X ⟶ Y i) :
    eHomProductLift V X Y (fun i => eHomEquiv V (f i)) =
      eHomEquiv V (Pi.lift f) := by
  let iso := eHomProductIso V X Y
  have h_eq : eHomProductLift V X Y (fun i => eHomEquiv V (f i)) ≫ iso.hom =
      eHomEquiv V (Pi.lift f) ≫ iso.hom := by
    apply Pi.hom_ext
    intro i
    have lhs : (eHomProductLift V X Y (fun i => eHomEquiv V (f i)) ≫ iso.hom) ≫
        Pi.π (fun j => (X ⟶[V] Y j)) i = eHomEquiv V (f i) := by
      calc (eHomProductLift V X Y (fun i => eHomEquiv V (f i)) ≫ iso.hom) ≫
          Pi.π (fun j => (X ⟶[V] Y j)) i
          = eHomProductLift V X Y (fun i => eHomEquiv V (f i)) ≫
              (iso.hom ≫ Pi.π (fun j => (X ⟶[V] Y j)) i) := by
            simp only [Category.assoc]
        _ = eHomProductLift V X Y (fun i => eHomEquiv V (f i)) ≫
              eHomWhiskerLeft V X (Pi.π Y i) := by
            rw [eHomProductIso_hom_π]
        _ = eHomEquiv V (f i) := by
            rw [eHomProductLift_comp_eHomWhiskerLeft]
    have rhs : (eHomEquiv V (Pi.lift f) ≫ iso.hom) ≫
        Pi.π (fun j => (X ⟶[V] Y j)) i = eHomEquiv V (f i) := by
      calc (eHomEquiv V (Pi.lift f) ≫ iso.hom) ≫
          Pi.π (fun j => (X ⟶[V] Y j)) i
          = eHomEquiv V (Pi.lift f) ≫ (iso.hom ≫ Pi.π (fun j => (X ⟶[V] Y j)) i) := by
            simp only [Category.assoc]
        _ = eHomEquiv V (Pi.lift f) ≫ eHomWhiskerLeft V X (Pi.π Y i) := by
            rw [eHomProductIso_hom_π]
        _ = eHomEquiv V (Pi.lift f ≫ Pi.π Y i) := by
            rw [eHomEquiv_comp_eHomWhiskerLeft]
        _ = eHomEquiv V (f i) := by
            rw [Limits.Pi.lift_comp_π]
    rw [lhs, rhs]
  calc eHomProductLift V X Y (fun i => eHomEquiv V (f i))
      = (eHomProductLift V X Y (fun i => eHomEquiv V (f i)) ≫ iso.hom) ≫ iso.inv := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = (eHomEquiv V (Pi.lift f) ≫ iso.hom) ≫ iso.inv := by
        rw [h_eq]
    _ = eHomEquiv V (Pi.lift f) := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

@[reassoc]
public theorem eHomProductLift_unique
    {Z : V} (X : C) (Y : I → C) [Unique I]
    [HasConicalProduct V Y]
    (f : ∀ i, Z ⟶ (X ⟶[V] Y i)) :
    eHomProductLift V X Y f =
      f default ≫ eHomWhiskerLeft V X (Limits.productUniqueIso Y).inv := by
  let iso := eHomProductIso V X Y
  apply (cancel_mono iso.hom).1
  apply Pi.hom_ext
  intro i
  have hi : i = default := Subsingleton.allEq _ _
  subst hi
  have h_left : (eHomProductLift V X Y f ≫ iso.hom) ≫
      Pi.π (fun j => (X ⟶[V] Y j)) default =
      f default := by
    calc (eHomProductLift V X Y f ≫ iso.hom) ≫
        Pi.π (fun j => (X ⟶[V] Y j)) default
        = eHomProductLift V X Y f ≫
          (iso.hom ≫ Pi.π (fun j => (X ⟶[V] Y j)) default) := by
          rw [Category.assoc]
      _ = eHomProductLift V X Y f ≫
          eHomWhiskerLeft V X (Pi.π Y default) := by
          rw [eHomProductIso_hom_π]
      _ = f default := by
          rw [eHomProductLift_comp_eHomWhiskerLeft]
  have h_right : ((f default ≫
      eHomWhiskerLeft V X (Limits.productUniqueIso Y).inv) ≫ iso.hom) ≫
      Pi.π (fun j => (X ⟶[V] Y j)) default =
      f default := by
    calc ((f default ≫
        eHomWhiskerLeft V X (Limits.productUniqueIso Y).inv) ≫ iso.hom) ≫
        Pi.π (fun j => (X ⟶[V] Y j)) default
        = f default ≫
          (eHomWhiskerLeft V X (Limits.productUniqueIso Y).inv ≫
            (iso.hom ≫ Pi.π (fun j => (X ⟶[V] Y j)) default)) := by
          simp only [Category.assoc]
      _ = f default ≫
          (eHomWhiskerLeft V X (Limits.productUniqueIso Y).inv ≫
            eHomWhiskerLeft V X (Pi.π Y default)) := by
          rw [eHomProductIso_hom_π]
      _ = f default ≫
          eHomWhiskerLeft V X
            ((Limits.productUniqueIso Y).inv ≫ Pi.π Y default) := by
          rw [← eHomWhiskerLeft_comp]
      _ = f default ≫
          eHomWhiskerLeft V X (𝟙 (Y default)) := by
          have hpi : (Limits.productUniqueIso Y).inv ≫ Pi.π Y default =
              𝟙 (Y default) := by
            simp
          rw [hpi]
      _ = f default ≫ 𝟙 _ := by
          rw [eHomWhiskerLeft_id]
      _ = f default := by
          simp
  exact h_left.trans h_right.symm

/-- Coherence between a flat enriched hom lift and iterated lifts.
The lifted map into a flat product over `Σ i, K i` followed by whiskering
the canonical comparison `chosenPiPiHom` equals the iterated product lift
of inner lifts. This is the operad-free coherence needed for enriched
endomorphism-operad associativity. -/
public theorem eHomProductLift_sigma
    {K : I → Type w'} {X : C} {Y : ∀ i, K i → C} {Z : V}
    (f : ∀ i j, Z ⟶ (X ⟶[V] Y i j))
    [∀ i, HasConicalProduct V (Y i)]
    [HasConicalProduct V (fun i => ∏ᶜ Y i)]
    [HasConicalProduct V (fun p : (Σ i, K i) => Y p.1 p.2)] :
    eHomProductLift V X (fun p : (Σ i, K i) => Y p.1 p.2)
        (fun p => f p.1 p.2) ≫
        eHomWhiskerLeft V X (Limits.chosenPiPiHom (X := Y)) =
      eHomProductLift V X (fun i => ∏ᶜ Y i)
        (fun i => eHomProductLift V X (Y i) (f i)) := by
  let isoOuter := eHomProductIso V X (fun i => ∏ᶜ Y i)
  apply (cancel_mono isoOuter.hom).1
  apply Pi.hom_ext
  intro i
  have hR : (eHomProductLift V X (fun i => ∏ᶜ Y i)
        (fun j => eHomProductLift V X (Y j) (f j)) ≫
        isoOuter.hom) ≫
        Pi.π (fun i => (X ⟶[V] ∏ᶜ Y i)) i =
      eHomProductLift V X (Y i) (f i) := by
    calc (eHomProductLift V X (fun i => ∏ᶜ Y i)
          (fun j => eHomProductLift V X (Y j) (f j)) ≫
          isoOuter.hom) ≫
          Pi.π (fun i => (X ⟶[V] ∏ᶜ Y i)) i
        = eHomProductLift V X (fun i => ∏ᶜ Y i)
            (fun j => eHomProductLift V X (Y j) (f j)) ≫
            (isoOuter.hom ≫
              Pi.π (fun i => (X ⟶[V] ∏ᶜ Y i)) i) := by
          rw [Category.assoc]
      _ = eHomProductLift V X (fun i => ∏ᶜ Y i)
            (fun j => eHomProductLift V X (Y j) (f j)) ≫
            eHomWhiskerLeft V X
              (Pi.π (fun i => ∏ᶜ Y i) i) := by
          rw [eHomProductIso_hom_π]
      _ = eHomProductLift V X (Y i) (f i) := by
          rw [eHomProductLift_comp_eHomWhiskerLeft]
  have hL : ((eHomProductLift V X
        (fun p : (Σ i, K i) => Y p.1 p.2)
        (fun p => f p.1 p.2) ≫
        eHomWhiskerLeft V X
          (Limits.chosenPiPiHom (X := Y))) ≫
        isoOuter.hom) ≫
        Pi.π (fun i => (X ⟶[V] ∏ᶜ Y i)) i =
      eHomProductLift V X
        (fun p : (Σ i, K i) => Y p.1 p.2)
        (fun p => f p.1 p.2) ≫
        eHomWhiskerLeft V X
          (Pi.lift (fun j =>
            Pi.π (fun p : (Σ i, K i) => Y p.1 p.2)
              ⟨i, j⟩)) := by
    calc ((eHomProductLift V X
          (fun p : (Σ i, K i) => Y p.1 p.2)
          (fun p => f p.1 p.2) ≫
          eHomWhiskerLeft V X
            (Limits.chosenPiPiHom (X := Y))) ≫
          isoOuter.hom) ≫
          Pi.π (fun i => (X ⟶[V] ∏ᶜ Y i)) i
        = (eHomProductLift V X
            (fun p : (Σ i, K i) => Y p.1 p.2)
            (fun p => f p.1 p.2) ≫
            eHomWhiskerLeft V X
              (Limits.chosenPiPiHom (X := Y))) ≫
            (isoOuter.hom ≫
              Pi.π (fun i => (X ⟶[V] ∏ᶜ Y i)) i) := by
          rw [Category.assoc]
      _ = (eHomProductLift V X
            (fun p : (Σ i, K i) => Y p.1 p.2)
            (fun p => f p.1 p.2) ≫
            eHomWhiskerLeft V X
              (Limits.chosenPiPiHom (X := Y))) ≫
            eHomWhiskerLeft V X
              (Pi.π (fun i => ∏ᶜ Y i) i) := by
          rw [eHomProductIso_hom_π]
      _ = eHomProductLift V X
            (fun p : (Σ i, K i) => Y p.1 p.2)
            (fun p => f p.1 p.2) ≫
            (eHomWhiskerLeft V X
                (Limits.chosenPiPiHom (X := Y)) ≫
              eHomWhiskerLeft V X
                (Pi.π (fun i => ∏ᶜ Y i) i)) := by
          rw [Category.assoc]
      _ = eHomProductLift V X
            (fun p : (Σ i, K i) => Y p.1 p.2)
            (fun p => f p.1 p.2) ≫
            eHomWhiskerLeft V X
              (Limits.chosenPiPiHom (X := Y) ≫
                Pi.π (fun i => ∏ᶜ Y i) i) := by
          rw [← eHomWhiskerLeft_comp]
      _ = eHomProductLift V X
            (fun p : (Σ i, K i) => Y p.1 p.2)
            (fun p => f p.1 p.2) ≫
            eHomWhiskerLeft V X
              (Pi.lift (fun j =>
                Pi.π (fun p : (Σ i, K i) => Y p.1 p.2)
                  ⟨i, j⟩)) := by
          rw [Limits.chosenPiPiHom_π]
  rw [hL, hR]
  let isoInner := eHomProductIso V X (Y i)
  apply (cancel_mono isoInner.hom).1
  apply Pi.hom_ext
  intro j
  have hInnerR : (eHomProductLift V X (Y i) (f i) ≫
        isoInner.hom) ≫
        Pi.π (fun j => (X ⟶[V] Y i j)) j = f i j := by
    calc (eHomProductLift V X (Y i) (f i) ≫
          isoInner.hom) ≫
          Pi.π (fun j => (X ⟶[V] Y i j)) j
        = eHomProductLift V X (Y i) (f i) ≫
            (isoInner.hom ≫
              Pi.π (fun j => (X ⟶[V] Y i j)) j) := by
          rw [Category.assoc]
      _ = eHomProductLift V X (Y i) (f i) ≫
            eHomWhiskerLeft V X (Pi.π (Y i) j) := by
          rw [eHomProductIso_hom_π]
      _ = f i j := by
          rw [eHomProductLift_comp_eHomWhiskerLeft]
  have hInnerL : ((eHomProductLift V X
        (fun p : (Σ i, K i) => Y p.1 p.2)
        (fun p => f p.1 p.2) ≫
        eHomWhiskerLeft V X
          (Pi.lift (fun j =>
            Pi.π (fun p : (Σ i, K i) => Y p.1 p.2)
              ⟨i, j⟩))) ≫
        isoInner.hom) ≫
        Pi.π (fun j => (X ⟶[V] Y i j)) j = f i j := by
    calc ((eHomProductLift V X
          (fun p : (Σ i, K i) => Y p.1 p.2)
          (fun p => f p.1 p.2) ≫
          eHomWhiskerLeft V X
            (Pi.lift (fun j =>
              Pi.π (fun p : (Σ i, K i) => Y p.1 p.2)
                ⟨i, j⟩))) ≫
          isoInner.hom) ≫
          Pi.π (fun j => (X ⟶[V] Y i j)) j
        = (eHomProductLift V X
            (fun p : (Σ i, K i) => Y p.1 p.2)
            (fun p => f p.1 p.2) ≫
            eHomWhiskerLeft V X
              (Pi.lift (fun j =>
                Pi.π (fun p : (Σ i, K i) => Y p.1 p.2)
                  ⟨i, j⟩))) ≫
            (isoInner.hom ≫
              Pi.π (fun j => (X ⟶[V] Y i j)) j) := by
          rw [Category.assoc]
      _ = (eHomProductLift V X
            (fun p : (Σ i, K i) => Y p.1 p.2)
            (fun p => f p.1 p.2) ≫
            eHomWhiskerLeft V X
              (Pi.lift (fun j =>
                Pi.π (fun p : (Σ i, K i) => Y p.1 p.2)
                  ⟨i, j⟩))) ≫
            eHomWhiskerLeft V X (Pi.π (Y i) j) := by
          rw [eHomProductIso_hom_π]
      _ = eHomProductLift V X
            (fun p : (Σ i, K i) => Y p.1 p.2)
            (fun p => f p.1 p.2) ≫
            (eHomWhiskerLeft V X
                (Pi.lift (fun j =>
                  Pi.π (fun p : (Σ i, K i) => Y p.1 p.2)
                    ⟨i, j⟩)) ≫
              eHomWhiskerLeft V X (Pi.π (Y i) j)) := by
          rw [Category.assoc]
      _ = eHomProductLift V X
            (fun p : (Σ i, K i) => Y p.1 p.2)
            (fun p => f p.1 p.2) ≫
            eHomWhiskerLeft V X
              (Pi.lift (fun j =>
                  Pi.π (fun p : (Σ i, K i) => Y p.1 p.2)
                    ⟨i, j⟩) ≫
                Pi.π (Y i) j) := by
          rw [← eHomWhiskerLeft_comp]
      _ = eHomProductLift V X
            (fun p : (Σ i, K i) => Y p.1 p.2)
            (fun p => f p.1 p.2) ≫
            eHomWhiskerLeft V X
              (Pi.π (fun p : (Σ i, K i) => Y p.1 p.2)
                ⟨i, j⟩) := by
          rw [Pi.lift_comp_π]
      _ = f i j := by
          rw [eHomProductLift_comp_eHomWhiskerLeft]
  rw [hInnerL, hInnerR]

end CategoryTheory.Enriched

namespace CategoryTheory.Enriched

open CategoryTheory Limits MonoidalCategory

universe uJ uV vV uC vC

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
variable {C : Type uC} [Category.{vC} C] [EnrichedOrdinaryCategory V C]

/-- The Hom iso of an exhibited conical product reflects maps at every enriching weight. -/
public theorem eHomProduct_hom_ext {J : Type uJ} {W : V} (B : C) (E : J → C)
    [HasConicalProduct V E]
    (r s : W ⟶ (B ⟶[V] ∏ᶜ E))
    (h : ∀ j, r ≫ eHomWhiskerLeft V B (Pi.π E j) =
      s ≫ eHomWhiskerLeft V B (Pi.π E j)) : r = s := by
  let σ := Enriched.eHomProductIso V B E
  apply (cancel_mono σ.hom).1
  apply Pi.hom_ext
  intro j
  have hπ : σ.hom ≫ Pi.π (fun i => (B ⟶[V] E i)) j =
      eHomWhiskerLeft V B (Pi.π E j) := Enriched.eHomProductIso_hom_π V B E j
  exact (Category.assoc _ _ _).trans
    ((congrArg (r ≫ ·) hπ).trans
      ((h j).trans ((Category.assoc _ _ _).trans (congrArg (s ≫ ·) hπ)).symm))

end CategoryTheory.Enriched
