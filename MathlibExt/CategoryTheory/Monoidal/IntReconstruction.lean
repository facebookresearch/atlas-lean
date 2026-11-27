/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Monoidal.IntCompact

/-!
# Reconstructing Int morphisms by duality

The elementary duality pairings bend the negative wires of an embedded crossed
map to recover its Int morphism. This is the morphism formula in the proof of
Joyal, Street and Verity, Traced monoidal categories (1996), Proposition 5.2,
https://doi.org/10.1017/S0305004100074338, in the symmetric specialization.
-/

@[expose] public section
universe v u
namespace CategoryTheory
open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
open scoped MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
namespace IntConstruction
variable (T : SymmetricTrace C)
private abbrev pos (A : C) : IntConstruction T := ⟨A, 𝟙_ C⟩
private abbrev neg (A : C) : IntConstruction T := ⟨𝟙_ C, A⟩
private def cup (A : C) : 𝟙_ (IntConstruction T) ⟶ pos T A ⊗ neg T A :=
  (positivePairing T A).coevaluation'

private theorem cup_left (X : IntConstruction T) (A : C) :
    hom T (X ◁ cup T A) =
      𝟙 ((X.positive ⊗ 𝟙_ C) ⊗ ((A ⊗ 𝟙_ C) ⊗ X.negative)) ⊗≫
        𝟙 (X.positive ⊗ (A ⊗ X.negative)) ⊗≫
          𝟙 ((X.positive ⊗ (A ⊗ 𝟙_ C)) ⊗ (𝟙_ C ⊗ X.negative)) := by
  change (tensorShuffle X.positive (𝟙_ C) X.negative (A ⊗ 𝟙_ C)).hom ≫
    (𝟙 _ ⊗ₘ ((λ_ (A ⊗ 𝟙_ C)).hom ≫ (ρ_ (A ⊗ 𝟙_ C)).inv)) ≫
    (tensorShuffle X.positive (A ⊗ 𝟙_ C) X.negative (𝟙_ C)).inv = _
  simp only [tensorShuffle, Iso.trans_hom, Iso.trans_inv, whiskerLeftIso_hom,
    whiskerLeftIso_inv, tensorμ, tensorδ, braiding_tensorUnit_left,
    braiding_tensorUnit_right,
    BraidedCategory.braiding_tensor_left_hom, BraidedCategory.braiding_tensor_right_hom,
    ← SymmetricCategory.braiding_swap_eq_inv_braiding]
  calc
    _ = 𝟙 ((X.positive ⊗ 𝟙_ C) ⊗ ((A ⊗ 𝟙_ C) ⊗ X.negative)) ⊗≫
        X.positive ◁ ((β_ A X.negative).hom ≫ (β_ X.negative A).hom) ⊗≫
          𝟙 ((X.positive ⊗ (A ⊗ 𝟙_ C)) ⊗ (𝟙_ C ⊗ X.negative)) := by monoidal
    _ = _ := by rw [SymmetricCategory.symmetry]; simp only [whiskerLeft_id]

private def mateStart (X : IntConstruction T) (A : C) :
    X ⟶ (X ⊗ pos T A) ⊗ neg T A :=
  (ρ_ X).inv ≫ X ◁ cup T A ≫ (α_ X (pos T A) (neg T A)).inv

private theorem hom_mateStart (X : IntConstruction T) (A : C) :
    hom T (mateStart T X A) =
      𝟙 (X.positive ⊗ (A ⊗ (𝟙_ C ⊗ X.negative))) ⊗≫
        𝟙 ((X.positive ⊗ A) ⊗ X.negative) ⊗≫
          𝟙 (((X.positive ⊗ A) ⊗ 𝟙_ C) ⊗ X.negative) := by
  unfold mateStart
  rw [hom_comp, hom_comp, cup_left]
  change compose T ((ρ_ X.positive).inv ⊗ₘ (λ_ X.negative).hom)
    (compose T _ ((α_ X.positive A (𝟙_ C)).inv ⊗ₘ (α_ A (𝟙_ C) X.negative).inv)) = _
  rw [compose_tensor_left, compose_tensor_right]
  monoidal

/-- Bend an embedded positive input into a formal negative output using the elementary pairing. -/
def rightMate {X Y : IntConstruction T} (A : C)
    (f : X ⊗ (embedding T).obj A ⟶ Y) : X ⟶ Y ⊗ (⟨𝟙_ C, A⟩ : IntConstruction T) := by
  letI := positivePairing T A
  exact tensorRightHomEquiv X (⟨A, 𝟙_ C⟩ : IntConstruction T)
    (⟨𝟙_ C, A⟩ : IntConstruction T) Y f

set_option backward.defeqAttrib.useBackward true in
private theorem hom_rightMate_positive (P A : C) {Y : IntConstruction T}
    (f : pos T P ⊗ pos T A ⟶ Y) :
    hom T (rightMate T A f) = (α_ P A Y.negative).inv ≫ hom T f ≫
      (α_ Y.positive (𝟙_ C) (𝟙_ C)).inv := by
  have h : rightMate T A f = mateStart T (pos T P) A ≫ f ▷ neg T A := by
    change (ρ_ (pos T P)).inv ≫ pos T P ◁ cup T A ≫
      (α_ (pos T P) (pos T A) (neg T A)).inv ≫ f ▷ neg T A = _
    simp only [mateStart, Category.assoc]
  rw [h, hom_comp, hom_mateStart]
  change compose T _ ((tensorShuffle (P ⊗ A) (𝟙_ C) Y.negative A).hom ≫
    (hom T f ⊗ₘ 𝟙 _) ≫ (tensorShuffle Y.positive (𝟙_ C) (𝟙_ C ⊗ 𝟙_ C) A).inv) = _
  simp only [compose, tensorShuffle, Iso.trans_hom, Iso.trans_inv,
    whiskerLeftIso_hom, whiskerLeftIso_inv, tensorμ, tensorδ, exchange,
    T.vanishing_tensor, T.vanishing_unit,
    ← SymmetricCategory.braiding_swap_eq_inv_braiding,
    braiding_tensorUnit_left, braiding_tensorUnit_right,
    BraidedCategory.braiding_tensor_left_hom, BraidedCategory.braiding_tensor_right_hom,
    tensorHom_id]
  let l := (α_ P A Y.negative).inv
  let r := hom T f ≫ (α_ Y.positive (𝟙_ C) (𝟙_ C)).inv
  let k := exchange (P ⊗ A) Y.negative A ≫ exchange P A A ▷ Y.negative ≫
    exchange (P ⊗ A) A Y.negative
  have hk : T.trace k = 𝟙 ((P ⊗ A) ⊗ Y.negative) := by
    rw [show k = exchange (P ⊗ A) Y.negative A ≫ exchange P A A ▷ Y.negative ≫
      exchange (P ⊗ A) A Y.negative from rfl, trace_whiskerRight]
    have hx : T.trace (exchange P A A) = 𝟙 (P ⊗ A) := by
      simpa [exchange, T.yanking] using T.superposing (β_ A A).hom (𝟙 P)
    simp only [hx, id_whiskerRight]
  calc
    _ = T.trace (l ▷ A ≫ k ≫ r ▷ A) := by
      apply congrArg T.trace
      dsimp only [l, r, k]
      simp only [exchange]
      monoidal
    _ = _ := by
      rw [show T.trace (l ▷ A ≫ k ≫ r ▷ A) = l ≫ T.trace k ≫ r by
        simpa only [tensorHom_id] using T.naturality k l r]
      simp only [hk, Category.id_comp, l, r]

private theorem cup_right (A P : C) :
    hom T (cup T A ▷ pos T P) =
      𝟙 ((𝟙_ C ⊗ P) ⊗ (𝟙_ C ⊗ (A ⊗ 𝟙_ C))) ⊗≫
        (β_ P A).hom ⊗≫ 𝟙 (((A ⊗ 𝟙_ C) ⊗ P) ⊗ (𝟙_ C ⊗ 𝟙_ C)) := by
  change (tensorShuffle (𝟙_ C) P (A ⊗ 𝟙_ C) (𝟙_ C)).hom ≫
    (((λ_ (A ⊗ 𝟙_ C)).hom ≫ (ρ_ (A ⊗ 𝟙_ C)).inv) ⊗ₘ 𝟙 _) ≫
    (tensorShuffle (A ⊗ 𝟙_ C) P (𝟙_ C) (𝟙_ C)).inv = _
  simp only [tensorShuffle, Iso.trans_hom, Iso.trans_inv, whiskerLeftIso_hom,
    whiskerLeftIso_inv, tensorμ, tensorδ,
    BraidedCategory.braiding_tensor_right_hom, braiding_tensorUnit_left,
    braiding_tensorUnit_right, braiding_inv_tensorUnit_right]
  monoidal

private def leftMateStart (P A : C) : pos T P ⟶ pos T A ⊗ (neg T A ⊗ pos T P) :=
  (λ_ (pos T P)).inv ≫ cup T A ▷ pos T P ≫ (α_ (pos T A) (neg T A) (pos T P)).hom

private theorem hom_leftMateStart (P A : C) :
    hom T (leftMateStart T P A) =
      𝟙 (P ⊗ ((𝟙_ C ⊗ A) ⊗ 𝟙_ C)) ⊗≫ (β_ P A).hom ⊗≫
        𝟙 ((A ⊗ (𝟙_ C ⊗ P)) ⊗ 𝟙_ C) := by
  unfold leftMateStart
  rw [hom_comp, hom_comp, cup_right]
  change compose T ((λ_ P).inv ⊗ₘ (ρ_ (𝟙_ C)).hom)
    (compose T _ ((α_ A (𝟙_ C) P).hom ⊗ₘ (α_ (𝟙_ C) A (𝟙_ C)).hom)) = _
  rw [compose_tensor_left, compose_tensor_right]
  monoidal

private def leftMate (P A : C) {Y : IntConstruction T}
    (f : neg T A ⊗ pos T P ⟶ Y) : pos T P ⟶ pos T A ⊗ Y :=
  leftMateStart T P A ≫ pos T A ◁ f

private theorem hom_leftMate (P A : C) {Y : IntConstruction T}
    (f : neg T A ⊗ pos T P ⟶ Y) :
    hom T (leftMate T P A f) =
      (α_ P Y.negative (𝟙_ C)).inv ≫ (ρ_ (P ⊗ Y.negative)).hom ≫
        (λ_ P).inv ▷ Y.negative ≫ hom T f ≫ Y.positive ◁ (λ_ A).hom ≫
          (β_ Y.positive A).hom ≫ (ρ_ (A ⊗ Y.positive)).inv := by
  unfold leftMate
  rw [hom_comp, hom_leftMateStart]
  change compose T _ ((tensorShuffle A (𝟙_ C ⊗ P) (𝟙_ C) Y.negative).hom ≫
    (𝟙 _ ⊗ₘ hom T f) ≫ (tensorShuffle A Y.positive (𝟙_ C) (𝟙_ C ⊗ A)).inv) = _
  simp only [compose, tensorShuffle, Iso.trans_hom, Iso.trans_inv,
    whiskerLeftIso_hom, whiskerLeftIso_inv, tensorμ, tensorδ, exchange,
    T.vanishing_tensor, T.vanishing_unit,
    ← SymmetricCategory.braiding_swap_eq_inv_braiding,
    braiding_tensorUnit_left, braiding_tensorUnit_right,
    BraidedCategory.braiding_tensor_left_hom, BraidedCategory.braiding_tensor_right_hom,
    id_tensorHom]
  let L := P ⊗ (Y.negative ⊗ 𝟙_ C)
  let R := (A ⊗ Y.positive) ⊗ 𝟙_ C
  let l : L ⊗ (𝟙_ C) ⟶ (𝟙_ C ⊗ P) ⊗ Y.negative := 𝟙 _ ⊗≫ 𝟙 _
  let r₀ : A ⊗ (Y.positive ⊗ (𝟙_ C ⊗ A)) ⟶ (R ⊗ (𝟙_ C)) ⊗ A := 𝟙 _ ⊗≫ 𝟙 _
  let r : Y.positive ⊗ A ⟶ R ⊗ (𝟙_ C) := (β_ Y.positive A).hom ⊗≫ 𝟙 _
  let k := l ≫ hom T f ≫ Y.positive ◁ (λ_ A).hom
  have hx : T.trace (exchange Y.positive A A) = 𝟙 (Y.positive ⊗ A) := by
    simpa [exchange, T.yanking] using T.superposing (β_ A A).hom (𝟙 Y.positive)
  calc
    _ = (ρ_ L).inv ≫ T.trace (l ▷ A ≫ (β_ ((𝟙_ C ⊗ P) ⊗ Y.negative) A).hom ≫
      A ◁ hom T f ≫ r₀) ≫ (ρ_ R).hom := by
      congr 2
      apply congrArg T.trace
      dsimp only [l, r₀, L, R]
      simp only [BraidedCategory.braiding_tensor_left_hom, braiding_tensorUnit_left]
      monoidal
    _ = (ρ_ L).inv ≫ T.trace (k ▷ A ≫ exchange Y.positive A A ≫ r ▷ A) ≫ (ρ_ R).hom := by
      congr 2
      apply congrArg T.trace
      rw [← BraidedCategory.braiding_naturality_left_assoc]
      dsimp only [l, r₀, r, k, L, R, neg, pos, tensorObj]
      simp only [exchange, BraidedCategory.braiding_tensor_left_hom,
        braiding_tensorUnit_left]
      monoidal
    _ = _ := by
      rw [show T.trace (k ▷ A ≫ exchange Y.positive A A ≫ r ▷ A) =
        k ≫ T.trace (exchange Y.positive A A) ≫ r by
          simpa only [tensorHom_id] using T.naturality (exchange Y.positive A A) k r]
      rw [hx]
      dsimp only [l, r, k, L, R]
      monoidal

private def embeddedCross {P V B U : C} (f : P ⊗ V ⟶ B ⊗ U) :
    pos T P ⊗ pos T V ⟶ pos T B ⊗ pos T U :=
  μ (embedding T) P V ≫ (embedding T).map f ≫ δ (embedding T) B U

private theorem hom_embeddedCross {P V B U : C} (f : P ⊗ V ⟶ B ⊗ U) :
    hom T (embeddedCross T f) = f ⊗ₘ 𝟙 ((𝟙_ C) ⊗ (𝟙_ C)) := by
  unfold embeddedCross
  rw [embedding_map_eq_mapPair]
  change hom T (
    (mapPair T (𝟙 _) (λ_ (𝟙_ C)).inv : pos T P ⊗ pos T V ⟶ pos T (P ⊗ V)) ≫
    (mapPair T f (𝟙 _) : pos T (P ⊗ V) ⟶ pos T (B ⊗ U)) ≫
    (mapPair T (𝟙 _) (λ_ (𝟙_ C)).hom : pos T (B ⊗ U) ⟶ pos T B ⊗ pos T U)) = _
  simp only [mapPair_comp, Category.id_comp, Category.comp_id, Iso.hom_inv_id]
  rfl

private def swappedDecomposition (X : IntConstruction T) :
    X ≅ neg T X.negative ⊗ pos T X.positive :=
  decomposition T X ≪≫ β_ _ _

private def bendCross {X Y : IntConstruction T}
    (f : X.positive ⊗ Y.negative ⟶ Y.positive ⊗ X.negative) :
    pos T X.positive ⟶ pos T X.negative ⊗ (pos T Y.positive ⊗ neg T Y.negative) :=
  rightMate T Y.negative (embeddedCross T f) ≫
    (β_ (pos T Y.positive) (pos T X.negative)).hom ▷ neg T Y.negative ≫
      (α_ (pos T X.negative) (pos T Y.positive) (neg T Y.negative)).hom

private theorem bendCross_eq {X Y : IntConstruction T} (f : X ⟶ Y) :
    bendCross T (hom T f) = leftMate T X.positive X.negative
      ((swappedDecomposition T X).inv ≫ f ≫ (decomposition T Y).hom) := by
  apply hom_ext T
  unfold bendCross
  rw [hom_comp, hom_rightMate_positive, hom_embeddedCross, hom_leftMate]
  simp only [hom_comp]
  have hw : hom T ((β_ (pos T Y.positive) (pos T X.negative)).hom ▷ neg T Y.negative) =
      ((β_ Y.positive X.negative).hom ⊗ₘ 𝟙 (𝟙_ C)) ⊗ₘ
        (𝟙 Y.negative ⊗ₘ (β_ (𝟙_ C) (𝟙_ C)).hom) := by
    change hom T (tensorMap T
      (mapPair T (β_ Y.positive X.negative).hom (β_ (𝟙_ C) (𝟙_ C)).hom :
        pos T Y.positive ⊗ pos T X.negative ⟶ pos T X.negative ⊗ pos T Y.positive)
      (𝟙 (neg T Y.negative))) = _
    rw [← mapPair_id T (neg T Y.negative), tensorMap_mapPair]
    rfl
  rw [hw]
  change compose T _ (compose T _
    ((α_ X.negative Y.positive (𝟙_ C)).hom ⊗ₘ
      (α_ Y.negative (𝟙_ C) (𝟙_ C)).hom)) = _
  have hc {A B D U V W : C} (a : A ⟶ B) (b : V ⟶ U) (c : B ⟶ D) (d : W ⟶ V) :
      compose T (a ⊗ₘ b) (c ⊗ₘ d) = (a ≫ c) ⊗ₘ (d ≫ b) := by
    exact congrArg (hom T) (mapPair_comp T (X := ⟨A,U⟩) (Y := ⟨B,V⟩) (Z := ⟨D,W⟩) a b c d)
  rw [hc, compose_tensor_right]
  have hd : hom T (swappedDecomposition T X).inv =
      ((β_ (𝟙_ C) X.positive).hom ≫ (ρ_ X.positive).hom) ⊗ₘ
        ((ρ_ X.negative).inv ≫ (β_ X.negative (𝟙_ C)).hom) := by
    change hom T ((mapPair T (β_ X.positive (𝟙_ C)).inv
      (β_ (𝟙_ C) X.negative).inv : neg T X.negative ⊗ pos T X.positive ⟶
        pos T X.positive ⊗ neg T X.negative) ≫
      (decomposition T X).inv) = _
    change hom T ((mapPair T _ _ : neg T X.negative ⊗ pos T X.positive ⟶
      pos T X.positive ⊗ neg T X.negative) ≫
      (mapPair T (ρ_ X.positive).hom (ρ_ X.negative).inv :
        pos T X.positive ⊗ neg T X.negative ⟶ X)) = _
    rw [mapPair_comp]
    simp only [hom_mapPair, ← SymmetricCategory.braiding_swap_eq_inv_braiding]
  rw [hd]
  change _ = _ ≫ _ ≫ _ ≫ compose T _ (compose T (hom T f)
    ((ρ_ Y.positive).inv ⊗ₘ (ρ_ Y.negative).hom)) ≫ _
  rw [compose_tensor_left, compose_tensor_right]
  dsimp only [pos, neg, tensorObj]
  simp only [braiding_tensorUnit_left, braiding_tensorUnit_right,
    BraidedCategory.braiding_tensor_left_hom, tensorHom_id]
  monoidal

/-- Recover an Int morphism by embedding its crossed map and bending both negative wires.

The right bend uses coevaluation; the inverse left bend uses evaluation. The
component decompositions and symmetry put the inputs and outputs in their original order. -/
def reconstruct {X Y : IntConstruction T}
    (f : X.positive ⊗ Y.negative ⟶ Y.positive ⊗ X.negative) : X ⟶ Y := by
  let p (A : C) : IntConstruction T := ⟨A, 𝟙_ C⟩
  let n (A : C) : IntConstruction T := ⟨𝟙_ C, A⟩
  letI := positivePairing T X.negative
  let g : p X.positive ⊗ p Y.negative ⟶ p Y.positive ⊗ p X.negative :=
    μ (embedding T) _ _ ≫ (embedding T).map f ≫ δ (embedding T) _ _
  let h := rightMate T Y.negative g ≫
    (β_ (p Y.positive) (p X.negative)).hom ▷ n Y.negative ≫
      (α_ (p X.negative) (p Y.positive) (n Y.negative)).hom
  exact (decomposition T X).hom ≫ (β_ (p X.positive) (n X.negative)).hom ≫
    (tensorLeftHomEquiv (p X.positive) (p X.negative) (n X.negative)
      (p Y.positive ⊗ n Y.negative)).symm h ≫ (decomposition T Y).inv

/-- The duality construction recovers every Int morphism, for any supplied trace. -/
@[simp] theorem reconstruct_hom {X Y : IntConstruction T} (f : X ⟶ Y) :
    reconstruct T (hom T f) = f := by
  let _ : ExactPairing (pos T X.negative) (neg T X.negative) := positivePairing T X.negative
  have he (g : neg T X.negative ⊗ pos T X.positive ⟶ pos T Y.positive ⊗ neg T Y.negative) :
      leftMate T X.positive X.negative g =
        tensorLeftHomEquiv (pos T X.positive) (pos T X.negative) (neg T X.negative)
          (pos T Y.positive ⊗ neg T Y.negative) g := by
    change (_ ≫ _ ≫ _) ≫ _ = _ ≫ _ ≫ _ ≫ _
    simp only [Category.assoc]
    rfl
  have h : (swappedDecomposition T X).hom ≫
      (tensorLeftHomEquiv (pos T X.positive) (pos T X.negative) (neg T X.negative)
        (pos T Y.positive ⊗ neg T Y.negative)).symm (bendCross T (hom T f)) ≫
          (decomposition T Y).inv = f := by
    rw [bendCross_eq, he, Equiv.symm_apply_apply]
    simp
  simpa only [reconstruct, swappedDecomposition, Iso.trans_hom, bendCross,
    embeddedCross, Category.assoc] using h

/-- The crossed map of the reconstruction is the map supplied to it. -/
@[simp] theorem hom_reconstruct {X Y : IntConstruction T}
    (f : X.positive ⊗ Y.negative ⟶ Y.positive ⊗ X.negative) :
    hom T (reconstruct T (X := X) (Y := Y) f) = f := by
  exact congrArg (hom T) (reconstruct_hom T (ofHom T f))

end IntConstruction
end CategoryTheory
