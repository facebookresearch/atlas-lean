/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Monoidal.IntMonoidal
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Compact closure of the Int construction

Source: Joyal, Street and Verity, Traced monoidal categories (1996),
Proposition 5.1, https://doi.org/10.1017/S0305004100074338,
specialized to symmetric monoidal categories. Swapping the components gives
both duals; the resulting canonical trace agrees with the supplied source trace
under the fully faithful strong symmetric monoidal embedding. No rigidity of the
source is assumed.

The basic positive/negative pairing is proved directly from trace axioms.
General pairings reuse Mathlib's tensor, swapped, and transported pairings.
Named pairings avoid installing overlapping global `ExactPairing` instances.
-/

@[expose] public section
universe v u
namespace CategoryTheory
open MonoidalCategory
open scoped MonoidalCategory
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
namespace IntConstruction
variable (T : SymmetricTrace C)

/-- Swap the positive and negative objects. -/
abbrev dual (X : IntConstruction T) : IntConstruction T := ⟨X.negative, X.positive⟩

private abbrev pos (A : C) : IntConstruction T := ⟨A, 𝟙_ C⟩
private abbrev neg (A : C) : IntConstruction T := ⟨𝟙_ C, A⟩

private def cup (A : C) : 𝟙_ (IntConstruction T) ⟶ pos T A ⊗ neg T A :=
  ofHom T ((λ_ (A ⊗ 𝟙_ C)).hom ≫ (ρ_ (A ⊗ 𝟙_ C)).inv)

private def cap (A : C) : neg T A ⊗ pos T A ⟶ 𝟙_ (IntConstruction T) :=
  ofHom T ((ρ_ (𝟙_ C ⊗ A)).hom ≫ (λ_ (𝟙_ C ⊗ A)).inv)

private theorem cup_right (A B : C) :
    hom T (cup T A ▷ pos T B) =
      𝟙 ((𝟙_ C ⊗ B) ⊗ (𝟙_ C ⊗ (A ⊗ 𝟙_ C))) ⊗≫
        (β_ B A).hom ⊗≫ 𝟙 (((A ⊗ 𝟙_ C) ⊗ B) ⊗ (𝟙_ C ⊗ 𝟙_ C)) := by
  change (tensorShuffle (𝟙_ C) B (A ⊗ 𝟙_ C) (𝟙_ C)).hom ≫
    (((λ_ (A ⊗ 𝟙_ C)).hom ≫ (ρ_ (A ⊗ 𝟙_ C)).inv) ⊗ₘ 𝟙 _) ≫
    (tensorShuffle (A ⊗ 𝟙_ C) B (𝟙_ C) (𝟙_ C)).inv = _
  simp only [tensorShuffle, Iso.trans_hom, Iso.trans_inv, whiskerLeftIso_hom,
    whiskerLeftIso_inv, tensorμ, tensorδ,
    BraidedCategory.braiding_tensor_right_hom, braiding_tensorUnit_left,
    braiding_tensorUnit_right, braiding_inv_tensorUnit_right]
  monoidal

private theorem cap_left (A B : C) :
    hom T (pos T B ◁ cap T A) =
      𝟙 ((B ⊗ (𝟙_ C ⊗ A)) ⊗ (𝟙_ C ⊗ 𝟙_ C)) ⊗≫
        𝟙 (B ⊗ A) ⊗≫ 𝟙 ((B ⊗ 𝟙_ C) ⊗ ((𝟙_ C ⊗ A) ⊗ 𝟙_ C)) := by
  change (tensorShuffle B (𝟙_ C ⊗ A) (𝟙_ C) (𝟙_ C)).hom ≫
    (𝟙 _ ⊗ₘ ((ρ_ (𝟙_ C ⊗ A)).hom ≫ (λ_ (𝟙_ C ⊗ A)).inv)) ≫
    (tensorShuffle B (𝟙_ C) (𝟙_ C) (𝟙_ C ⊗ A)).inv = _
  simp only [tensorShuffle, Iso.trans_hom, Iso.trans_inv, whiskerLeftIso_hom,
    whiskerLeftIso_inv, tensorμ, tensorδ,
    braiding_tensorUnit_right, braiding_inv_tensorUnit_right]
  monoidal

private theorem snake_pos (A : C) :
    cup T A ▷ pos T A ≫ (α_ (pos T A) (neg T A) (pos T A)).hom ≫
      pos T A ◁ cap T A = (λ_ (pos T A)).hom ≫ (ρ_ (pos T A)).inv := by
  apply hom_ext T
  rw [hom_comp, hom_comp, cup_right, cap_left]
  change compose T _ (compose T ((α_ A (𝟙_ C) A).hom ⊗ₘ (α_ (𝟙_ C) A (𝟙_ C)).hom) _) =
    compose T ((λ_ A).hom ⊗ₘ (ρ_ (𝟙_ C)).inv)
      ((ρ_ A).inv ⊗ₘ (λ_ (𝟙_ C)).hom)
  rw [compose_tensor_left, compose_tensor_left]
  simp only [compose, exchange, T.vanishing_tensor, T.vanishing_unit,
    BraidedCategory.braiding_tensor_left_hom, BraidedCategory.braiding_tensor_right_hom,
    braiding_tensorUnit_left, braiding_tensorUnit_right]
  let l : (((𝟙_ C ⊗ A) ⊗ (𝟙_ C ⊗ 𝟙_ C)) ⊗ 𝟙_ C) ⟶ A :=
    𝟙 _ ⊗≫ 𝟙 A
  let r : A ⟶ (((A ⊗ 𝟙_ C) ⊗ (𝟙_ C ⊗ 𝟙_ C)) ⊗ 𝟙_ C) :=
    𝟙 A ⊗≫ 𝟙 _
  calc
    _ = (ρ_ _).inv ≫ T.trace (l ▷ A ≫ (β_ A A).hom ≫ r ▷ A) ≫ (ρ_ _).hom := by
      congr 2
      apply congrArg T.trace
      dsimp only [l, r]
      monoidal
    _ = _ := by
      rw [show T.trace (l ▷ A ≫ (β_ A A).hom ≫ r ▷ A) = l ≫ 𝟙 A ≫ r by
        simpa only [tensorHom_id, T.yanking] using T.naturality (β_ A A).hom l r]
      dsimp only [l, r]
      monoidal

private theorem cup_left (A B : C) :
    hom T (neg T B ◁ cup T A) =
      𝟙 ((𝟙_ C ⊗ 𝟙_ C) ⊗ ((A ⊗ 𝟙_ C) ⊗ B)) ⊗≫
        𝟙 (A ⊗ B) ⊗≫ 𝟙 ((𝟙_ C ⊗ (A ⊗ 𝟙_ C)) ⊗ (𝟙_ C ⊗ B)) := by
  change (tensorShuffle (𝟙_ C) (𝟙_ C) B (A ⊗ 𝟙_ C)).hom ≫
    (𝟙 _ ⊗ₘ ((λ_ (A ⊗ 𝟙_ C)).hom ≫ (ρ_ (A ⊗ 𝟙_ C)).inv)) ≫
    (tensorShuffle (𝟙_ C) (A ⊗ 𝟙_ C) B (𝟙_ C)).inv = _
  simp only [tensorShuffle, Iso.trans_hom, Iso.trans_inv, whiskerLeftIso_hom,
    whiskerLeftIso_inv, tensorμ, tensorδ, braiding_tensorUnit_left,
    braiding_tensorUnit_right,
    BraidedCategory.braiding_tensor_left_hom, BraidedCategory.braiding_tensor_right_hom,
    ← SymmetricCategory.braiding_swap_eq_inv_braiding]
  calc
    _ = 𝟙 ((𝟙_ C ⊗ 𝟙_ C) ⊗ ((A ⊗ 𝟙_ C) ⊗ B)) ⊗≫
        ((β_ A B).hom ≫ (β_ B A).hom) ⊗≫
          𝟙 ((𝟙_ C ⊗ (A ⊗ 𝟙_ C)) ⊗ (𝟙_ C ⊗ B)) := by monoidal
    _ = _ := by rw [SymmetricCategory.symmetry]

private theorem cap_right (A B : C) :
    hom T (cap T A ▷ neg T B) =
      𝟙 (((𝟙_ C ⊗ A) ⊗ 𝟙_ C) ⊗ (B ⊗ 𝟙_ C)) ⊗≫
        (β_ A B).hom ⊗≫ 𝟙 ((𝟙_ C ⊗ 𝟙_ C) ⊗ (B ⊗ (𝟙_ C ⊗ A))) := by
  change (tensorShuffle (𝟙_ C ⊗ A) (𝟙_ C) (𝟙_ C) B).hom ≫
    (((ρ_ (𝟙_ C ⊗ A)).hom ≫ (λ_ (𝟙_ C ⊗ A)).inv) ⊗ₘ 𝟙 _) ≫
    (tensorShuffle (𝟙_ C) (𝟙_ C) (𝟙_ C ⊗ A) B).inv = _
  simp only [tensorShuffle, Iso.trans_hom, Iso.trans_inv, whiskerLeftIso_hom,
    whiskerLeftIso_inv, tensorμ, tensorδ, braiding_tensorUnit_left,
    braiding_tensorUnit_right,
    ← SymmetricCategory.braiding_swap_eq_inv_braiding,
    BraidedCategory.braiding_tensor_right_hom, BraidedCategory.braiding_tensor_left_hom]
  monoidal

private theorem snake_neg (A : C) :
    neg T A ◁ cup T A ≫ (α_ (neg T A) (pos T A) (neg T A)).inv ≫
      cap T A ▷ neg T A = (ρ_ (neg T A)).hom ≫ (λ_ (neg T A)).inv := by
  apply hom_ext T
  rw [hom_comp, hom_comp, cup_left, cap_right]
  change compose T _ (compose T ((α_ (𝟙_ C) A (𝟙_ C)).inv ⊗ₘ (α_ A (𝟙_ C) A).inv) _) =
    compose T ((ρ_ (𝟙_ C)).hom ⊗ₘ (λ_ A).inv)
      ((λ_ (𝟙_ C)).inv ⊗ₘ (ρ_ A).hom)
  rw [compose_tensor_left, compose_tensor_left]
  simp only [compose, exchange, T.vanishing_tensor, T.vanishing_unit,
    BraidedCategory.braiding_tensor_left_hom, BraidedCategory.braiding_tensor_right_hom,
    braiding_tensorUnit_left, braiding_tensorUnit_right]
  let L := ((𝟙_ C ⊗ 𝟙_ C) ⊗ (A ⊗ 𝟙_ C))
  let R := ((𝟙_ C ⊗ 𝟙_ C) ⊗ (𝟙_ C ⊗ A))
  let l : L ⟶ A := 𝟙 L ⊗≫ 𝟙 A
  let r : A ⟶ R := 𝟙 A ⊗≫ 𝟙 R
  let b := (β_ A A).hom
  let l₂ : L ⊗ (A ⊗ 𝟙_ C) ⟶ A ⊗ A := 𝟙 _ ⊗≫ 𝟙 _
  let r₂ : A ⊗ A ⟶ R ⊗ (A ⊗ 𝟙_ C) := 𝟙 _ ⊗≫ 𝟙 _
  have hperm : b ▷ A ≫ exchange A A A ≫ exchange A A A ≫
      b ▷ A ≫ exchange A A A ≫ b ▷ A = exchange A A A ≫ b ▷ A := by
    simp only [exchange_exchange_assoc, ← comp_whiskerRight_assoc, b,
      SymmetricCategory.symmetry, id_whiskerRight, Category.id_comp]
  have ht : T.trace (exchange A A A ≫ b ▷ A) = b := by
    have h := T.naturality (exchange A A A) (𝟙 (A ⊗ A)) b
    have hy : T.trace (exchange A A A) = 𝟙 (A ⊗ A) := by
      simpa [exchange, T.yanking] using T.superposing (β_ A A).hom (𝟙 A)
    simpa [hy] using h
  have hi : T.trace (l₂ ▷ A ≫ (exchange A A A ≫ b ▷ A) ≫ r₂ ▷ A) =
      l₂ ≫ b ≫ r₂ := by
    simpa only [tensorHom_id, ht] using T.naturality (exchange A A A ≫ b ▷ A) l₂ r₂
  calc
    _ = T.trace ((ρ_ (L ⊗ A)).inv ≫ (α_ L A (𝟙_ C)).hom ≫
        T.trace (l₂ ▷ A ≫ (exchange A A A ≫ b ▷ A) ≫ r₂ ▷ A) ≫
          (α_ R A (𝟙_ C)).inv ≫ (ρ_ (R ⊗ A)).hom) := by
      apply congrArg T.trace
      simp only [Category.assoc]
      congr 3
      apply congrArg T.trace
      have hperm' := congrArg (fun k => l₂ ▷ A ≫ k ≫ r₂ ▷ A) hperm
      simp only [Category.assoc] at hperm'
      rw [← hperm']
      dsimp only [l₂, r₂, L, R, b]
      simp only [exchange]
      monoidal
    _ = T.trace (l ▷ A ≫ b ≫ r ▷ A) := by
      rw [hi]
      apply congrArg T.trace
      dsimp only [l, r, l₂, r₂, L, R]
      monoidal
    _ = _ := by
      rw [show T.trace (l ▷ A ≫ b ≫ r ▷ A) = l ≫ 𝟙 A ≫ r by
        simpa only [tensorHom_id, b, T.yanking] using T.naturality b l r]
      dsimp only [l, r, L, R]
      monoidal

/-- The embedded positive object pairs with the corresponding negative object.
This is a named pairing, not a global instance competing with tensor pairings. -/
@[instance_reducible]
def positivePairing (A : C) :
    ExactPairing (⟨A, 𝟙_ C⟩ : IntConstruction T) ⟨𝟙_ C, A⟩ where
  coevaluation' := ofHom T ((λ_ (A ⊗ 𝟙_ C)).hom ≫ (ρ_ (A ⊗ 𝟙_ C)).inv)
  evaluation' := ofHom T ((ρ_ (𝟙_ C ⊗ A)).hom ≫ (λ_ (𝟙_ C ⊗ A)).inv)
  coevaluation_evaluation' := by exact snake_neg T A
  evaluation_coevaluation' := by exact snake_pos T A

/-- Every Int object decomposes into its positive and negative components. -/
def decomposition (X : IntConstruction T) :
    X ≅ (⟨X.positive, 𝟙_ C⟩ : IntConstruction T) ⊗ ⟨𝟙_ C, X.negative⟩ :=
  pairIso T (ρ_ X.positive).symm (ρ_ X.negative)

/-- An object and its swapped pair form an exact pairing. -/
@[instance_reducible]
def exactPairing (X : IntConstruction T) : ExactPairing X (dual T X) := by
  letI := positivePairing T X.positive
  letI := positivePairing T X.negative
  letI := BraidedCategory.exactPairing_swap
    (⟨X.negative, 𝟙_ C⟩ : IntConstruction T) ⟨𝟙_ C, X.negative⟩
  exact exactPairingCongr (decomposition T X) (decomposition T (dual T X))

private theorem cup_left_pos (A B : C) :
    hom T (pos T B ◁ cup T A) =
      𝟙 ((B ⊗ 𝟙_ C) ⊗ ((A ⊗ 𝟙_ C) ⊗ 𝟙_ C)) ⊗≫
        𝟙 (B ⊗ A) ⊗≫ 𝟙 ((B ⊗ (A ⊗ 𝟙_ C)) ⊗ (𝟙_ C ⊗ 𝟙_ C)) := by
  change (tensorShuffle B (𝟙_ C) (𝟙_ C) (A ⊗ 𝟙_ C)).hom ≫
    (𝟙 _ ⊗ₘ ((λ_ (A ⊗ 𝟙_ C)).hom ≫ (ρ_ (A ⊗ 𝟙_ C)).inv)) ≫
    (tensorShuffle B (A ⊗ 𝟙_ C) (𝟙_ C) (𝟙_ C)).inv = _
  simp only [tensorShuffle, Iso.trans_hom, Iso.trans_inv, whiskerLeftIso_hom,
    whiskerLeftIso_inv, tensorμ, tensorδ,
    braiding_tensorUnit_right, braiding_inv_tensorUnit_right]
  monoidal

private def traceStart (X U : C) : pos T X ⟶ (pos T X ⊗ pos T U) ⊗ neg T U :=
  (ρ_ (pos T X)).inv ≫ pos T X ◁ cup T U ≫
    (α_ (pos T X) (pos T U) (neg T U)).inv

private def traceEnd (Y U : C) : (pos T Y ⊗ pos T U) ⊗ neg T U ⟶ pos T Y :=
  (α_ (pos T Y) (pos T U) (neg T U)).hom ≫
    pos T Y ◁ (β_ (pos T U) (neg T U)).hom ≫ pos T Y ◁ cap T U ≫
      (ρ_ (pos T Y)).hom

private theorem hom_traceStart (X U : C) : hom T (traceStart T X U) =
    𝟙 (X ⊗ (U ⊗ (𝟙_ C ⊗ 𝟙_ C))) ⊗≫
      𝟙 (X ⊗ U) ⊗≫ 𝟙 (((X ⊗ U) ⊗ 𝟙_ C) ⊗ 𝟙_ C) := by
  unfold traceStart
  rw [hom_comp, hom_comp, cup_left_pos]
  change compose T ((ρ_ X).inv ⊗ₘ (λ_ (𝟙_ C)).hom)
    (compose T _ ((α_ X U (𝟙_ C)).inv ⊗ₘ (α_ U (𝟙_ C) (𝟙_ C)).inv)) = _
  rw [compose_tensor_left, compose_tensor_right]
  monoidal

private theorem hom_traceEnd (Y U : C) : hom T (traceEnd T Y U) =
    𝟙 (((Y ⊗ U) ⊗ 𝟙_ C) ⊗ 𝟙_ C) ⊗≫
      𝟙 (Y ⊗ U) ⊗≫ 𝟙 (Y ⊗ (U ⊗ (𝟙_ C ⊗ 𝟙_ C))) := by
  unfold traceEnd
  change hom T (mapPair T _ _ ≫ tensorMap T (𝟙 _) (mapPair T _ _) ≫
    pos T Y ◁ cap T U ≫ mapPair T _ _) = _
  rw [← mapPair_id T (pos T Y), tensorMap_mapPair]
  rw [hom_comp, hom_comp, hom_comp, hom_mapPair, hom_mapPair, hom_mapPair, cap_left]
  rw [compose_tensor_left, compose_tensor_left, compose_tensor_right]
  dsimp
  simp only [braiding_tensorUnit_left, braiding_tensorUnit_right]
  monoidal

private theorem trace_positive {X Y U : C} (f : X ⊗ U ⟶ Y ⊗ U) :
    @SymmetricTrace.traceOfPairing (IntConstruction T) _ _ _
      (pos T X) (pos T Y) (pos T U) (neg T U) (positivePairing T U)
      (mapPair T (X := pos T X ⊗ pos T U) (Y := pos T Y ⊗ pos T U)
        f (𝟙 (𝟙_ C ⊗ 𝟙_ C))) = (embedding T).map (T.trace f) := by
  suffices h : traceStart T X U ≫ tensorMap T
      (mapPair T (X := pos T X ⊗ pos T U) (Y := pos T Y ⊗ pos T U) f (𝟙 _))
      (𝟙 (neg T U)) ≫ traceEnd T Y U = (embedding T).map (T.trace f) by
    change (ρ_ (pos T X)).inv ≫ pos T X ◁ cup T U ≫
      (α_ (pos T X) (pos T U) (neg T U)).inv ≫
      tensorMap T (mapPair T (X := pos T X ⊗ pos T U) (Y := pos T Y ⊗ pos T U)
        f (𝟙 _)) (𝟙 (neg T U)) ≫ traceEnd T Y U = _
    simpa only [traceStart, Category.assoc] using h
  rw [← mapPair_id T (neg T U), tensorMap_mapPair]
  apply hom_ext T
  rw [hom_comp, hom_comp, hom_traceStart, hom_traceEnd, hom_mapPair]
  rw [compose_tensor_left]
  change compose T _ ((f ⊗ₘ 𝟙 (𝟙_ C)) ▷ (𝟙_ C) ≫ _ ≫
    Y ◁ (𝟙 U ⊗ₘ 𝟙 (𝟙_ C ⊗ 𝟙_ C))) = T.trace f ▷ (𝟙_ C)
  simp only [compose, exchange, T.vanishing_tensor, T.vanishing_unit,
    BraidedCategory.braiding_tensor_right_hom,
    braiding_tensorUnit_left, braiding_tensorUnit_right,
    tensorHom_id]
  calc
    _ = T.trace ((ρ_ X).hom ▷ U ≫ f ≫ (ρ_ Y).inv ▷ U) := by
      apply congrArg T.trace
      monoidal
    _ = _ := by
      rw [show T.trace ((ρ_ X).hom ▷ U ≫ f ≫ (ρ_ Y).inv ▷ U) =
          (ρ_ X).hom ≫ T.trace f ≫ (ρ_ Y).inv by
        simpa only [tensorHom_id] using T.naturality f (ρ_ X).hom (ρ_ Y).inv]
      simp

/-- Int is compact closed: symmetric monoidal with both left and right duals.
The source is assumed traced, not rigid. -/
instance rigidCategory : RigidCategory (IntConstruction T) where
  rightDual X := { rightDual := dual T X, exact := exactPairing T X }
  leftDual X := { leftDual := dual T X, exact := exactPairing T (dual T X) }

@[simp] theorem dual_dual (X : IntConstruction T) : dual T (dual T X) = X := rfl

@[simp] theorem rightDual_eq (X : IntConstruction T) : Xᘁ = dual T X := rfl

@[simp] theorem leftDual_eq (X : IntConstruction T) : (ᘁX : IntConstruction T) = dual T X := rfl

/-- The fully faithful strong symmetric monoidal embedding preserves the supplied trace,
not just traces arising from pre-existing duals in the source. -/
theorem embedding_preserves_trace :
    T.Preserves (symmetricTraceOfRigid (IntConstruction T)) (embedding T) := by
  intro X Y U f
  have hk : Functor.LaxMonoidal.μ (embedding T) X U ≫ (embedding T).map f ≫
      Functor.OplaxMonoidal.δ (embedding T) Y U =
      mapPair T (X := pos T X ⊗ pos T U) (Y := pos T Y ⊗ pos T U)
        f (𝟙 (𝟙_ C ⊗ 𝟙_ C)) := by
    rw [embedding_μ, embedding_map_eq_mapPair]
    dsimp only [embedding]
    change mapPair T _ _ ≫ mapPair T _ _ ≫ mapPair T _ _ = _
    rw [mapPair_comp, mapPair_comp]
    simp
  rw [hk]
  dsimp only [embedding]
  change (embedding T).map (T.trace f) =
    @SymmetricTrace.traceOfPairing (IntConstruction T) _ _ _
      (pos T X) (pos T Y) (pos T U) (neg T U) (exactPairing T (pos T U)) _
  exact (trace_positive T f).symm.trans
    (SymmetricTrace.traceOfPairing_independent
      (p := positivePairing T U) (q := exactPairing T (⟨U, 𝟙_ C⟩ : IntConstruction T)) _)

end IntConstruction
end CategoryTheory
