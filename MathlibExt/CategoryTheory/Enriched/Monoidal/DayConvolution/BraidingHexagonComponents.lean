/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.BraidingTriple

/-!
# The genuine Day forward hexagon on the entire original coend

Cancellation along the actual flattening isomorphism reduces the equation
to all full original triple generators. Their weight equation is the
original inverse index hexagon; their coefficient equation is the original
value hexagon. No braiding or hexagon on the Day category is an input.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe uV vV uI vI
open CategoryTheory CategoryTheory.Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.BraidingHexagonComponents

private theorem three_steps {V : Type uV} [Category.{vV} V]
    {A₀ A₁ A₂ A₃ X₀ X₁ X₂ X₃ : V}
    (g₀ : A₀ ⟶ X₀) (g₁ : A₁ ⟶ X₁) (g₂ : A₂ ⟶ X₂) (g₃ : A₃ ⟶ X₃)
    (p : X₀ ⟶ X₁) (q : X₁ ⟶ X₂) (r : X₂ ⟶ X₃)
    (a : A₀ ⟶ A₁) (c : A₁ ⟶ A₂) (e : A₂ ⟶ A₃)
    (h₁ : g₀ ≫ p = a ≫ g₁) (h₂ : g₁ ≫ q = c ≫ g₂)
    (h₃ : g₂ ≫ r = e ≫ g₃) :
    g₀ ≫ p ≫ q ≫ r = a ≫ c ≫ e ≫ g₃ := by
  calc
    _ = a ≫ g₁ ≫ q ≫ r := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ q ≫ r) h₁
    _ = a ≫ c ≫ g₂ ≫ r := by
      simpa only [Category.assoc] using congrArg (fun t => a ≫ t ≫ r) h₂
    _ = _ := congrArg (fun t => a ≫ c ≫ t) h₃

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  (d : EnrichedMonoidalCategoryData V I)
  (b : EnrichedBraidedMonoidalCategoryData V I d)
  (F G H : EnrichedFunctor V I V) (k : I)

/-- The first complete Day hexagon path on every full original triple generator. -/
theorem left_trace (a c e : I) :
    BraidingTriple.leftAt d F G H k a c e ≫
        (AssociatorConstruction.componentIso d F G H k).hom ≫
        BraidingComponents.component d b F (Output.functor d.tensorEnrichedFunctor G H) k ≫
        (AssociatorConstruction.componentIso d G H F k).hom =
      ((eHomWhiskerRight V (α_ a c e).inv k ≫
        eHomWhiskerRight V (β_ a (c ⊗ e)).inv k ≫
        eHomWhiskerRight V (α_ c e a).inv k) ⊗ₘ
        ((α_ (F.obj a) (G.obj c) (H.obj e)).hom ≫
          (β_ (F.obj a) (G.obj c ⊗ H.obj e)).hom ≫
          (α_ (G.obj c) (H.obj e) (F.obj a)).hom)) ≫
        BraidingTriple.rightAt d G H F k c e a := by
  let A := F.obj a
  let B := G.obj c
  let C := H.obj e
  let g₀ := BraidingTriple.leftAt d F G H k a c e
  let g₁ := BraidingTriple.rightAt d F G H k a c e
  let g₂ := BraidingTriple.leftAt d G H F k c e a
  let g₃ := BraidingTriple.rightAt d G H F k c e a
  let p := (AssociatorConstruction.componentIso d F G H k).hom
  let q := BraidingComponents.component d b F (Output.functor d.tensorEnrichedFunctor G H) k
  let r := (AssociatorConstruction.componentIso d G H F k).hom
  let w₁ := eHomWhiskerRight V (α_ a c e).inv k
  let w₂ := eHomWhiskerRight V (β_ a (c ⊗ e)).inv k
  let w₃ := eHomWhiskerRight V (α_ c e a).inv k
  let v₁ := (α_ A B C).hom
  let v₂ := (β_ A (B ⊗ C)).hom
  let v₃ := (α_ B C A).hom
  have h₁ : g₀ ≫ p = (w₁ ⊗ₘ v₁) ≫ g₁ :=
    (Category.assoc (AssociatorFlat.leftGenerator d F G H k ((a, c), e))
      (AssociatorFlattening.flatToNested d F G H k) p).trans
        (AssociatorConstruction.tripleGenerator_hom d F G H k ((a, c), e))
  have h₂ : g₁ ≫ q = (w₂ ⊗ₘ v₂) ≫ g₂ := BraidingTriple.outer_right d b F G H k a c e
  have h₃ : g₂ ≫ r = (w₃ ⊗ₘ v₃) ≫ g₃ :=
    (Category.assoc (AssociatorFlat.leftGenerator d G H F k ((c, e), a))
      (AssociatorFlattening.flatToNested d G H F k) r).trans
        (AssociatorConstruction.tripleGenerator_hom d G H F k ((c, e), a))
  have ht : (w₁ ⊗ₘ v₁) ≫ (w₂ ⊗ₘ v₂) ≫ (w₃ ⊗ₘ v₃) =
      (w₁ ≫ w₂ ≫ w₃) ⊗ₘ (v₁ ≫ v₂ ≫ v₃) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  have h := three_steps g₀ g₁ g₂ g₃ p q r
    (w₁ ⊗ₘ v₁) (w₂ ⊗ₘ v₂) (w₃ ⊗ₘ v₃) h₁ h₂ h₃
  have h' := congrArg (fun t => t ≫ g₃) ht
  simp only [Category.assoc] at h'
  exact h.trans h'

/-- The second complete Day hexagon path on every full original triple generator. -/
theorem right_trace (a c e : I) :
    BraidingTriple.leftAt d F G H k a c e ≫
        Input.mapAt d.tensorEnrichedFunctor (BraidingFunctor.functorIso d b F G).hom
          (GradedNatTrans.unitId H) k ≫
        (AssociatorConstruction.componentIso d G F H k).hom ≫
        Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId G)
          (BraidingFunctor.functorIso d b F H).hom k =
      ((eHomWhiskerRight V ((β_ a c).inv ▷ e) k ≫
        eHomWhiskerRight V (α_ c a e).inv k ≫
        eHomWhiskerRight V (c ◁ (β_ a e).inv) k) ⊗ₘ
        ((β_ (F.obj a) (G.obj c)).hom ▷ H.obj e ≫
          (α_ (G.obj c) (F.obj a) (H.obj e)).hom ≫
          G.obj c ◁ (β_ (F.obj a) (H.obj e)).hom)) ≫
        BraidingTriple.rightAt d G H F k c e a := by
  let A := F.obj a
  let B := G.obj c
  let C := H.obj e
  let g₀ := BraidingTriple.leftAt d F G H k a c e
  let g₁ := BraidingTriple.leftAt d G F H k c a e
  let g₂ := BraidingTriple.rightAt d G F H k c a e
  let g₃ := BraidingTriple.rightAt d G H F k c e a
  let p := Input.mapAt d.tensorEnrichedFunctor (BraidingFunctor.functorIso d b F G).hom
    (GradedNatTrans.unitId H) k
  let q := (AssociatorConstruction.componentIso d G F H k).hom
  let r := Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId G)
    (BraidingFunctor.functorIso d b F H).hom k
  let w₁ := eHomWhiskerRight V ((β_ a c).inv ▷ e) k
  let w₂ := eHomWhiskerRight V (α_ c a e).inv k
  let w₃ := eHomWhiskerRight V (c ◁ (β_ a e).inv) k
  let v₁ := (β_ A B).hom ▷ C
  let v₂ := (α_ B A C).hom
  let v₃ := B ◁ (β_ A C).hom
  have h₁ : g₀ ≫ p = (w₁ ⊗ₘ v₁) ≫ g₁ := by
    have h := BraidingTriple.inner_left d b F G H k a c e
    simp only [tensorHom_id] at h
    exact h
  have h₂ : g₁ ≫ q = (w₂ ⊗ₘ v₂) ≫ g₂ :=
    (Category.assoc (AssociatorFlat.leftGenerator d G F H k ((c, a), e))
      (AssociatorFlattening.flatToNested d G F H k) q).trans
        (AssociatorConstruction.tripleGenerator_hom d G F H k ((c, a), e))
  have h₃ : g₂ ≫ r = (w₃ ⊗ₘ v₃) ≫ g₃ := by
    have h := BraidingTriple.inner_right d b G F H k c a e
    simp only [id_tensorHom] at h
    exact h
  have ht : (w₁ ⊗ₘ v₁) ≫ (w₂ ⊗ₘ v₂) ≫ (w₃ ⊗ₘ v₃) =
      (w₁ ≫ w₂ ≫ w₃) ⊗ₘ (v₁ ≫ v₂ ≫ v₃) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  have h := three_steps g₀ g₁ g₂ g₃ p q r
    (w₁ ⊗ₘ v₁) (w₂ ⊗ₘ v₂) (w₃ ⊗ₘ v₃) h₁ h₂ h₃
  have h' := congrArg (fun t => t ≫ g₃) ht
  simp only [Category.assoc] at h'
  exact h.trans h'

/-- Every full original triple generator satisfies the actual Day forward hexagon. -/
theorem generator_forward (a c e : I) :
    BraidingTriple.leftAt d F G H k a c e ≫
        (AssociatorConstruction.componentIso d F G H k).hom ≫
        BraidingComponents.component d b F (Output.functor d.tensorEnrichedFunctor G H) k ≫
        (AssociatorConstruction.componentIso d G H F k).hom =
      BraidingTriple.leftAt d F G H k a c e ≫
        Input.mapAt d.tensorEnrichedFunctor (BraidingFunctor.functorIso d b F G).hom
          (GradedNatTrans.unitId H) k ≫
        (AssociatorConstruction.componentIso d G F H k).hom ≫
        Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId G)
          (BraidingFunctor.functorIso d b F H).hom k := by
  have hw : eHomWhiskerRight V (α_ a c e).inv k ≫
        eHomWhiskerRight V (β_ a (c ⊗ e)).inv k ≫
        eHomWhiskerRight V (α_ c e a).inv k =
      eHomWhiskerRight V ((β_ a c).inv ▷ e) k ≫
        eHomWhiskerRight V (α_ c a e).inv k ≫
        eHomWhiskerRight V (c ◁ (β_ a e).inv) k := by
    have h := congrArg (fun f => eHomWhiskerRight V f k) (hexagon_forward_inv a c e)
    simp only [eHomWhiskerRight_comp, Category.assoc] at h
    exact h
  have hv : (α_ (F.obj a) (G.obj c) (H.obj e)).hom ≫
        (β_ (F.obj a) (G.obj c ⊗ H.obj e)).hom ≫
        (α_ (G.obj c) (H.obj e) (F.obj a)).hom =
      (β_ (F.obj a) (G.obj c)).hom ▷ H.obj e ≫
        (α_ (G.obj c) (F.obj a) (H.obj e)).hom ≫
        G.obj c ◁ (β_ (F.obj a) (H.obj e)).hom :=
    hexagon_forward (F.obj a) (G.obj c) (H.obj e)
  have h := congrArg (fun t => t ≫ BraidingTriple.rightAt d G H F k c e a)
    (congrArg₂ (fun w v => w ⊗ₘ v) hw hv)
  exact (left_trace d b F G H k a c e).trans
    (h.trans (right_trace d b F G H k a c e).symm)

/-- The full original Day associator and actual coend braid satisfy the forward hexagon. -/
theorem forward :
    (AssociatorConstruction.componentIso d F G H k).hom ≫
        BraidingComponents.component d b F (Output.functor d.tensorEnrichedFunctor G H) k ≫
        (AssociatorConstruction.componentIso d G H F k).hom =
      Input.mapAt d.tensorEnrichedFunctor (BraidingFunctor.functorIso d b F G).hom
        (GradedNatTrans.unitId H) k ≫
        (AssociatorConstruction.componentIso d G F H k).hom ≫
        Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId G)
          (BraidingFunctor.functorIso d b F H).hom k := by
  apply (cancel_epi (AssociatorFlattening.iso d F G H k).hom).1
  apply Enriched.weightedCoend.hom_ext (AssociatorIndex.leftWeight d k)
    (Associator.leftCoefficients F G H)
  rintro ⟨⟨a, c⟩, e⟩
  let γ := AssociatorFlat.leftGenerator d F G H k ((a, c), e)
  let f := AssociatorFlattening.flatToNested d F G H k
  let l := (AssociatorConstruction.componentIso d F G H k).hom ≫
    BraidingComponents.component d b F (Output.functor d.tensorEnrichedFunctor G H) k ≫
    (AssociatorConstruction.componentIso d G H F k).hom
  let r := Input.mapAt d.tensorEnrichedFunctor (BraidingFunctor.functorIso d b F G).hom
    (GradedNatTrans.unitId H) k ≫ (AssociatorConstruction.componentIso d G F H k).hom ≫
    Input.mapAt d.tensorEnrichedFunctor (GradedNatTrans.unitId G)
      (BraidingFunctor.functorIso d b F H).hom k
  have h := generator_forward d b F G H k a c e
  change (γ ≫ f) ≫ l = (γ ≫ f) ≫ r at h
  change γ ≫ f ≫ l = γ ≫ f ≫ r
  exact (Category.assoc γ f l).symm.trans (h.trans (Category.assoc γ f r))

end CategoryTheory.EnrichedDayKernel.BraidingHexagonComponents
