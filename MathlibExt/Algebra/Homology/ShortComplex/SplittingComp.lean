/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Composition of split short complexes

Let X → Y → Z₁ and Y → Z → Z₂ be split short complexes in a preadditive category with the
biproduct Z₁ ⊕ Z₂. The composite X → Z admits the quotient map (g₁ ∘ r₂,g₂) : Z → Z₁ ⊕ Z₂, where
r₂ retracts Y → Z.

The two splittings give a splitting of X → Z → Z₁ ⊕ Z₂. In particular, the displayed quotient
map is a cokernel of the composite X → Z.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex.Splitting

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Let C be preadditive and let X —f₁→ Y —g₁→ Z₁ and Y —f₂→ Z —g₂→ Z₂ be short complexes with g₁ ∘
f₁=g₂ ∘ f₂=0. Assume the biproduct Z₁ ⊕ Z₂ exists, and let s₂ be a splitting of the second
complex with retraction r₂ : Z → Y. The map (g₁ ∘ r₂,g₂) : Z → Z₁ ⊕ Z₂ kills f₂ ∘ f₁ : X → Z. No
splitting of the first short complex is needed for this zero-composite equation. -/
theorem compLeft_zero
    {X Y Z Z₁ Z₂ : C}
    {f₁ : X ⟶ Y} {g₁ : Y ⟶ Z₁} {w₁ : f₁ ≫ g₁ = 0}
    {f₂ : Y ⟶ Z} {g₂ : Z ⟶ Z₂} {w₂ : f₂ ≫ g₂ = 0}
    [HasBinaryBiproduct Z₁ Z₂]
    (s₂ : (ShortComplex.mk f₂ g₂ w₂).Splitting) :
    (f₁ ≫ f₂) ≫ biprod.lift (s₂.r ≫ g₁) g₂ = 0 := by
  apply biprod.hom_ext
  · calc ((f₁ ≫ f₂) ≫ biprod.lift (s₂.r ≫ g₁) g₂) ≫ biprod.fst
        = (f₁ ≫ f₂) ≫ (biprod.lift (s₂.r ≫ g₁) g₂ ≫ biprod.fst) := by
          simp only [Category.assoc]
      _ = (f₁ ≫ f₂) ≫ (s₂.r ≫ g₁) := by simp [biprod.lift_fst]
      _ = f₁ ≫ (f₂ ≫ s₂.r) ≫ g₁ := by simp only [Category.assoc]
      _ = f₁ ≫ g₁ := by rw [s₂.f_r]; simp
      _ = 0 := w₁
      _ = 0 ≫ biprod.fst := by simp
  · calc ((f₁ ≫ f₂) ≫ biprod.lift (s₂.r ≫ g₁) g₂) ≫ biprod.snd
        = (f₁ ≫ f₂) ≫ (biprod.lift (s₂.r ≫ g₁) g₂ ≫ biprod.snd) := by
          simp only [Category.assoc]
      _ = (f₁ ≫ f₂) ≫ g₂ := by simp [biprod.lift_snd]
      _ = f₁ ≫ (f₂ ≫ g₂) := by simp only [Category.assoc]
      _ = f₁ ≫ 0 := by rw [w₂]
      _ = 0 := by simp
      _ = 0 ≫ biprod.snd := by simp

/-- Let C be preadditive and let X —f₁→ Y —g₁→ Z₁ and Y —f₂→ Z —g₂→ Z₂ be short complexes with g₁ ∘
f₁=g₂ ∘ f₂=0. Assume the biproduct Z₁ ⊕ Z₂ exists, and let s₂ be a splitting of the second
complex with retraction r₂ : Z → Y. If the first complex also has a splitting s₁, then X —f₂∘f₁→
Z —(g₁∘r₂,g₂)→ Z₁ ⊕ Z₂ is split, with the splitting constructed from s₁ and s₂. -/
noncomputable def compLeft
    {X Y Z Z₁ Z₂ : C}
    {f₁ : X ⟶ Y} {g₁ : Y ⟶ Z₁} {w₁ : f₁ ≫ g₁ = 0}
    {f₂ : Y ⟶ Z} {g₂ : Z ⟶ Z₂} {w₂ : f₂ ≫ g₂ = 0}
    [HasBinaryBiproduct Z₁ Z₂]
    (s₁ : (ShortComplex.mk f₁ g₁ w₁).Splitting)
    (s₂ : (ShortComplex.mk f₂ g₂ w₂).Splitting) :
    (ShortComplex.mk (f₁ ≫ f₂) (biprod.lift (s₂.r ≫ g₁) g₂)
      (compLeft_zero (w₁ := w₁) s₂)).Splitting where
  r := s₂.r ≫ s₁.r
  s := biprod.desc (s₁.s ≫ f₂) s₂.s
  f_r := by
    calc (f₁ ≫ f₂) ≫ (s₂.r ≫ s₁.r)
        = f₁ ≫ (f₂ ≫ s₂.r) ≫ s₁.r := by simp only [Category.assoc]
      _ = f₁ ≫ s₁.r := by rw [s₂.f_r]; simp
      _ = 𝟙 X := s₁.f_r
  s_g := by
    apply biprod.hom_ext'
    · have h_inl : biprod.inl ≫ biprod.desc (s₁.s ≫ f₂) s₂.s = s₁.s ≫ f₂ := by
        simp [biprod.inl_desc]
      have h_comp_inl : (s₁.s ≫ f₂) ≫ biprod.lift (s₂.r ≫ g₁) g₂ = biprod.inl := by
        apply biprod.hom_ext
        · calc ((s₁.s ≫ f₂) ≫ biprod.lift (s₂.r ≫ g₁) g₂) ≫ biprod.fst
              = (s₁.s ≫ f₂) ≫ (biprod.lift (s₂.r ≫ g₁) g₂ ≫ biprod.fst) := by
                simp only [Category.assoc]
            _ = (s₁.s ≫ f₂) ≫ (s₂.r ≫ g₁) := by simp [biprod.lift_fst]
            _ = s₁.s ≫ (f₂ ≫ s₂.r) ≫ g₁ := by simp only [Category.assoc]
            _ = s₁.s ≫ g₁ := by rw [s₂.f_r]; simp
            _ = 𝟙 Z₁ := s₁.s_g
            _ = biprod.inl ≫ biprod.fst := by simp
        · calc ((s₁.s ≫ f₂) ≫ biprod.lift (s₂.r ≫ g₁) g₂) ≫ biprod.snd
              = (s₁.s ≫ f₂) ≫ g₂ := by simp only [Category.assoc, biprod.lift_snd]
            _ = s₁.s ≫ (f₂ ≫ g₂) := by simp only [Category.assoc]
            _ = s₁.s ≫ 0 := by rw [w₂]
            _ = 0 := by simp
            _ = biprod.inl ≫ biprod.snd := by simp
      calc biprod.inl ≫ biprod.desc (s₁.s ≫ f₂) s₂.s ≫ biprod.lift (s₂.r ≫ g₁) g₂
          = (biprod.inl ≫ biprod.desc (s₁.s ≫ f₂) s₂.s) ≫
            biprod.lift (s₂.r ≫ g₁) g₂ := by simp only [Category.assoc]
        _ = (s₁.s ≫ f₂) ≫ biprod.lift (s₂.r ≫ g₁) g₂ := by rw [h_inl]
        _ = biprod.inl := h_comp_inl
        _ = biprod.inl ≫ 𝟙 (Z₁ ⊞ Z₂) := by simp
    · have h_inr : biprod.inr ≫ biprod.desc (s₁.s ≫ f₂) s₂.s = s₂.s := by
        simp [biprod.inr_desc]
      have h_comp_inr : s₂.s ≫ biprod.lift (s₂.r ≫ g₁) g₂ = biprod.inr := by
        apply biprod.hom_ext
        · calc (s₂.s ≫ biprod.lift (s₂.r ≫ g₁) g₂) ≫ biprod.fst
              = s₂.s ≫ (biprod.lift (s₂.r ≫ g₁) g₂ ≫ biprod.fst) := by
                simp only [Category.assoc]
            _ = s₂.s ≫ (s₂.r ≫ g₁) := by simp [biprod.lift_fst]
            _ = (s₂.s ≫ s₂.r) ≫ g₁ := by simp only [Category.assoc]
            _ = 0 ≫ g₁ := by rw [s₂.s_r]
            _ = 0 := by simp
            _ = biprod.inr ≫ biprod.fst := by simp
        · calc (s₂.s ≫ biprod.lift (s₂.r ≫ g₁) g₂) ≫ biprod.snd
              = s₂.s ≫ g₂ := by simp only [Category.assoc, biprod.lift_snd]
            _ = 𝟙 Z₂ := s₂.s_g
            _ = biprod.inr ≫ biprod.snd := by simp
      calc biprod.inr ≫ biprod.desc (s₁.s ≫ f₂) s₂.s ≫ biprod.lift (s₂.r ≫ g₁) g₂
          = (biprod.inr ≫ biprod.desc (s₁.s ≫ f₂) s₂.s) ≫
            biprod.lift (s₂.r ≫ g₁) g₂ := by simp only [Category.assoc]
        _ = s₂.s ≫ biprod.lift (s₂.r ≫ g₁) g₂ := by rw [h_inr]
        _ = biprod.inr := h_comp_inr
        _ = biprod.inr ≫ 𝟙 (Z₁ ⊞ Z₂) := by simp
  id := by
    have h_lift_desc : biprod.lift (s₂.r ≫ g₁) g₂ ≫ biprod.desc (s₁.s ≫ f₂) s₂.s =
        (s₂.r ≫ g₁) ≫ (s₁.s ≫ f₂) + g₂ ≫ s₂.s := by
      rw [biprod.lift_desc]
    calc (s₂.r ≫ s₁.r) ≫ (f₁ ≫ f₂) +
          biprod.lift (s₂.r ≫ g₁) g₂ ≫ biprod.desc (s₁.s ≫ f₂) s₂.s
        = (s₂.r ≫ s₁.r) ≫ (f₁ ≫ f₂) +
          ((s₂.r ≫ g₁) ≫ (s₁.s ≫ f₂) + g₂ ≫ s₂.s) := by rw [h_lift_desc]
      _ = s₂.r ≫ s₁.r ≫ f₁ ≫ f₂ + (s₂.r ≫ g₁ ≫ s₁.s ≫ f₂ + g₂ ≫ s₂.s) := by
          simp only [Category.assoc]
      _ = (s₂.r ≫ s₁.r ≫ f₁ ≫ f₂ + s₂.r ≫ g₁ ≫ s₁.s ≫ f₂) + g₂ ≫ s₂.s := by
          abel
      _ = (s₂.r ≫ (s₁.r ≫ f₁) ≫ f₂ + s₂.r ≫ (g₁ ≫ s₁.s) ≫ f₂) + g₂ ≫ s₂.s := by
          simp only [Category.assoc]
      _ = s₂.r ≫ (s₁.r ≫ f₁ + g₁ ≫ s₁.s) ≫ f₂ + g₂ ≫ s₂.s := by
          simp only [Category.assoc, Preadditive.add_comp,
            Preadditive.comp_add]
      _ = s₂.r ≫ f₂ + g₂ ≫ s₂.s := by rw [s₁.id]; simp
      _ = 𝟙 Z := s₂.id

@[simp]
theorem compLeft_r
    {X Y Z Z₁ Z₂ : C}
    {f₁ : X ⟶ Y} {g₁ : Y ⟶ Z₁} {w₁ : f₁ ≫ g₁ = 0}
    {f₂ : Y ⟶ Z} {g₂ : Z ⟶ Z₂} {w₂ : f₂ ≫ g₂ = 0}
    [HasBinaryBiproduct Z₁ Z₂]
    (s₁ : (ShortComplex.mk f₁ g₁ w₁).Splitting)
    (s₂ : (ShortComplex.mk f₂ g₂ w₂).Splitting) :
    (compLeft s₁ s₂).r = s₂.r ≫ s₁.r :=
  rfl

@[simp]
theorem compLeft_s
    {X Y Z Z₁ Z₂ : C}
    {f₁ : X ⟶ Y} {g₁ : Y ⟶ Z₁} {w₁ : f₁ ≫ g₁ = 0}
    {f₂ : Y ⟶ Z} {g₂ : Z ⟶ Z₂} {w₂ : f₂ ≫ g₂ = 0}
    [HasBinaryBiproduct Z₁ Z₂]
    (s₁ : (ShortComplex.mk f₁ g₁ w₁).Splitting)
    (s₂ : (ShortComplex.mk f₂ g₂ w₂).Splitting) :
    (compLeft s₁ s₂).s = biprod.desc (s₁.s ≫ f₂) s₂.s :=
  rfl

/-- Let C be preadditive and let X —f₁→ Y —g₁→ Z₁ and Y —f₂→ Z —g₂→ Z₂ be short complexes with g₁ ∘
f₁=g₂ ∘ f₂=0. Assume the biproduct Z₁ ⊕ Z₂ exists, and let s₂ be a splitting of the second
complex with retraction r₂ : Z → Y. The quotient (g₁ ∘ r₂,g₂) : Z → Z₁ ⊕ Z₂ and its zero
composite with f₂ ∘ f₁ define a cokernel cofork for the composite left arrow. -/
noncomputable def compLeftCokernelCofork
    {X Y Z Z₁ Z₂ : C}
    {f₁ : X ⟶ Y} {g₁ : Y ⟶ Z₁} {w₁ : f₁ ≫ g₁ = 0}
    {f₂ : Y ⟶ Z} {g₂ : Z ⟶ Z₂} {w₂ : f₂ ≫ g₂ = 0}
    [HasBinaryBiproduct Z₁ Z₂]
    (s₂ : (ShortComplex.mk f₂ g₂ w₂).Splitting) :
    CokernelCofork (f₁ ≫ f₂) :=
  CokernelCofork.ofπ (biprod.lift (s₂.r ≫ g₁) g₂)
    (compLeft_zero (w₁ := w₁) s₂)

@[simp]
theorem compLeftCokernelCofork_π
    {X Y Z Z₁ Z₂ : C}
    {f₁ : X ⟶ Y} {g₁ : Y ⟶ Z₁} {w₁ : f₁ ≫ g₁ = 0}
    {f₂ : Y ⟶ Z} {g₂ : Z ⟶ Z₂} {w₂ : f₂ ≫ g₂ = 0}
    [HasBinaryBiproduct Z₁ Z₂]
    (s₂ : (ShortComplex.mk f₂ g₂ w₂).Splitting) :
    (compLeftCokernelCofork (f₁ := f₁) (g₁ := g₁) (w₁ := w₁) s₂).π =
      biprod.lift (s₂.r ≫ g₁) g₂ :=
  rfl

/-- Let C be preadditive and let X —f₁→ Y —g₁→ Z₁ and Y —f₂→ Z —g₂→ Z₂ be short complexes with g₁ ∘
f₁=g₂ ∘ f₂=0. Assume the biproduct Z₁ ⊕ Z₂ exists, and let s₂ be a splitting of the second
complex with retraction r₂ : Z → Y. If the first short complex is also split, the cofork with
quotient (g₁ ∘ r₂,g₂) is colimiting. Hence Z₁ ⊕ Z₂ is a cokernel of f₂ ∘ f₁ : X → Z. -/
noncomputable def compLeftCokernelCoforkIsColimit
    {X Y Z Z₁ Z₂ : C}
    {f₁ : X ⟶ Y} {g₁ : Y ⟶ Z₁} {w₁ : f₁ ≫ g₁ = 0}
    {f₂ : Y ⟶ Z} {g₂ : Z ⟶ Z₂} {w₂ : f₂ ≫ g₂ = 0}
    [HasBinaryBiproduct Z₁ Z₂]
    (s₁ : (ShortComplex.mk f₁ g₁ w₁).Splitting)
    (s₂ : (ShortComplex.mk f₂ g₂ w₂).Splitting) :
    IsColimit (compLeftCokernelCofork
      (f₁ := f₁) (g₁ := g₁) (w₁ := w₁) s₂) := by
  let s := compLeft s₁ s₂
  let q : Z ⟶ Z₁ ⊞ Z₂ := biprod.lift (s₂.r ≫ g₁) g₂
  letI : Epi q := by
    change Epi (ShortComplex.mk (f₁ ≫ f₂) q
      (compLeft_zero (w₁ := w₁) s₂)).g
    exact s.epi_g
  change IsColimit (CokernelCofork.ofπ q
    (compLeft_zero (w₁ := w₁) s₂))
  refine CokernelCofork.IsColimit.ofπ' q
    (compLeft_zero (w₁ := w₁) s₂) ?_
  intro T k hk
  refine ⟨s.s ≫ k, ?_⟩
  have h := congrArg (fun t : Z ⟶ Z => t ≫ k) s.id
  simpa only [Preadditive.add_comp, Category.assoc, hk, comp_zero,
    zero_add, Category.id_comp] using h

end CategoryTheory.ShortComplex.Splitting

end
