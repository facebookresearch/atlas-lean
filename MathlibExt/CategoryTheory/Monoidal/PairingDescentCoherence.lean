/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.Monoidal.TensorCokernel
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Associative pairings under kernels and quotients

The same original multiplication diagrams give associativity after a
monomorphic output comparison or an epimorphic tensor input comparison.
These lemmas use the actual maps in each diagram.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A B D X Y L Q A' B' D' X' Y' L' Q' : C}

/-- Two successive original products preserve the original projection into the left-associated output. -/
lemma iteratedPair_left_projection
    (a : A ⟶ A') (b : B ⟶ B') (d₀ : D ⟶ D') (x : X ⟶ X') (l : L ⟶ L') (q : Q ⟶ Q')
    (f : A ⊗ B ⟶ X) (g : X ⊗ D ⟶ L) (f' : A' ⊗ B' ⟶ X') (g' : X' ⊗ D' ⟶ L')
    (c : L ⟶ Q) (c' : L' ⟶ Q')
    (hf : f ≫ x = (a ⊗ₘ b) ≫ f') (hg : g ≫ l = (x ⊗ₘ d₀) ≫ g') (hc : c ≫ q = l ≫ c') :
    (f ⊗ₘ 𝟙 D) ≫ g ≫ c ≫ q = ((a ⊗ₘ b) ⊗ₘ d₀) ≫ (f' ⊗ₘ 𝟙 D') ≫ g' ≫ c' := by
  have ht : (f ⊗ₘ 𝟙 D) ≫ (x ⊗ₘ d₀) = ((a ⊗ₘ b) ⊗ₘ d₀) ≫ (f' ⊗ₘ 𝟙 D') := by
    rw [tensorHom_comp_tensorHom, hf, tensorHom_comp_tensorHom]
    simp only [Category.id_comp, Category.comp_id]
  rw [hc, ← Category.assoc g l c', hg]
  simp only [Category.assoc]
  rw [← Category.assoc (f ⊗ₘ 𝟙 D) (x ⊗ₘ d₀) (g' ≫ c'), ht, Category.assoc]

/-- The actual associator and two original products preserve the right-associated output projection. -/
lemma iteratedPair_right_projection
    (a : A ⟶ A') (b : B ⟶ B') (d₀ : D ⟶ D') (y : Y ⟶ Y') (q : Q ⟶ Q')
    (h : B ⊗ D ⟶ Y) (k : A ⊗ Y ⟶ Q) (h' : B' ⊗ D' ⟶ Y') (k' : A' ⊗ Y' ⟶ Q')
    (hh : h ≫ y = (b ⊗ₘ d₀) ≫ h') (hk : k ≫ q = (a ⊗ₘ y) ≫ k') :
    (α_ A B D).hom ≫ (𝟙 A ⊗ₘ h) ≫ k ≫ q =
      ((a ⊗ₘ b) ⊗ₘ d₀) ≫ (α_ A' B' D').hom ≫ (𝟙 A' ⊗ₘ h') ≫ k' := by
  have ht : (𝟙 A ⊗ₘ h) ≫ (a ⊗ₘ y) = (a ⊗ₘ (b ⊗ₘ d₀)) ≫ (𝟙 A' ⊗ₘ h') := by
    rw [tensorHom_comp_tensorHom, hh, tensorHom_comp_tensorHom]
    simp only [Category.id_comp, Category.comp_id]
  rw [hk, ← Category.assoc (𝟙 A ⊗ₘ h) (a ⊗ₘ y) k', ht]
  simp only [Category.assoc]
  rw [← associator_naturality_assoc]

/-- A monomorphic actual output comparison transfers an original associative pairing diagram. -/
lemma pairing_associativity_of_mono_projection
    (a : A ⟶ A') (b : B ⟶ B') (d₀ : D ⟶ D') (x : X ⟶ X') (y : Y ⟶ Y')
    (l : L ⟶ L') (q : Q ⟶ Q') [Mono q]
    (f : A ⊗ B ⟶ X) (g : X ⊗ D ⟶ L) (h : B ⊗ D ⟶ Y) (k : A ⊗ Y ⟶ Q)
    (f' : A' ⊗ B' ⟶ X') (g' : X' ⊗ D' ⟶ L') (h' : B' ⊗ D' ⟶ Y') (k' : A' ⊗ Y' ⟶ Q')
    (c : L ⟶ Q) (c' : L' ⟶ Q')
    (hf : f ≫ x = (a ⊗ₘ b) ≫ f') (hg : g ≫ l = (x ⊗ₘ d₀) ≫ g')
    (hh : h ≫ y = (b ⊗ₘ d₀) ≫ h') (hk : k ≫ q = (a ⊗ₘ y) ≫ k') (hc : c ≫ q = l ≫ c')
    (hassoc : (f' ⊗ₘ 𝟙 D') ≫ g' ≫ c' = (α_ A' B' D').hom ≫ (𝟙 A' ⊗ₘ h') ≫ k') :
    (f ⊗ₘ 𝟙 D) ≫ g ≫ c = (α_ A B D).hom ≫ (𝟙 A ⊗ₘ h) ≫ k := by
  apply (cancel_mono q).mp
  simp only [Category.assoc]
  rw [iteratedPair_left_projection a b d₀ x l q f g f' g' c c' hf hg hc,
    iteratedPair_right_projection a b d₀ y q h k h' k' hh hk, hassoc]

/-- An epimorphic actual tensor input comparison descends the original associative pairing diagram. -/
lemma pairing_associativity_of_epi_projection
    (a : A ⟶ A') (b : B ⟶ B') (d₀ : D ⟶ D') (x : X ⟶ X') (y : Y ⟶ Y')
    (l : L ⟶ L') (q : Q ⟶ Q') [Epi ((a ⊗ₘ b) ⊗ₘ d₀)]
    (f : A ⊗ B ⟶ X) (g : X ⊗ D ⟶ L) (h : B ⊗ D ⟶ Y) (k : A ⊗ Y ⟶ Q)
    (f' : A' ⊗ B' ⟶ X') (g' : X' ⊗ D' ⟶ L') (h' : B' ⊗ D' ⟶ Y') (k' : A' ⊗ Y' ⟶ Q')
    (c : L ⟶ Q) (c' : L' ⟶ Q')
    (hf : f ≫ x = (a ⊗ₘ b) ≫ f') (hg : g ≫ l = (x ⊗ₘ d₀) ≫ g')
    (hh : h ≫ y = (b ⊗ₘ d₀) ≫ h') (hk : k ≫ q = (a ⊗ₘ y) ≫ k') (hc : c ≫ q = l ≫ c')
    (hassoc : (f ⊗ₘ 𝟙 D) ≫ g ≫ c = (α_ A B D).hom ≫ (𝟙 A ⊗ₘ h) ≫ k) :
    (f' ⊗ₘ 𝟙 D') ≫ g' ≫ c' = (α_ A' B' D').hom ≫ (𝟙 A' ⊗ₘ h') ≫ k' := by
  apply (cancel_epi ((a ⊗ₘ b) ⊗ₘ d₀)).mp
  rw [← iteratedPair_left_projection a b d₀ x l q f g f' g' c c' hf hg hc,
    ← iteratedPair_right_projection a b d₀ y q h k h' k' hh hk]
  simpa only [Category.assoc] using congrArg (fun z => z ≫ q) hassoc

section TensorEpimorphisms

variable [Abelian C] [MonoidalPreadditive C]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft A)]
  [∀ A : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight A)]

/-- Preserving the actual cokernels preserves the tensor of any two original epimorphisms. -/
lemma epi_tensorHom_of_preservesCokernels {A B D F : C} (f : A ⟶ B) (g : D ⟶ F)
    [Epi f] [Epi g] : Epi (f ⊗ₘ g) := by
  let c₁ : CokernelCofork (kernel.ι f) := CokernelCofork.ofπ f (kernel.condition f)
  let c₂ : CokernelCofork (kernel.ι g) := CokernelCofork.ofπ g (kernel.condition g)
  exact CokernelCofork.epi_tensor_π c₁ (Abelian.epiIsCokernelOfKernel _ (limit.isLimit _))
    c₂ (Abelian.epiIsCokernelOfKernel _ (limit.isLimit _))

end TensorEpimorphisms

section Units

variable {A B D A' B' D' : C}

/-- The original unit and product maps preserve the actual left unit composite. -/
lemma iteratedPair_leftUnit_projection
    (a : A ⟶ A') (b : B ⟶ B') (d₀ : D ⟶ D')
    (e : 𝟙_ C ⟶ A) (e' : 𝟙_ C ⟶ A')
    (f : A ⊗ B ⟶ D) (f' : A' ⊗ B' ⟶ D') (c : D ⟶ B) (c' : D' ⟶ B')
    (he : e ≫ a = e') (hf : f ≫ d₀ = (a ⊗ₘ b) ≫ f') (hc : c ≫ b = d₀ ≫ c') :
    (e ⊗ₘ 𝟙 B) ≫ f ≫ c ≫ b = (𝟙 (𝟙_ C) ⊗ₘ b) ≫ (e' ⊗ₘ 𝟙 B') ≫ f' ≫ c' := by
  have ht : (e ⊗ₘ 𝟙 B) ≫ (a ⊗ₘ b) = (𝟙 (𝟙_ C) ⊗ₘ b) ≫ (e' ⊗ₘ 𝟙 B') := by
    rw [tensorHom_comp_tensorHom, he, tensorHom_comp_tensorHom]
    simp only [Category.id_comp, Category.comp_id]
  rw [hc, ← Category.assoc f d₀ c', hf]
  simp only [Category.assoc]
  rw [← Category.assoc (e ⊗ₘ 𝟙 B) (a ⊗ₘ b) (f' ≫ c'), ht, Category.assoc]

/-- A monomorphic original output comparison retains the actual left unit law. -/
lemma pairing_leftUnit_of_mono_projection
    (a : A ⟶ A') (b : B ⟶ B') (d₀ : D ⟶ D') [Mono b]
    (e : 𝟙_ C ⟶ A) (e' : 𝟙_ C ⟶ A')
    (f : A ⊗ B ⟶ D) (f' : A' ⊗ B' ⟶ D') (c : D ⟶ B) (c' : D' ⟶ B')
    (he : e ≫ a = e') (hf : f ≫ d₀ = (a ⊗ₘ b) ≫ f') (hc : c ≫ b = d₀ ≫ c')
    (hunit : (e' ⊗ₘ 𝟙 B') ≫ f' ≫ c' = (λ_ B').hom) :
    (e ⊗ₘ 𝟙 B) ≫ f ≫ c = (λ_ B).hom := by
  apply (cancel_mono b).mp
  simp only [Category.assoc]
  rw [iteratedPair_leftUnit_projection a b d₀ e e' f f' c c' he hf hc, hunit]
  simpa only [MonoidalCategory.id_tensorHom] using leftUnitor_naturality b

/-- The actual tensor quotient descends the original left unit law. -/
lemma pairing_leftUnit_of_epi_projection
    (a : A ⟶ A') (b : B ⟶ B') (d₀ : D ⟶ D') [Epi (𝟙 (𝟙_ C) ⊗ₘ b)]
    (e : 𝟙_ C ⟶ A) (e' : 𝟙_ C ⟶ A')
    (f : A ⊗ B ⟶ D) (f' : A' ⊗ B' ⟶ D') (c : D ⟶ B) (c' : D' ⟶ B')
    (he : e ≫ a = e') (hf : f ≫ d₀ = (a ⊗ₘ b) ≫ f') (hc : c ≫ b = d₀ ≫ c')
    (hunit : (e ⊗ₘ 𝟙 B) ≫ f ≫ c = (λ_ B).hom) :
    (e' ⊗ₘ 𝟙 B') ≫ f' ≫ c' = (λ_ B').hom := by
  apply (cancel_epi (𝟙 (𝟙_ C) ⊗ₘ b)).mp
  rw [← iteratedPair_leftUnit_projection a b d₀ e e' f f' c c' he hf hc]
  have h : ((e ⊗ₘ 𝟙 B) ≫ f ≫ c) ≫ b = (λ_ B).hom ≫ b := congrArg (fun z => z ≫ b) hunit
  simpa only [Category.assoc, MonoidalCategory.id_tensorHom] using h.trans (leftUnitor_naturality b).symm

/-- The original unit and product maps preserve the actual right unit composite. -/
lemma iteratedPair_rightUnit_projection
    (a : A ⟶ A') (b : B ⟶ B') (d₀ : D ⟶ D')
    (e : 𝟙_ C ⟶ A) (e' : 𝟙_ C ⟶ A')
    (f : B ⊗ A ⟶ D) (f' : B' ⊗ A' ⟶ D') (c : D ⟶ B) (c' : D' ⟶ B')
    (he : e ≫ a = e') (hf : f ≫ d₀ = (b ⊗ₘ a) ≫ f') (hc : c ≫ b = d₀ ≫ c') :
    (𝟙 B ⊗ₘ e) ≫ f ≫ c ≫ b = (b ⊗ₘ 𝟙 (𝟙_ C)) ≫ (𝟙 B' ⊗ₘ e') ≫ f' ≫ c' := by
  have ht : (𝟙 B ⊗ₘ e) ≫ (b ⊗ₘ a) = (b ⊗ₘ 𝟙 (𝟙_ C)) ≫ (𝟙 B' ⊗ₘ e') := by
    rw [tensorHom_comp_tensorHom, he, tensorHom_comp_tensorHom]
    simp only [Category.id_comp, Category.comp_id]
  rw [hc, ← Category.assoc f d₀ c', hf]
  simp only [Category.assoc]
  rw [← Category.assoc (𝟙 B ⊗ₘ e) (b ⊗ₘ a) (f' ≫ c'), ht, Category.assoc]

/-- A monomorphic original output comparison retains the actual right unit law. -/
lemma pairing_rightUnit_of_mono_projection
    (a : A ⟶ A') (b : B ⟶ B') (d₀ : D ⟶ D') [Mono b]
    (e : 𝟙_ C ⟶ A) (e' : 𝟙_ C ⟶ A')
    (f : B ⊗ A ⟶ D) (f' : B' ⊗ A' ⟶ D') (c : D ⟶ B) (c' : D' ⟶ B')
    (he : e ≫ a = e') (hf : f ≫ d₀ = (b ⊗ₘ a) ≫ f') (hc : c ≫ b = d₀ ≫ c')
    (hunit : (𝟙 B' ⊗ₘ e') ≫ f' ≫ c' = (ρ_ B').hom) :
    (𝟙 B ⊗ₘ e) ≫ f ≫ c = (ρ_ B).hom := by
  apply (cancel_mono b).mp
  simp only [Category.assoc]
  rw [iteratedPair_rightUnit_projection a b d₀ e e' f f' c c' he hf hc, hunit]
  simpa only [MonoidalCategory.tensorHom_id] using rightUnitor_naturality b

/-- The actual tensor quotient descends the original right unit law. -/
lemma pairing_rightUnit_of_epi_projection
    (a : A ⟶ A') (b : B ⟶ B') (d₀ : D ⟶ D') [Epi (b ⊗ₘ 𝟙 (𝟙_ C))]
    (e : 𝟙_ C ⟶ A) (e' : 𝟙_ C ⟶ A')
    (f : B ⊗ A ⟶ D) (f' : B' ⊗ A' ⟶ D') (c : D ⟶ B) (c' : D' ⟶ B')
    (he : e ≫ a = e') (hf : f ≫ d₀ = (b ⊗ₘ a) ≫ f') (hc : c ≫ b = d₀ ≫ c')
    (hunit : (𝟙 B ⊗ₘ e) ≫ f ≫ c = (ρ_ B).hom) :
    (𝟙 B' ⊗ₘ e') ≫ f' ≫ c' = (ρ_ B').hom := by
  apply (cancel_epi (b ⊗ₘ 𝟙 (𝟙_ C))).mp
  rw [← iteratedPair_rightUnit_projection a b d₀ e e' f f' c c' he hf hc]
  have h : ((𝟙 B ⊗ₘ e) ≫ f ≫ c) ≫ b = (ρ_ B).hom ≫ b := congrArg (fun z => z ≫ b) hunit
  simpa only [Category.assoc, MonoidalCategory.tensorHom_id] using h.trans (rightUnitor_naturality b).symm

end Units

section SignedSymmetry

variable [Preadditive C] [BraidedCategory C]
  {A B D Q A' B' D' Q' : C}

omit [Preadditive C] in
/-- The actual braiding and swapped original product preserve the output projection. -/
lemma pairing_swap_projection (a : A ⟶ A') (b : B ⟶ B') (q : Q ⟶ Q')
    (g : B ⊗ A ⟶ Q) (g' : B' ⊗ A' ⟶ Q') (hg : g ≫ q = (b ⊗ₘ a) ≫ g') :
    (β_ A B).hom ≫ g ≫ q = (a ⊗ₘ b) ≫ (β_ A' B').hom ≫ g' := by
  rw [hg, ← BraidedCategory.braiding_naturality_assoc]

omit [Preadditive C] [BraidedCategory C] in
/-- The original ordered product and output comparison preserve the actual projection. -/
lemma pairing_ordered_projection (a : A ⟶ A') (b : B ⟶ B') (d₀ : D ⟶ D') (q : Q ⟶ Q')
    (f : A ⊗ B ⟶ D) (f' : A' ⊗ B' ⟶ D') (c : D ⟶ Q) (c' : D' ⟶ Q')
    (hf : f ≫ d₀ = (a ⊗ₘ b) ≫ f') (hc : c ≫ q = d₀ ≫ c') :
    f ≫ c ≫ q = (a ⊗ₘ b) ≫ f' ≫ c' := by
  rw [hc, ← Category.assoc f d₀ c', hf, Category.assoc]

/-- A monomorphic actual output comparison retains the structural signed braiding law. -/
lemma pairing_signedSwap_of_mono_projection
    (a : A ⟶ A') (b : B ⟶ B') (d₀ : D ⟶ D') (q : Q ⟶ Q') [Mono q]
    (f : A ⊗ B ⟶ D) (g : B ⊗ A ⟶ Q) (f' : A' ⊗ B' ⟶ D') (g' : B' ⊗ A' ⟶ Q')
    (c : D ⟶ Q) (c' : D' ⟶ Q') (z : ℤ)
    (hf : f ≫ d₀ = (a ⊗ₘ b) ≫ f') (hg : g ≫ q = (b ⊗ₘ a) ≫ g') (hc : c ≫ q = d₀ ≫ c')
    (hcomm : (β_ A' B').hom ≫ g' = z • (f' ≫ c')) :
    (β_ A B).hom ≫ g = z • (f ≫ c) := by
  apply (cancel_mono q).mp
  simp only [Category.assoc, Preadditive.zsmul_comp]
  rw [pairing_swap_projection a b q g g' hg, pairing_ordered_projection a b d₀ q f f' c c' hf hc,
    hcomm, Preadditive.comp_zsmul]

/-- An epimorphic actual tensor quotient descends the structural signed braiding law. -/
lemma pairing_signedSwap_of_epi_projection
    (a : A ⟶ A') (b : B ⟶ B') (d₀ : D ⟶ D') (q : Q ⟶ Q') [Epi (a ⊗ₘ b)]
    (f : A ⊗ B ⟶ D) (g : B ⊗ A ⟶ Q) (f' : A' ⊗ B' ⟶ D') (g' : B' ⊗ A' ⟶ Q')
    (c : D ⟶ Q) (c' : D' ⟶ Q') (z : ℤ)
    (hf : f ≫ d₀ = (a ⊗ₘ b) ≫ f') (hg : g ≫ q = (b ⊗ₘ a) ≫ g') (hc : c ≫ q = d₀ ≫ c')
    (hcomm : (β_ A B).hom ≫ g = z • (f ≫ c)) :
    (β_ A' B').hom ≫ g' = z • (f' ≫ c') := by
  apply (cancel_epi (a ⊗ₘ b)).mp
  rw [Preadditive.comp_zsmul, ← pairing_swap_projection a b q g g' hg,
    ← pairing_ordered_projection a b d₀ q f f' c c' hf hc]
  simpa only [Category.assoc, Preadditive.zsmul_comp] using congrArg (fun z => z ≫ q) hcomm

end SignedSymmetry

end CategoryTheory
