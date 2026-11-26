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
# Coherence of pairings under compatible comparison maps

In a monoidal category, consider products f : A ⊗ B → X, g : X ⊗ D → L, h : B ⊗ D → Y and k :
A ⊗ Y → Q, with c : L → Q. Their left and right iterated products are L₀ = (f ⊗ id_D) ≫ g ≫ c
and R₀ = α_{A,B,D} ≫ (id_A ⊗ h) ≫ k. Suppose maps a,b,d,x,y,l,q to primed objects satisfy f ≫
x = (a ⊗ b) ≫ f', g ≫ l = (x ⊗ d) ≫ g', h ≫ y = (b ⊗ d) ≫ h', k ≫ q = (a ⊗ y) ≫ k' and c ≫ q =
l ≫ c'. Then L₀ ≫ q = ((a ⊗ b) ⊗ d) ≫ L₀' and the corresponding equation holds for R₀.

A monic output q therefore reflects associativity, while an epic triple tensor input descends
it. The same argument applies to left and right unit laws. In a braided preadditive category,
it also applies to a braiding law β ≫ g = z • (f ≫ c) for any integer z. Tensor epimorphisms
follow from preservation of cokernels by left and right tensor functors in an abelian monoidal
preadditive category. All object and morphism universes remain independent.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {A B D X Y L Q A' B' D' X' Y' L' Q' : C}

/-- Comparison of left-associated iterated pairings.

In a monoidal category, let f : A ⊗ B → X, g : X ⊗ D → L and c : L → Q, with primed
counterparts. If f ≫ x = (a ⊗ b) ≫ f', g ≫ l = (x ⊗ d) ≫ g' and c ≫ q = l ≫ c', then (f ⊗
id_D) ≫ g ≫ c ≫ q = ((a ⊗ b) ⊗ d) ≫ (f' ⊗ id_D') ≫ g' ≫ c'. -/
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

/-- Comparison of right-associated iterated pairings.

In a monoidal category, let h : B ⊗ D → Y and k : A ⊗ Y → Q, with primed counterparts. If h ≫
y = (b ⊗ d) ≫ h' and k ≫ q = (a ⊗ y) ≫ k', then α_{A,B,D} ≫ (id_A ⊗ h) ≫ k ≫ q = ((a ⊗ b) ⊗ d)
≫ α_{A',B',D'} ≫ (id_A' ⊗ h') ≫ k'. The associators preserve the displayed tensor order. -/
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

/-- Associativity reflected by a monic output comparison.

Suppose two monoidal pairing diagrams are related by compatible maps on A,B,D,X,Y,L,Q, with
the five product and output squares commuting. If the output comparison q : Q → Q' is monic
and the primed diagram satisfies (f' ⊗ id_D') ≫ g' ≫ c' = α ≫ (id_A' ⊗ h') ≫ k', then the
corresponding unprimed associativity equation holds. Postcomposition by q identifies the two
iterated products. -/
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

/-- Associativity descended through an epic triple tensor comparison.

For two compatible monoidal pairing diagrams, suppose ((a ⊗ b) ⊗ d) is epic. If (f ⊗ id_D) ≫ g
≫ c = α ≫ (id_A ⊗ h) ≫ k in the source diagram, then the primed diagram is associative. The
five commuting product and output squares identify both primed composites after precomposition
by the same epic triple tensor map. -/
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

/-- Epimorphism of a tensor product of epic maps.

Let C be abelian and monoidal preadditive, with every left and right tensor functor preserving
colimits of parallel pairs. For epimorphisms f : A → B and g : D → F, the tensor map f ⊗ g : A
⊗ D → B ⊗ F is epic. Present f and g as cokernels of their kernels and use tensor preservation
of these cokernels. -/
lemma epi_tensorHom_of_preservesCokernels {A B D F : C} (f : A ⟶ B) (g : D ⟶ F)
    [Epi f] [Epi g] : Epi (f ⊗ₘ g) := by
  let c₁ : CokernelCofork (kernel.ι f) := CokernelCofork.ofπ f (kernel.condition f)
  let c₂ : CokernelCofork (kernel.ι g) := CokernelCofork.ofπ g (kernel.condition g)
  exact CokernelCofork.epi_tensor_π c₁ (Abelian.epiIsCokernelOfKernel _ (limit.isLimit _))
    c₂ (Abelian.epiIsCokernelOfKernel _ (limit.isLimit _))

end TensorEpimorphisms

section Units

variable {A B D A' B' D' : C}

/-- Comparison equation for left unit composites.

In a monoidal category, let e : 𝟙 → A, f : A ⊗ B → D and c : D → B, with primed data. If e ≫ a
= e', f ≫ d = (a ⊗ b) ≫ f' and c ≫ b = d ≫ c', then (e ⊗ id_B) ≫ f ≫ c ≫ b = (id_𝟙 ⊗ b) ≫ (e'
⊗ id_B') ≫ f' ≫ c'. -/
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

/-- Left unit law reflected by a monic output map.

For compatible unit and pairing maps e,f,c and e',f',c' in a monoidal category, assume b : B →
B' is monic. If the primed left unit composite is (e' ⊗ id_B') ≫ f' ≫ c' = λ_{B'}, then (e ⊗
id_B) ≫ f ≫ c = λ_B. The unit map, product map and output map squares commute, and naturality
of the left unitor gives the reflection. -/
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

/-- Left unit law descended through an epic unit tensor map.

For compatible unit and pairing maps in a monoidal category, assume id_𝟙 ⊗ b is epic. If (e ⊗
id_B) ≫ f ≫ c = λ_B, then (e' ⊗ id_B') ≫ f' ≫ c' = λ_{B'}. The compatible unit, product and
output squares compare the two composites after the epic map id_𝟙 ⊗ b. -/
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

/-- Comparison equation for right unit composites.

In a monoidal category, let e : 𝟙 → A, f : B ⊗ A → D and c : D → B, with primed data. If e ≫ a
= e', f ≫ d = (b ⊗ a) ≫ f' and c ≫ b = d ≫ c', then (id_B ⊗ e) ≫ f ≫ c ≫ b = (b ⊗ id_𝟙) ≫
(id_B' ⊗ e') ≫ f' ≫ c'. -/
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

/-- Right unit law reflected by a monic output map.

For compatible unit and pairing maps e,f,c and e',f',c' in a monoidal category, assume b : B →
B' is monic. If (id_B' ⊗ e') ≫ f' ≫ c' = ρ_{B'}, then (id_B ⊗ e) ≫ f ≫ c = ρ_B.
Postcomposition by b compares these right unit composites by naturality of the right unitor. -/
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

/-- Right unit law descended through an epic unit tensor map.

For compatible unit and pairing maps in a monoidal category, assume b ⊗ id_𝟙 is epic. If (id_B
⊗ e) ≫ f ≫ c = ρ_B, then (id_B' ⊗ e') ≫ f' ≫ c' = ρ_{B'}. The compatible unit, product and
output squares identify the composites after precomposition by b ⊗ id_𝟙. -/
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
/-- Comparison of a pairing after braiding its inputs.

In a braided monoidal category, let g : B ⊗ A → Q and g' : B' ⊗ A' → Q' satisfy g ≫ q = (b ⊗
a) ≫ g'. Then β_{A,B} ≫ g ≫ q = (a ⊗ b) ≫ β_{A',B'} ≫ g'. This is naturality of the braiding
on the two input maps. -/
lemma pairing_swap_projection (a : A ⟶ A') (b : B ⟶ B') (q : Q ⟶ Q')
    (g : B ⊗ A ⟶ Q) (g' : B' ⊗ A' ⟶ Q') (hg : g ≫ q = (b ⊗ₘ a) ≫ g') :
    (β_ A B).hom ≫ g ≫ q = (a ⊗ₘ b) ≫ (β_ A' B').hom ≫ g' := by
  rw [hg, ← BraidedCategory.braiding_naturality_assoc]

omit [Preadditive C] [BraidedCategory C] in
/-- Comparison of an ordered pairing and its output map.

In a monoidal category, if f : A ⊗ B → D and c : D → Q have compatible primed maps with f ≫ d
= (a ⊗ b) ≫ f' and c ≫ q = d ≫ c', then f ≫ c ≫ q = (a ⊗ b) ≫ f' ≫ c'. -/
lemma pairing_ordered_projection (a : A ⟶ A') (b : B ⟶ B') (d₀ : D ⟶ D') (q : Q ⟶ Q')
    (f : A ⊗ B ⟶ D) (f' : A' ⊗ B' ⟶ D') (c : D ⟶ Q) (c' : D' ⟶ Q')
    (hf : f ≫ d₀ = (a ⊗ₘ b) ≫ f') (hc : c ≫ q = d₀ ≫ c') :
    f ≫ c ≫ q = (a ⊗ₘ b) ≫ f' ≫ c' := by
  rw [hc, ← Category.assoc f d₀ c', hf, Category.assoc]

/-- Integer braiding law reflected by a monic output comparison.

In a braided preadditive monoidal category, let ordered and swapped pairings satisfy the
compatible product and output squares, and suppose q : Q → Q' is monic. For any z : ℤ, the
primed equation β_{A',B'} ≫ g' = z • (f' ≫ c') implies β_{A,B} ≫ g = z • (f ≫ c). Cancellation
preserves the same integer scalar. -/
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

/-- Integer braiding law descended through an epic tensor comparison.

In a braided preadditive monoidal category, suppose the ordered and swapped pairings satisfy
the compatible product and output squares and a ⊗ b is epic. For any z : ℤ, the equation
β_{A,B} ≫ g = z • (f ≫ c) implies β_{A',B'} ≫ g' = z • (f' ≫ c'). The sign or integer
coefficient z is unchanged. -/
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
