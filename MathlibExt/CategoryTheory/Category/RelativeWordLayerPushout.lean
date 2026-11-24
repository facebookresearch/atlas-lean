/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Category.RelativeWordLayer
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# The actual pointwise original relative-word layer pushout

The next normalized layer is the pushout of the previous layer and all
raw words with one more target letter, along the actual raw words whose
new-letter count drops. The universal map is constructed by the whole
original word length and both factors are proved using the genuine
positive-stratum normalization/forgetting inverse.
-/

noncomputable section
universe u v wA wB
open CategoryTheory Limits

namespace CategoryTheory.RelativeGenerators
open RelativeWords

variable {C : Type u} [Category.{v} C]
  {A : C → C → Type wA} {B : C → C → Type wB}
  (i : ∀ {a b : C}, A a b → B a b) (φ : ∀ {a b : C}, A a b → (a ⟶ b))

/-- The actual universal next-layer function chooses the same original low word or its
positive raw representative. -/
def layerDesc (a b : C) (n : ℕ) {Z : Type (max u v wB)}
    (L : Layer (A := A) (B := B) (@i) a b n ⟶ Z) (R : RawLayer (B := B) a b n ⟶ Z) :
    Layer (A := A) (B := B) (@i) a b (n + 1) ⟶ Z := by
  classical
  exact ↾fun p => if hp : p.val.length ≤ n then L ⟨p.val, hp⟩ else
    R ⟨forget (A := A) (B := B) (@i) p.val, by
      rw [length_forget]
      have h := p.property
      omega⟩

/-- The entire original previous layer factors through the actual next-layer universal map. -/
theorem layerDesc_left (a b : C) (n : ℕ) {Z : Type (max u v wB)}
    (L : Layer (A := A) (B := B) (@i) a b n ⟶ Z) (R : RawLayer (B := B) a b n ⟶ Z) :
    layerInclude (A := A) (B := B) (@i) a b n ≫ layerDesc (A := A) (B := B) (@i) a b n L R = L := by
  ext p
  simp only [TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply, TypeCat.ofHom_apply, layerInclude,
    layerDesc, dite_eq_left p.property]

/-- Every actual raw word factors, using the original boundary condition or its actual
positive representative. -/
theorem layerDesc_right (a b : C) (n : ℕ) {Z : Type (max u v wB)}
    (L : Layer (A := A) (B := B) (@i) a b n ⟶ Z) (R : RawLayer (B := B) a b n ⟶ Z)
    (h : boundaryNormalize (A := A) (B := B) (@i) (@φ) a b n ≫ L =
      boundaryInclude (A := A) (B := B) (@i) a b n ≫ R) :
    rawNormalize (A := A) (B := B) (@i) (@φ) a b n ≫
      layerDesc (A := A) (B := B) (@i) a b n L R = R := by
  classical
  ext p
  by_cases hp : (normalize (A := A) (B := B) (@i) (@φ) p.val).length ≤ n
  · have hc : count (A := A) (B := B) (@i) p.val ≤ n := by
      rwa [length_normalize_eq_count] at hp
    have hh := congrArg (fun f => f ⟨p.val, p.property, hc⟩) h
    simpa only [TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply, TypeCat.ofHom_apply,
      rawNormalize,
      layerDesc, boundaryNormalize, boundaryInclude, dite_eq_left hp] using hh
  · have hc := count_le_length (A := A) (B := B) (@i) p.val
    have hn := length_normalize_eq_count (A := A) (B := B) (@i) (@φ) p.val
    have hpLen := p.property
    have hpos : count (A := A) (B := B) (@i) p.val = p.val.length := by omega
    have hi := forget_normalize_of_positive (A := A) (B := B) (@i) (@φ) p.val hpos
    simp only [TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply, TypeCat.ofHom_apply,
      rawNormalize,
      layerDesc, dite_eq_right hp]
    apply congrArg R
    apply Subtype.ext
    exact hi

/-- The actual whole next-layer map is uniquely determined by its two original structural
factors. -/
theorem layerDesc_unique (a b : C) (n : ℕ) {Z : Type (max u v wB)}
    (L : Layer (A := A) (B := B) (@i) a b n ⟶ Z) (R : RawLayer (B := B) a b n ⟶ Z)
    (H : Layer (A := A) (B := B) (@i) a b (n + 1) ⟶ Z)
    (hL : layerInclude (A := A) (B := B) (@i) a b n ≫ H = L)
    (hR : rawNormalize (A := A) (B := B) (@i) (@φ) a b n ≫ H = R) :
    H = layerDesc (A := A) (B := B) (@i) a b n L R := by
  classical
  ext p
  by_cases hp : p.val.length ≤ n
  · have hh := congrArg (fun f => f ⟨p.val, hp⟩) hL
    simpa only [TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply, TypeCat.ofHom_apply,
      layerInclude,
      layerDesc, dite_eq_left hp] using hh
  · have hk : (forget (A := A) (B := B) (@i) p.val).length = n + 1 := by
      rw [length_forget]
      have h := p.property
      omega
    have hh := congrArg (fun f => f ⟨forget (A := A) (B := B) (@i) p.val, hk⟩) hR
    have hi := normalize_forget (A := A) (B := B) (@i) (@φ) p.val
    simp only [CategoryTheory.comp_apply, TypeCat.ofHom_apply, rawNormalize] at hh
    have he : (⟨normalize (A := A) (B := B) (@i) (@φ)
      (forget (A := A) (B := B) (@i) p.val), by
        exact (length_normalize_le (A := A) (B := B) (@i) (@φ)
          (forget (A := A) (B := B) (@i) p.val)).trans_eq hk⟩ : Layer (A := A) (B :=
            B) (@i) a b (n + 1)) = p :=
      Subtype.ext hi
    simpa only [TypeCat.Fun.toFun_apply, CategoryTheory.comp_apply, TypeCat.ofHom_apply, he,
      layerDesc,
      dite_eq_right hp] using hh

/-- The actual pointwise original normalized layer square is a genuine pushout. -/
theorem layerIsPushout (a b : C) (n : ℕ) :
    IsPushout (boundaryNormalize (A := A) (B := B) (@i) (@φ) a b n)
      (boundaryInclude (A := A) (B := B) (@i) a b n)
      (layerInclude (A := A) (B := B) (@i) a b n)
      (rawNormalize (A := A) (B := B) (@i) (@φ) a b n) := by
  let hc : IsColimit (PushoutCocone.mk
      (layerInclude (A := A) (B := B) (@i) a b n)
      (rawNormalize (A := A) (B := B) (@i) (@φ) a b n)
      (layer_square (A := A) (B := B) (@i) (@φ) a b n)) :=
    PushoutCocone.IsColimit.mk (layer_square (A := A) (B := B) (@i) (@φ) a b n)
    (fun s => layerDesc (A := A) (B := B) (@i) a b n s.inl s.inr)
    (fun s => layerDesc_left (A := A) (B := B) (@i) a b n s.inl s.inr)
    (fun s => layerDesc_right (A := A) (B := B) (@i) (@φ) a b n s.inl s.inr s.condition)
    (fun s H hL hR => layerDesc_unique (A := A) (B := B) (@i) (@φ) a b n s.inl s.inr H hL hR)
  exact IsPushout.of_isColimit hc

end CategoryTheory.RelativeGenerators
