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

public import MathlibExt.Algebra.Homology.PartialTotalNested

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

example (p' : ℕ) :
    (ComplexShape.embeddingDownNatInitialSegment 0).RangeLE
      (ComplexShape.embeddingDownNatInitialSegment p') :=
  ComplexShape.embeddingDownNatInitialSegment_rangeLE (Nat.zero_le p')

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]

local instance : HasFiniteBiproducts C :=
  HasFiniteBiproducts.of_hasFiniteCoproducts

variable (B : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ))

example {p p' : ℕ} (h : p ≤ p') :
    B.firstStupidTrunc p ⟶ B.firstStupidTrunc p' :=
  B.firstStupidTruncMap h

example {p p' : ℕ} (h : p ≤ p') :
    B.partialTotal p ⟶ B.partialTotal p' :=
  B.partialTotalMap h

example {p p' : ℕ} (h : p ≤ p')
    (i : Fin (p + 1)) (j n : ℕ) (hn : i.1 + j = n) :
    (B.firstStupidTrunc p).ιTotal (ComplexShape.down ℕ) i.1 j n hn ≫
        (B.partialTotalMap h).f n =
      ((B.stupidTruncXIso
          (ComplexShape.embeddingDownNatInitialSegment p) rfl).hom.f j ≫
        (B.stupidTruncXIso
          (ComplexShape.embeddingDownNatInitialSegment p')
          (ComplexShape.downNatInitialSegmentEmbedding_f_embedding_f
            h i)).inv.f j) ≫
        (B.firstStupidTrunc p').ιTotal
          (ComplexShape.down ℕ) i.1 j n hn :=
  B.ιTotal_partialTotalMap h i j n hn

example (p' : ℕ) :
    (B.firstStupidTrunc 0).ιTotal (ComplexShape.down ℕ) 0 0 0 rfl ≫
        (B.partialTotalMap (Nat.zero_le p')).f 0 =
      ((B.stupidTruncXIso
          (ComplexShape.embeddingDownNatInitialSegment 0) rfl).hom.f 0 ≫
        (B.stupidTruncXIso
          (ComplexShape.embeddingDownNatInitialSegment p')
          (ComplexShape.downNatInitialSegmentEmbedding_f_embedding_f
            (Nat.zero_le p') (0 : Fin 1))).inv.f 0) ≫
        (B.firstStupidTrunc p').ιTotal
          (ComplexShape.down ℕ) 0 0 0 rfl :=
  B.ιTotal_partialTotalMap (Nat.zero_le p') (0 : Fin 1) 0 0 rfl

example {p p' : ℕ} (h : p ≤ p') :
    B.partialTotalMap h ≫ B.partialTotalι p' = B.partialTotalι p :=
  B.partialTotalMap_comp_partialTotalι h

example (p : ℕ) :
    B.partialTotalMap (le_refl p) = 𝟙 _ :=
  B.partialTotalMap_refl p

example {p p' p'' : ℕ} (h : p ≤ p') (h' : p' ≤ p'') :
    B.partialTotalMap h ≫ B.partialTotalMap h' =
      B.partialTotalMap (h.trans h') :=
  B.partialTotalMap_comp h h'

example {p p' : ℕ} (h : p ≤ p') :
    B.partialTotalMap (le_refl p) ≫ B.partialTotalMap h =
      B.partialTotalMap ((le_refl p).trans h) :=
  B.partialTotalMap_comp (le_refl p) h

example {p p' : ℕ} (h : p ≤ p') (n : ℕ) :
    Mono ((B.partialTotalMap h).f n) :=
  inferInstance

example {p p' : ℕ} (h : p ≤ p') :
    Mono (B.partialTotalMap h) :=
  inferInstance

example (p n : ℕ) :
    Mono ((B.partialTotalMap (le_refl p)).f n) :=
  inferInstance

example (p : ℕ) :
    Mono (B.partialTotalMap (le_refl p)) :=
  inferInstance

example
    {B' : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (φ : B ⟶ B') (p : ℕ) :
    B.partialTotal p ⟶ B'.partialTotal p :=
  B.partialTotalHom φ p

example
    {B' : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (φ : B ⟶ B') (p : ℕ)
    (i : Fin (p + 1)) (j n : ℕ) (hn : i.1 + j = n) :
    (B.firstStupidTrunc p).ιTotal (ComplexShape.down ℕ) i.1 j n hn ≫
        (B.partialTotalHom φ p).f n =
      (((HomologicalComplex.stupidTruncMap φ
        (ComplexShape.embeddingDownNatInitialSegment p)).f i.1).f j) ≫
        (B'.firstStupidTrunc p).ιTotal
          (ComplexShape.down ℕ) i.1 j n hn :=
  B.ιTotal_partialTotalHom φ p i j n hn

example
    {B' : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (φ : B ⟶ B') (p : ℕ) :
    B.partialTotalHom φ p ≫ B'.partialTotalι p =
      B.partialTotalι p ≫
        HomologicalComplex₂.total.map φ (ComplexShape.down ℕ) :=
  B.partialTotalHom_ι_naturality φ p

example
    {B' : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (φ : B ⟶ B')
    {p p' : ℕ} (h : p ≤ p') :
    B.partialTotalHom φ p ≫ B'.partialTotalMap h =
      B.partialTotalMap h ≫ B.partialTotalHom φ p' :=
  B.partialTotalMap_naturality φ h

example {p p' : ℕ} (h : p ≤ p') :
    B.partialTotalHom (𝟙 B) p ≫ B.partialTotalMap h =
      B.partialTotalMap h ≫ B.partialTotalHom (𝟙 B) p' :=
  B.partialTotalMap_naturality (𝟙 B) h

end HomologicalComplex₂

end
