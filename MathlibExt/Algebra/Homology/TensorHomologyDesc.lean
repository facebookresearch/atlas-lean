/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import MathlibExt.CategoryTheory.Monoidal.TensorCokernel

/-!
# Tensor descent from cycles to homology

This file specializes tensor descent through chosen cokernel presentations to the presentation of
homology as cycles modulo boundaries. It is independent of the shapes and degree arithmetic of the
two complexes.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe v u w₁ w₂

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {ι₁ : Type w₁} {ι₂ : Type w₂}
  {c₁ : ComplexShape ι₁} {c₂ : ComplexShape ι₂}

/--
The homology projection, packaged as the cokernel cofork of the boundary-to-cycles map at a chosen
predecessor.
-/
noncomputable def homologyCofork (K : HomologicalComplex C c₁)
    (i j : ι₁) (_h : c₁.prev j = i) [K.HasHomology j] :
    CokernelCofork (K.toCycles i j) :=
  CokernelCofork.ofπ (K.homologyπ j) (K.toCycles_comp_homologyπ i j)

@[simp]
lemma homologyCofork_pt (K : HomologicalComplex C c₁)
    (i j : ι₁) (hij : c₁.prev j = i) [K.HasHomology j] :
    (homologyCofork K i j hij).pt = K.homology j :=
  rfl

@[simp]
lemma homologyCofork_π (K : HomologicalComplex C c₁)
    (i j : ι₁) (hij : c₁.prev j = i) [K.HasHomology j] :
    (homologyCofork K i j hij).π = K.homologyπ j :=
  rfl

/-- The homology cofork is a colimit cokernel cofork. -/
noncomputable def homologyCoforkIsColimit (K : HomologicalComplex C c₁)
    (i j : ι₁) (h : c₁.prev j = i) [K.HasHomology j] :
    IsColimit (homologyCofork K i j h) :=
  K.homologyIsCokernel i j h

variable [MonoidalCategory C] [MonoidalPreadditive C]

variable (K₁ : HomologicalComplex C c₁) (i₁ j₁ : ι₁)
  (h₁ : c₁.prev j₁ = i₁) [K₁.HasHomology j₁]
  (K₂ : HomologicalComplex C c₂) (i₂ j₂ : ι₂)
  (h₂ : c₂.prev j₂ = i₂) [K₂.HasHomology j₂]
  [PreservesColimit (parallelPair (K₂.toCycles i₂ j₂) 0)
    (tensorLeft (K₁.homology j₁))]
  [PreservesColimit (parallelPair (K₁.toCycles i₁ j₁) 0)
    (tensorRight (K₂.cycles j₂))]

include i₁ h₁ i₂ h₂ in
/-- Morphisms out of a tensor product of homology objects are determined by
their composites with the tensor of the homology projections. -/
lemma tensor_homologyπ_hom_ext {Z : C}
    {f g : K₁.homology j₁ ⊗ K₂.homology j₂ ⟶ Z}
    (w : (K₁.homologyπ j₁ ⊗ₘ K₂.homologyπ j₂) ≫ f =
      (K₁.homologyπ j₁ ⊗ₘ K₂.homologyπ j₂) ≫ g) : f = g := by
  let _ : PreservesColimit (parallelPair (K₂.toCycles i₂ j₂) 0)
      (tensorLeft (homologyCofork K₁ i₁ j₁ h₁).pt) := by
    change PreservesColimit _ (tensorLeft (K₁.homology j₁))
    infer_instance
  exact CokernelCofork.tensor_hom_ext
    (homologyCofork K₁ i₁ j₁ h₁)
    (homologyCoforkIsColimit K₁ i₁ j₁ h₁)
    (homologyCofork K₂ i₂ j₂ h₂)
    (homologyCoforkIsColimit K₂ i₂ j₂ h₂) w

variable [HasBinaryCoproduct (K₁.X i₁ ⊗ K₂.cycles j₂)
    (K₁.cycles j₁ ⊗ K₂.X i₂)]
  [PreservesColimit (parallelPair (K₁.toCycles i₁ j₁) 0)
    (tensorRight (K₂.X i₂))]

include h₁ h₂ in
/-- Descend a morphism on two cycle objects through the tensor product of the
corresponding homology objects. -/
noncomputable def tensorHomologyDesc {Z : C}
    (k : K₁.cycles j₁ ⊗ K₂.cycles j₂ ⟶ Z)
    (hk : coprod.desc (K₁.toCycles i₁ j₁ ▷ K₂.cycles j₂)
      (K₁.cycles j₁ ◁ K₂.toCycles i₂ j₂) ≫ k = 0) :
    K₁.homology j₁ ⊗ K₂.homology j₂ ⟶ Z := by
  let _ : PreservesColimit (parallelPair (K₂.toCycles i₂ j₂) 0)
      (tensorLeft (homologyCofork K₁ i₁ j₁ h₁).pt) := by
    change PreservesColimit _ (tensorLeft (K₁.homology j₁))
    infer_instance
  exact CokernelCofork.tensorDesc
    (homologyCofork K₁ i₁ j₁ h₁)
    (homologyCoforkIsColimit K₁ i₁ j₁ h₁)
    (homologyCofork K₂ i₂ j₂ h₂)
    (homologyCoforkIsColimit K₂ i₂ j₂ h₂) k hk

include h₁ h₂ in
/-- The tensor of the homology projections followed by
`tensorHomologyDesc` is the original map on cycles. -/
@[reassoc (attr := simp)]
lemma tensor_homologyπ_comp_tensorHomologyDesc {Z : C}
    (k : K₁.cycles j₁ ⊗ K₂.cycles j₂ ⟶ Z)
    (hk : coprod.desc (K₁.toCycles i₁ j₁ ▷ K₂.cycles j₂)
      (K₁.cycles j₁ ◁ K₂.toCycles i₂ j₂) ≫ k = 0) :
    (K₁.homologyπ j₁ ⊗ₘ K₂.homologyπ j₂) ≫
        tensorHomologyDesc K₁ i₁ j₁ h₁ K₂ i₂ j₂ h₂ k hk = k := by
  let _ : PreservesColimit (parallelPair (K₂.toCycles i₂ j₂) 0)
      (tensorLeft (homologyCofork K₁ i₁ j₁ h₁).pt) := by
    change PreservesColimit _ (tensorLeft (K₁.homology j₁))
    infer_instance
  exact CokernelCofork.tensor_π_desc
    (homologyCofork K₁ i₁ j₁ h₁)
    (homologyCoforkIsColimit K₁ i₁ j₁ h₁)
    (homologyCofork K₂ i₂ j₂ h₂)
    (homologyCoforkIsColimit K₂ i₂ j₂ h₂) k hk

include h₁ h₂ in
/-- Naturality of tensor homology descent under maps of both complexes and a
map of targets. -/
lemma tensorHomologyDesc_naturality
    {L₁ : HomologicalComplex C c₁} {L₂ : HomologicalComplex C c₂}
    [L₁.HasHomology j₁] [L₂.HasHomology j₂]
    [HasBinaryCoproduct (L₁.X i₁ ⊗ L₂.cycles j₂)
      (L₁.cycles j₁ ⊗ L₂.X i₂)]
    [PreservesColimit (parallelPair (L₂.toCycles i₂ j₂) 0)
      (tensorLeft (L₁.homology j₁))]
    [PreservesColimit (parallelPair (L₁.toCycles i₁ j₁) 0)
      (tensorRight (L₂.cycles j₂))]
    [PreservesColimit (parallelPair (L₁.toCycles i₁ j₁) 0)
      (tensorRight (L₂.X i₂))]
    (f₁ : K₁ ⟶ L₁) (f₂ : K₂ ⟶ L₂)
    {Z Z' : C}
    (k : K₁.cycles j₁ ⊗ K₂.cycles j₂ ⟶ Z)
    (hk : coprod.desc (K₁.toCycles i₁ j₁ ▷ K₂.cycles j₂)
      (K₁.cycles j₁ ◁ K₂.toCycles i₂ j₂) ≫ k = 0)
    (k' : L₁.cycles j₁ ⊗ L₂.cycles j₂ ⟶ Z')
    (hk' : coprod.desc (L₁.toCycles i₁ j₁ ▷ L₂.cycles j₂)
      (L₁.cycles j₁ ◁ L₂.toCycles i₂ j₂) ≫ k' = 0)
    (z : Z ⟶ Z')
    (hz : (K₁.cyclesMap f₁ j₁ ⊗ₘ K₂.cyclesMap f₂ j₂) ≫ k' =
      k ≫ z) :
    (K₁.homologyMap f₁ j₁ ⊗ₘ K₂.homologyMap f₂ j₂) ≫
        tensorHomologyDesc L₁ i₁ j₁ h₁ L₂ i₂ j₂ h₂ k' hk' =
      tensorHomologyDesc K₁ i₁ j₁ h₁ K₂ i₂ j₂ h₂ k hk ≫ z := by
  let _ : PreservesColimit (parallelPair (K₂.toCycles i₂ j₂) 0)
      (tensorLeft (homologyCofork K₁ i₁ j₁ h₁).pt) := by
    change PreservesColimit _ (tensorLeft (K₁.homology j₁))
    infer_instance
  let _ : PreservesColimit (parallelPair (L₂.toCycles i₂ j₂) 0)
      (tensorLeft (homologyCofork L₁ i₁ j₁ h₁).pt) := by
    change PreservesColimit _ (tensorLeft (L₁.homology j₁))
    infer_instance
  exact CokernelCofork.tensorDesc_naturality
    (homologyCofork K₁ i₁ j₁ h₁)
    (homologyCoforkIsColimit K₁ i₁ j₁ h₁)
    (homologyCofork K₂ i₂ j₂ h₂)
    (homologyCoforkIsColimit K₂ i₂ j₂ h₂)
    (homologyCofork L₁ i₁ j₁ h₁)
    (homologyCoforkIsColimit L₁ i₁ j₁ h₁)
    (homologyCofork L₂ i₂ j₂ h₂)
    (homologyCoforkIsColimit L₂ i₂ j₂ h₂)
    (K₁.cyclesMap f₁ j₁) (K₂.cyclesMap f₂ j₂)
    (K₁.homologyMap f₁ j₁) (K₂.homologyMap f₂ j₂)
    (K₁.homologyπ_naturality f₁ j₁)
    (K₂.homologyπ_naturality f₂ j₂)
    k hk k' hk' z hz

end HomologicalComplex
