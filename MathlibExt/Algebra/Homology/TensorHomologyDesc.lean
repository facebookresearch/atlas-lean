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

In a preadditive category, H_j(K) is the cokernel of the incoming boundary map K_i → Z_j(K), for
the predecessor i of j. In a preadditive monoidal category with bilinear tensor product, a map
Z_j₁(K₁) ⊗ Z_j₂(K₂) → Z that kills boundaries in either factor descends to H_j₁(K₁) ⊗ H_j₂(K₂) →
Z under the specified cokernel-preservation and coproduct hypotheses. The descended map is
unique and natural in both complexes and the target, with no relation required between their
index types or complex shapes.
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
/-- Let C be a preadditive monoidal category with bilinear tensor product. Let K₁ and K₂ have
arbitrary, independently indexed complex shapes c₁,c₂, with homology at j₁,j₂ and predecessor
indices i₁ = c₁.prev(j₁), i₂ = c₂.prev(j₂). Write Z₁,Z₂ and H₁,H₂ for their cycles and homology,
and β₁ : K₁,i₁ → Z₁, β₂ : K₂,i₂ → Z₂ for the incoming boundary maps. Assume right tensoring by
Z₂ preserves the cokernel coequalizer of β₁ and left tensoring by H₁ preserves that of β₂. For
maps f,g : H₁ ⊗ H₂ → Z, equality (π₁ ⊗ π₂) ≫ f = (π₁ ⊗ π₂) ≫ g implies f = g. Only these two
cokernel-preservation hypotheses are needed for this uniqueness statement. -/
lemma tensor_homologyπ_hom_ext {Z : C}
    {f g : K₁.homology j₁ ⊗ K₂.homology j₂ ⟶ Z}
    (w : (K₁.homologyπ j₁ ⊗ₘ K₂.homologyπ j₂) ≫ f =
      (K₁.homologyπ j₁ ⊗ₘ K₂.homologyπ j₂) ≫ g) : f = g := by
  let _ : PreservesColimit (parallelPair (K₂.toCycles i₂ j₂) 0)
      (tensorLeft
        (CokernelCofork.ofπ (K₁.homologyπ j₁)
          (K₁.toCycles_comp_homologyπ i₁ j₁)).pt) := by
    change PreservesColimit _ (tensorLeft (K₁.homology j₁))
    infer_instance
  exact CokernelCofork.tensor_hom_ext
    (CokernelCofork.ofπ (K₁.homologyπ j₁) (K₁.toCycles_comp_homologyπ i₁ j₁))
    (K₁.homologyIsCokernel i₁ j₁ h₁)
    (CokernelCofork.ofπ (K₂.homologyπ j₂) (K₂.toCycles_comp_homologyπ i₂ j₂))
    (K₂.homologyIsCokernel i₂ j₂ h₂) w

variable [HasBinaryCoproduct (K₁.X i₁ ⊗ K₂.cycles j₂)
    (K₁.cycles j₁ ⊗ K₂.X i₂)]
  [PreservesColimit (parallelPair (K₁.toCycles i₁ j₁) 0)
    (tensorRight (K₂.X i₂))]

include h₁ h₂ in
/-- Let C be a preadditive monoidal category with bilinear tensor product. Let K₁ and K₂ have
arbitrary, independently indexed complex shapes c₁,c₂, with homology at j₁,j₂ and predecessor
indices i₁ = c₁.prev(j₁), i₂ = c₂.prev(j₂). Write Z₁,Z₂ and H₁,H₂ for their cycles and homology,
and β₁ : K₁,i₁ → Z₁, β₂ : K₂,i₂ → Z₂ for the incoming boundary maps. Assume right tensoring by
Z₂ preserves the cokernel coequalizer of β₁ and left tensoring by H₁ preserves that of β₂.
Assume also that the coproduct of K₁,i₁ ⊗ Z₂ and Z₁ ⊗ K₂,i₂ exists and right tensoring by K₂,i₂
preserves the cokernel coequalizer of β₁. If k : Z₁ ⊗ Z₂ → Z kills the map from the coproduct
whose components are β₁ ⊗ id_Z₂ and id_Z₁ ⊗ β₂, then tensorHomologyDesc k is the unique map H₁ ⊗
H₂ → Z satisfying (π₁ ⊗ π₂) ≫ tensorHomologyDesc k = k. -/
noncomputable def tensorHomologyDesc {Z : C}
    (k : K₁.cycles j₁ ⊗ K₂.cycles j₂ ⟶ Z)
    (hk : coprod.desc (K₁.toCycles i₁ j₁ ▷ K₂.cycles j₂)
      (K₁.cycles j₁ ◁ K₂.toCycles i₂ j₂) ≫ k = 0) :
    K₁.homology j₁ ⊗ K₂.homology j₂ ⟶ Z := by
  let _ : PreservesColimit (parallelPair (K₂.toCycles i₂ j₂) 0)
      (tensorLeft
        (CokernelCofork.ofπ (K₁.homologyπ j₁)
          (K₁.toCycles_comp_homologyπ i₁ j₁)).pt) := by
    change PreservesColimit _ (tensorLeft (K₁.homology j₁))
    infer_instance
  exact (CokernelCofork.isColimitTensor
    (K₁.homologyIsCokernel i₁ j₁ h₁) (K₂.homologyIsCokernel i₂ j₂ h₂)).desc
      (CokernelCofork.ofπ k hk)

include h₁ h₂ in
/-- Let C be a preadditive monoidal category with bilinear tensor product. Let K₁ and K₂ have
arbitrary, independently indexed complex shapes c₁,c₂, with homology at j₁,j₂ and predecessor
indices i₁ = c₁.prev(j₁), i₂ = c₂.prev(j₂). Write Z₁,Z₂ and H₁,H₂ for their cycles and homology,
and β₁ : K₁,i₁ → Z₁, β₂ : K₂,i₂ → Z₂ for the incoming boundary maps. Assume right tensoring by
Z₂ preserves the cokernel coequalizer of β₁ and left tensoring by H₁ preserves that of β₂.
Assume also that the coproduct of K₁,i₁ ⊗ Z₂ and Z₁ ⊗ K₂,i₂ exists and right tensoring by K₂,i₂
preserves the cokernel coequalizer of β₁. For k : Z₁ ⊗ Z₂ → Z vanishing on both tensor boundary
components, the descended map satisfies (π₁ ⊗ π₂) ≫ tensorHomologyDesc k = k. -/
@[reassoc (attr := simp)]
lemma tensor_homologyπ_comp_tensorHomologyDesc {Z : C}
    (k : K₁.cycles j₁ ⊗ K₂.cycles j₂ ⟶ Z)
    (hk : coprod.desc (K₁.toCycles i₁ j₁ ▷ K₂.cycles j₂)
      (K₁.cycles j₁ ◁ K₂.toCycles i₂ j₂) ≫ k = 0) :
    (K₁.homologyπ j₁ ⊗ₘ K₂.homologyπ j₂) ≫
        tensorHomologyDesc K₁ i₁ j₁ h₁ K₂ i₂ j₂ h₂ k hk = k := by
  let _ : PreservesColimit (parallelPair (K₂.toCycles i₂ j₂) 0)
      (tensorLeft
        (CokernelCofork.ofπ (K₁.homologyπ j₁)
          (K₁.toCycles_comp_homologyπ i₁ j₁)).pt) := by
    change PreservesColimit _ (tensorLeft (K₁.homology j₁))
    infer_instance
  exact (CokernelCofork.isColimitTensor
    (K₁.homologyIsCokernel i₁ j₁ h₁) (K₂.homologyIsCokernel i₂ j₂ h₂)).fac
      (CokernelCofork.ofπ k hk) WalkingParallelPair.one

include h₁ h₂ in
/-- Let C be a preadditive monoidal category with bilinear tensor product. Let K₁ and K₂ have
arbitrary, independently indexed complex shapes c₁,c₂, with homology at j₁,j₂ and predecessor
indices i₁ = c₁.prev(j₁), i₂ = c₂.prev(j₂). Write Z₁,Z₂ and H₁,H₂ for their cycles and homology,
and β₁ : K₁,i₁ → Z₁, β₂ : K₂,i₂ → Z₂ for the incoming boundary maps. Assume right tensoring by
Z₂ preserves the cokernel coequalizer of β₁ and left tensoring by H₁ preserves that of β₂.
Assume also that the coproduct of K₁,i₁ ⊗ Z₂ and Z₁ ⊗ K₂,i₂ exists and right tensoring by K₂,i₂
preserves the cokernel coequalizer of β₁. Let f₁ : K₁ → L₁ and f₂ : K₂ → L₂ preserve the
respective shapes, with homology for L₁,L₂ in j₁,j₂ and the same coproduct and three
cokernel-preservation hypotheses for their incoming boundary maps. Let k and k′ be maps on the
respective cycle tensors that kill both boundary components, and z : Z → Z′. If (Z_j₁(f₁) ⊗
Z_j₂(f₂)) ≫ k′ = k ≫ z, then (H_j₁(f₁) ⊗ H_j₂(f₂)) ≫ desc(k′) = desc(k) ≫ z. -/
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
      (tensorLeft
        (CokernelCofork.ofπ (K₁.homologyπ j₁)
          (K₁.toCycles_comp_homologyπ i₁ j₁)).pt) := by
    change PreservesColimit _ (tensorLeft (K₁.homology j₁))
    infer_instance
  let _ : PreservesColimit (parallelPair (L₂.toCycles i₂ j₂) 0)
      (tensorLeft
        (CokernelCofork.ofπ (L₁.homologyπ j₁)
          (L₁.toCycles_comp_homologyπ i₁ j₁)).pt) := by
    change PreservesColimit _ (tensorLeft (L₁.homology j₁))
    infer_instance
  exact CokernelCofork.tensorDesc_naturality
    (CokernelCofork.ofπ (K₁.homologyπ j₁) (K₁.toCycles_comp_homologyπ i₁ j₁))
    (K₁.homologyIsCokernel i₁ j₁ h₁)
    (CokernelCofork.ofπ (K₂.homologyπ j₂) (K₂.toCycles_comp_homologyπ i₂ j₂))
    (K₂.homologyIsCokernel i₂ j₂ h₂)
    (CokernelCofork.ofπ (L₁.homologyπ j₁) (L₁.toCycles_comp_homologyπ i₁ j₁))
    (L₁.homologyIsCokernel i₁ j₁ h₁)
    (CokernelCofork.ofπ (L₂.homologyπ j₂) (L₂.toCycles_comp_homologyπ i₂ j₂))
    (L₂.homologyIsCokernel i₂ j₂ h₂)
    (K₁.cyclesMap f₁ j₁) (K₂.cyclesMap f₂ j₂)
    (K₁.homologyMap f₁ j₁) (K₂.homologyMap f₂ j₂)
    (K₁.homologyπ_naturality f₁ j₁)
    (K₂.homologyπ_naturality f₂ j₂)
    k hk k' hk' z hz

end HomologicalComplex
