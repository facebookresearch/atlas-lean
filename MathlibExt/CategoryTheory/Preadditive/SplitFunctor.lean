/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Preadditive.SplitKernel
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Additive functors preserve split complementary kernels and cokernels

Let `F : C → D` be additive between preadditive categories and
`i : Y → X`, `r : X → Y` satisfy `i ≫ r = 𝟙 Y`. The mapped
split pair gives the kernel and cokernel universal properties for
`F(q)`, where `q = 𝟙 X-r ≫ i`; hence `F` preserves these diagrams.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits

namespace CategoryTheory.Limits

universe uC vC uD vD

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  {D : Type uD} [Category.{vD} D] [Preadditive D]
  (F : C ⥤ D) [F.Additive]
  {X Y : C} (q : X ⟶ X) (i : Y ⟶ X) (r : X ⟶ Y)
  (hi : i ≫ r = 𝟙 Y) (hq : q = 𝟙 X - r ≫ i)

include hi hq in
/-- Let `F : C → D` be additive between preadditive categories, and
let `i : Y → X`, `r : X → Y` satisfy `i ≫ r = 𝟙 Y`,
`q = 𝟙 X-r ≫ i`. The functor `F` preserves the kernel of `q`,
using the mapped inclusion and retraction. -/
theorem preservesKernel_splitComplement :
    PreservesLimit (parallelPair q 0) F := by
  apply preservesLimit_of_preserves_limit_cone (splitComplementIsKernel q i r hi hq)
  let w : i ≫ q = 0 := inclusion_comp_splitComplement q i r hi hq
  let wF : F.map i ≫ F.map q = 0 := by
    simp only [← F.map_comp, w, Functor.map_zero]
  let mappedFork : Fork (F.map q) 0 := KernelFork.ofι (F.map i) wF
  have hMapped : IsLimit mappedFork :=
    splitComplementIsKernel (F.map q) (F.map i) (F.map r)
      (by rw [← F.map_comp, hi, F.map_id])
      (by rw [hq, F.map_sub, F.map_id, F.map_comp])
  let e : IsLimit (F.mapCone (KernelFork.ofι i w)) ≃ IsLimit mappedFork :=
    isLimitMapConeForkEquiv' F w
  exact e.symm hMapped

include hi hq in
/-- Let `F : C → D` be additive between preadditive categories, and
let `i : Y → X`, `r : X → Y` satisfy `i ≫ r = 𝟙 Y`,
`q = 𝟙 X-r ≫ i`. The functor `F` preserves the cokernel of `q`,
using the mapped inclusion and retraction. -/
theorem preservesCokernel_splitComplement :
    PreservesColimit (parallelPair q 0) F := by
  apply preservesColimit_of_preserves_colimit_cocone (splitComplementIsCokernel q i r hi hq)
  let w : q ≫ r = 0 := splitComplement_comp_retraction q i r hi hq
  let wF : F.map q ≫ F.map r = 0 := by
    simp only [← F.map_comp, w, Functor.map_zero]
  let mappedCofork : Cofork (F.map q) 0 := CokernelCofork.ofπ (F.map r) wF
  have hMapped : IsColimit mappedCofork :=
    splitComplementIsCokernel (F.map q) (F.map i) (F.map r)
      (by rw [← F.map_comp, hi, F.map_id])
      (by rw [hq, F.map_sub, F.map_id, F.map_comp])
  let e : IsColimit (F.mapCocone (CokernelCofork.ofπ r w)) ≃ IsColimit mappedCofork :=
    isColimitMapCoconeCoforkEquiv' F w
  exact e.symm hMapped

end CategoryTheory.Limits
