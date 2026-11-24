/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# The canonical cokernel–middle–kernel sequence

Four actual composable arrows a,u,m,d supply cokernel(a)→middle→kernel(d).
The data requires their adjacent zero relations and the two local limits.
Native exactness of the original sequence makes this actual short complex
short exact in a preadditive category. No comparison is supplied.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.ComposableArrows

universe u v

variable {C : Type u} [Category.{v} C]

section ZeroMorphisms

variable [HasZeroMorphisms C]

/-- The original adjacent arrow, with finite indices computed in a public definition. -/
abbrev fourArrowMap (S : ComposableArrows C 4) (i : Fin 4) :
    S.obj i.castSucc ⟶ S.obj i.succ :=
  S.map (homOfLE (show i.castSucc ≤ i.succ from Nat.le_succ i.val))

section Data

variable (S : ComposableArrows C 4) (hS : S.IsComplex)
  [HasCokernel (S.fourArrowMap 0)] [HasKernel (S.fourArrowMap 3)]

/-- The canonical sequence uses the actual cokernel descent and kernel lift. -/
@[implicit_reducible]
def middleKernelCokernelSequence : ShortComplex C :=
  ShortComplex.mk
    (cokernel.desc (S.fourArrowMap 0) (S.fourArrowMap 1) (hS.zero 0))
    (kernel.lift (S.fourArrowMap 3) (S.fourArrowMap 2) (hS.zero 2)) (by
      apply (cancel_epi (cokernel.π (S.fourArrowMap 0))).1
      apply (cancel_mono (kernel.ι (S.fourArrowMap 3))).1
      simp only [Category.assoc, kernel.lift_ι, cokernel.π_desc_assoc,
        hS.zero 1, Limits.comp_zero, Limits.zero_comp])

/-- The first object is the actual cokernel of the original first arrow. -/
theorem middleKernelCokernelSequence_X₁ :
    (middleKernelCokernelSequence S hS).X₁ = cokernel (S.fourArrowMap 0) := rfl

/-- The middle object is unchanged from the original sequence. -/
theorem middleKernelCokernelSequence_X₂ :
    (middleKernelCokernelSequence S hS).X₂ = S.obj (2 : Fin 5) := rfl

/-- The third object is the actual kernel of the original last arrow. -/
theorem middleKernelCokernelSequence_X₃ :
    (middleKernelCokernelSequence S hS).X₃ = kernel (S.fourArrowMap 3) := rfl

/-- The actual first map factors the original second arrow. -/
@[reassoc]
theorem middleKernelCokernelSequence_π_f :
    cokernel.π (S.fourArrowMap 0) ≫ (middleKernelCokernelSequence S hS).f = S.fourArrowMap 1 :=
  cokernel.π_desc _ _ _

/-- The actual second map factors the original third arrow. -/
@[reassoc]
theorem middleKernelCokernelSequence_g_ι :
    (middleKernelCokernelSequence S hS).g ≫ kernel.ι (S.fourArrowMap 3) = S.fourArrowMap 2 :=
  kernel.lift_ι _ _ _

end Data

section Naturality

variable {S T V : ComposableArrows C 4}
  [HasCokernel (S.fourArrowMap 0)] [HasKernel (S.fourArrowMap 3)]
  [HasCokernel (T.fourArrowMap 0)] [HasKernel (T.fourArrowMap 3)]
  [HasCokernel (V.fourArrowMap 0)] [HasKernel (V.fourArrowMap 3)]

/-- The original natural transformation induces its actual cokernel, middle and kernel maps. -/
def middleKernelCokernelSequenceMap (φ : S ⟶ T) (hS : S.IsComplex) (hT : T.IsComplex) :
    middleKernelCokernelSequence S hS ⟶ middleKernelCokernelSequence T hT := by
  refine ShortComplex.homMk
    (cokernel.map (S.fourArrowMap 0) (T.fourArrowMap 0)
      (app' φ 0 (by decide)) (app' φ 1 (by decide))
      (naturality' φ 0 1 (by decide) (by decide)))
    (app' φ 2 (by decide))
    (kernel.map (S.fourArrowMap 3) (T.fourArrowMap 3) (app' φ 3 (by decide)) (app' φ 4 (by decide))
      (naturality' φ 3 4 (by decide) (by decide))) ?_ ?_
  · exact cokernel.map_desc (S.fourArrowMap 0) (S.fourArrowMap 1) (hS.zero 0)
      (T.fourArrowMap 0) (T.fourArrowMap 1) (hT.zero 0)
      (app' φ 0 (by decide)) (app' φ 1 (by decide)) (app' φ 2 (by decide))
      (naturality' φ 0 1 (by decide) (by decide))
      (naturality' φ 1 2 (by decide) (by decide))
  · dsimp only [middleKernelCokernelSequence]
    apply (cancel_mono (kernel.ι (T.fourArrowMap 3))).1
    rw [Category.assoc, kernel.lift_ι]
    dsimp only [kernel.map]
    rw [Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc]
    exact (naturality' φ 2 3 (by decide) (by decide)).symm

/-- The middle component is exactly the given map of the original middle objects. -/
theorem middleKernelCokernelSequenceMap_τ₂ (φ : S ⟶ T)
    (hS : S.IsComplex) (hT : T.IsComplex) :
    (middleKernelCokernelSequenceMap φ hS hT).τ₂ = app' φ 2 (by decide) := rfl

/-- The first component retains the original map of cokernel representatives. -/
@[reassoc]
theorem middleKernelCokernelSequenceMap_π (φ : S ⟶ T)
    (hS : S.IsComplex) (hT : T.IsComplex) :
    cokernel.π (S.fourArrowMap 0) ≫ (middleKernelCokernelSequenceMap φ hS hT).τ₁ =
      app' φ 1 (by decide) ≫ cokernel.π (T.fourArrowMap 0) := by
  dsimp only [middleKernelCokernelSequenceMap, ShortComplex.homMk, cokernel.map]
  exact cokernel.π_desc _ _ _

/-- The last component retains the original map of kernel representatives. -/
@[reassoc]
theorem middleKernelCokernelSequenceMap_ι (φ : S ⟶ T)
    (hS : S.IsComplex) (hT : T.IsComplex) :
    (middleKernelCokernelSequenceMap φ hS hT).τ₃ ≫ kernel.ι (T.fourArrowMap 3) =
      kernel.ι (S.fourArrowMap 3) ≫ app' φ 3 (by decide) := by
  dsimp only [middleKernelCokernelSequenceMap, kernel.map]
  exact kernel.lift_ι _ _ _

/-- Identity transformations act as identity on the canonical clipped sequence. -/
theorem middleKernelCokernelSequenceMap_id (hS : S.IsComplex) :
    middleKernelCokernelSequenceMap (𝟙 S) hS hS = 𝟙 (middleKernelCokernelSequence S hS) := by
  dsimp only [middleKernelCokernelSequence]
  apply ShortComplex.hom_ext
  · apply (cancel_epi (cokernel.π (S.fourArrowMap 0))).1
    rw [middleKernelCokernelSequenceMap_π]
    change 𝟙 _ ≫ cokernel.π (S.fourArrowMap 0) =
      cokernel.π (S.fourArrowMap 0) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
  · rw [middleKernelCokernelSequenceMap_τ₂]
    rfl
  · apply (cancel_mono (kernel.ι (S.fourArrowMap 3))).1
    rw [middleKernelCokernelSequenceMap_ι]
    change kernel.ι (S.fourArrowMap 3) ≫ 𝟙 _ =
      𝟙 _ ≫ kernel.ι (S.fourArrowMap 3)
    rw [Category.id_comp, Category.comp_id]

/-- Composition preserves the original natural-transformation order. -/
theorem middleKernelCokernelSequenceMap_comp (φ : S ⟶ T) (ψ : T ⟶ V)
    (hS : S.IsComplex) (hT : T.IsComplex) (hV : V.IsComplex) :
    middleKernelCokernelSequenceMap (φ ≫ ψ) hS hV =
      middleKernelCokernelSequenceMap φ hS hT ≫ middleKernelCokernelSequenceMap ψ hT hV := by
  dsimp only [middleKernelCokernelSequence]
  apply ShortComplex.hom_ext
  · apply (cancel_epi (cokernel.π (S.fourArrowMap 0))).1
    rw [ShortComplex.comp_τ₁, middleKernelCokernelSequenceMap_π,
      ← Category.assoc, middleKernelCokernelSequenceMap_π, Category.assoc,
      middleKernelCokernelSequenceMap_π]
    change (app' φ 1 (by decide) ≫ app' ψ 1 (by decide)) ≫
        cokernel.π (V.fourArrowMap 0) =
      app' φ 1 (by decide) ≫ app' ψ 1 (by decide) ≫ cokernel.π (V.fourArrowMap 0)
    exact Category.assoc _ _ _
  · rw [ShortComplex.comp_τ₂, middleKernelCokernelSequenceMap_τ₂,
      middleKernelCokernelSequenceMap_τ₂, middleKernelCokernelSequenceMap_τ₂]
    rfl
  · apply (cancel_mono (kernel.ι (V.fourArrowMap 3))).1
    rw [ShortComplex.comp_τ₃, middleKernelCokernelSequenceMap_ι,
      Category.assoc, middleKernelCokernelSequenceMap_ι,
      ← Category.assoc, middleKernelCokernelSequenceMap_ι]
    change kernel.ι (S.fourArrowMap 3) ≫
        (app' φ 3 (by decide) ≫ app' ψ 3 (by decide)) =
      (kernel.ι (S.fourArrowMap 3) ≫ app' φ 3 (by decide)) ≫ app' ψ 3 (by decide)
    exact (Category.assoc _ _ _).symm

end Naturality

end ZeroMorphisms

section Exactness

variable [Preadditive C] (S : ComposableArrows C 4)
  [HasCokernel (S.fourArrowMap 0)] [HasKernel (S.fourArrowMap 3)]

/-- Native exactness of the given sequence makes the actual canonical clip short exact. -/
theorem middleKernelCokernelSequence_shortExact (hS : S.Exact) :
    (middleKernelCokernelSequence S hS.toIsComplex).ShortExact := by
  let K := middleKernelCokernelSequence S hS.toIsComplex
  let A : ShortComplex C := ShortComplex.mk (S.fourArrowMap 0) (S.fourArrowMap 1)
    (hS.zero 0)
  let M : ShortComplex C := ShortComplex.mk (S.fourArrowMap 1) (S.fourArrowMap 2)
    (hS.zero 1)
  let D : ShortComplex C := ShortComplex.mk (S.fourArrowMap 2) (S.fourArrowMap 3)
    (hS.zero 2)
  have hA : A.Exact := by
    change (S.sc hS.toIsComplex 0 (by decide)).Exact
    exact hS.exact 0 (by decide)
  have hM : M.Exact := by
    change (S.sc hS.toIsComplex 1 (by decide)).Exact
    exact hS.exact 1 (by decide)
  have hD : D.Exact := by
    change (S.sc hS.toIsComplex 2 (by decide)).Exact
    exact hS.exact 2 (by decide)
  letI : A.HasHomology := hA.hasHomology
  letI : D.HasHomology := hD.hasHomology
  have hf : Mono K.f := by
    change Mono (cokernel.desc A.f A.g A.zero)
    exact hA.mono_cokernelDesc
  have hg : Epi K.g := by
    change Epi (kernel.lift D.g D.f D.zero)
    exact hD.epi_kernelLift
  let T : ShortComplex C := ShortComplex.mk K.f (S.fourArrowMap 2) (by
    dsimp only [K, middleKernelCokernelSequence]
    apply (cancel_epi (cokernel.π (S.fourArrowMap 0))).1
    rw [cokernel.π_desc_assoc, hS.zero 1, Limits.comp_zero])
  let φ : M ⟶ T := ShortComplex.homMk (cokernel.π (S.fourArrowMap 0)) (𝟙 _) (𝟙 _)
    (by
      dsimp only [M, T, K, middleKernelCokernelSequence]
      rw [cokernel.π_desc, Category.comp_id])
    (by
      dsimp only [M, T]
      rw [Category.id_comp, Category.comp_id])
  let : Epi φ.τ₁ := by
    change Epi (cokernel.π (S.fourArrowMap 0))
    infer_instance
  let : IsIso φ.τ₂ := by
    change IsIso (𝟙 M.X₂)
    infer_instance
  let : Mono φ.τ₃ := by
    change Mono (𝟙 M.X₃)
    infer_instance
  have hT : T.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp hM
  let ψ : K ⟶ T := ShortComplex.homMk (𝟙 _) (𝟙 _) (kernel.ι (S.fourArrowMap 3))
    (by
      dsimp only [T]
      rw [Category.id_comp, Category.comp_id])
    (by
      dsimp only [T, K, middleKernelCokernelSequence]
      rw [Category.id_comp, kernel.lift_ι])
  let : Epi ψ.τ₁ := by
    change Epi (𝟙 K.X₁)
    infer_instance
  let : IsIso ψ.τ₂ := by
    change IsIso (𝟙 K.X₂)
    infer_instance
  let : Mono ψ.τ₃ := by
    change Mono (kernel.ι (S.fourArrowMap 3))
    infer_instance
  exact ShortComplex.ShortExact.mk'
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).mpr hT) hf hg

end Exactness

end CategoryTheory.ComposableArrows
