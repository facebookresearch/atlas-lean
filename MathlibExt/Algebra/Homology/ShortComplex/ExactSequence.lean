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
# The canonical cokernel middle kernel sequence

Let A₀ —a→ A₁ —u→ A₂ —m→ A₃ —d→ A₄ be a four-arrow sequence whose adjacent composites vanish. If
coker(a) and ker(d) exist, cokernel descent of u and kernel lift of m form coker(a) → A₂ →
ker(d).

Maps of the original sequences induce maps of these three objects with the usual quotient and
inclusion characteristics. In a preadditive category, exactness of the original four-arrow
sequence makes its canonical clip short exact.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.ComposableArrows

universe u v

variable {C : Type u} [Category.{v} C]

section ZeroMorphisms

variable [HasZeroMorphisms C]

/-- Let C be a category and S a sequence A₀ → A₁ → A₂ → A₃ → A₄ of four composable arrows. For
i∈{0,1,2,3}, fourArrowMap(S,i) is the original arrow Aᵢ → Aᵢ₊₁. -/
abbrev fourArrowMap (S : ComposableArrows C 4) (i : Fin 4) :
    S.obj i.castSucc ⟶ S.obj i.succ :=
  S.map (homOfLE (show i.castSucc ≤ i.succ from Nat.le_succ i.val))

section Data

variable (S : ComposableArrows C 4) (hS : S.IsComplex)
  [HasCokernel (S.fourArrowMap 0)] [HasKernel (S.fourArrowMap 3)]

/-- Let C have zero morphisms, and let S be A₀ —a→ A₁ —u→ A₂ —m→ A₃ —d→ A₄ with a ≫ u=u ≫ m=m ≫ d=0.
Assume the cokernel of a and the kernel of d exist. There is a canonical short complex coker(a)
→ A₂ → ker(d). Its first arrow is the descent of u through coker(a), and its second arrow is the
lift of m through ker(d); their composite is zero. -/
@[implicit_reducible]
def middleKernelCokernelSequence : ShortComplex C :=
  ShortComplex.mk
    (cokernel.desc (S.fourArrowMap 0) (S.fourArrowMap 1) (hS.zero 0))
    (kernel.lift (S.fourArrowMap 3) (S.fourArrowMap 2) (hS.zero 2)) (by
      apply (cancel_epi (cokernel.π (S.fourArrowMap 0))).1
      apply (cancel_mono (kernel.ι (S.fourArrowMap 3))).1
      simp only [Category.assoc, kernel.lift_ι, cokernel.π_desc_assoc,
        hS.zero 1, Limits.comp_zero, Limits.zero_comp])

/-- Let C have zero morphisms, and let S be A₀ —a→ A₁ —u→ A₂ —m→ A₃ —d→ A₄ with a ≫ u=u ≫ m=m ≫ d=0.
Assume the cokernel of a and the kernel of d exist. The left object of the canonical clipped
sequence coker(a) → A₂ → ker(d) is the cokernel of the original first arrow a. -/
theorem middleKernelCokernelSequence_X₁ :
    (middleKernelCokernelSequence S hS).X₁ = cokernel (S.fourArrowMap 0) := rfl

/-- Let C have zero morphisms, and let S be A₀ —a→ A₁ —u→ A₂ —m→ A₃ —d→ A₄ with a ≫ u=u ≫ m=m ≫ d=0.
Assume the cokernel of a and the kernel of d exist. The middle object of the canonical clipped
sequence is the original object A₂. -/
theorem middleKernelCokernelSequence_X₂ :
    (middleKernelCokernelSequence S hS).X₂ = S.obj (2 : Fin 5) := rfl

/-- Let C have zero morphisms, and let S be A₀ —a→ A₁ —u→ A₂ —m→ A₃ —d→ A₄ with a ≫ u=u ≫ m=m ≫ d=0.
Assume the cokernel of a and the kernel of d exist. The right object of the canonical clipped
sequence is the kernel of the original final arrow d. -/
theorem middleKernelCokernelSequence_X₃ :
    (middleKernelCokernelSequence S hS).X₃ = kernel (S.fourArrowMap 3) := rfl

/-- Let C have zero morphisms, and let S be A₀ —a→ A₁ —u→ A₂ —m→ A₃ —d→ A₄ with a ≫ u=u ≫ m=m ≫ d=0.
Assume the cokernel of a and the kernel of d exist. If j : coker(a) → A₂ is the first clipped
arrow and π : A₁ → coker(a) the cokernel quotient, then π ≫ j=u. -/
@[reassoc]
theorem middleKernelCokernelSequence_π_f :
    cokernel.π (S.fourArrowMap 0) ≫ (middleKernelCokernelSequence S hS).f = S.fourArrowMap 1 :=
  cokernel.π_desc _ _ _

/-- Let C have zero morphisms, and let S be A₀ —a→ A₁ —u→ A₂ —m→ A₃ —d→ A₄ with a ≫ u=u ≫ m=m ≫ d=0.
Assume the cokernel of a and the kernel of d exist. If r : A₂ → ker(d) is the second clipped
arrow and i : ker(d) → A₃ the kernel inclusion, then r ≫ i=m. -/
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

/-- Let C have zero morphisms, let φ : S → T be a componentwise commuting map of four-arrow
sequences with all adjacent composites zero, and assume their first-arrow cokernels and
last-arrow kernels exist. The induced map of clipped short complexes has components
coker(φ₀,φ₁), φ₂, and ker(φ₃,φ₄), from coker(a_S) → S₂ → ker(d_S) to coker(a_T) → T₂ → ker(d_T). -/
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

/-- Let C have zero morphisms, let φ : S → T be a componentwise commuting map of four-arrow
sequences with all adjacent composites zero, and assume their first-arrow cokernels and
last-arrow kernels exist. The middle component of the clipped-sequence map is precisely φ₂ : S₂
→ T₂. -/
theorem middleKernelCokernelSequenceMap_τ₂ (φ : S ⟶ T)
    (hS : S.IsComplex) (hT : T.IsComplex) :
    (middleKernelCokernelSequenceMap φ hS hT).τ₂ = app' φ 2 (by decide) := rfl

/-- Let C have zero morphisms, let φ : S → T be a componentwise commuting map of four-arrow
sequences with all adjacent composites zero, and assume their first-arrow cokernels and
last-arrow kernels exist. The cokernel component c satisfies π_S ≫ c=φ₁ ≫ π_T, where π_S and π_T
are the first-arrow cokernel quotients. -/
@[reassoc]
theorem middleKernelCokernelSequenceMap_π (φ : S ⟶ T)
    (hS : S.IsComplex) (hT : T.IsComplex) :
    cokernel.π (S.fourArrowMap 0) ≫ (middleKernelCokernelSequenceMap φ hS hT).τ₁ =
      app' φ 1 (by decide) ≫ cokernel.π (T.fourArrowMap 0) := by
  dsimp only [middleKernelCokernelSequenceMap, ShortComplex.homMk, cokernel.map]
  exact cokernel.π_desc _ _ _

/-- Let C have zero morphisms, let φ : S → T be a componentwise commuting map of four-arrow
sequences with all adjacent composites zero, and assume their first-arrow cokernels and
last-arrow kernels exist. The kernel component k satisfies k ≫ i_T=i_S ≫ φ₃, where i_S and i_T
are the last-arrow kernel inclusions. -/
@[reassoc]
theorem middleKernelCokernelSequenceMap_ι (φ : S ⟶ T)
    (hS : S.IsComplex) (hT : T.IsComplex) :
    (middleKernelCokernelSequenceMap φ hS hT).τ₃ ≫ kernel.ι (T.fourArrowMap 3) =
      kernel.ι (S.fourArrowMap 3) ≫ app' φ 3 (by decide) := by
  dsimp only [middleKernelCokernelSequenceMap, kernel.map]
  exact kernel.lift_ι _ _ _

/-- Let C have zero morphisms, and let S be A₀ —a→ A₁ —u→ A₂ —m→ A₃ —d→ A₄ with a ≫ u=u ≫ m=m ≫ d=0.
Assume the cokernel of a and the kernel of d exist. The identity on the original four-arrow
sequence induces the identity on coker(a) → A₂ → ker(d). -/
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

/-- Let C have zero morphisms and let φ : S → T and ψ : T → V be maps of four-arrow complexes.
Assume the relevant first-arrow cokernels and last-arrow kernels exist. The clipped-sequence map
of ψ ∘ φ is the clipped map of φ followed by that of ψ. -/
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

/-- Let C be preadditive and let A₀ —a→ A₁ —u→ A₂ —m→ A₃ —d→ A₄ be exact. Assume coker(a) and ker(d)
exist. The canonical sequence 0 → coker(a) → A₂ → ker(d) → 0 is short exact, with the arrows
induced by u and m. -/
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
