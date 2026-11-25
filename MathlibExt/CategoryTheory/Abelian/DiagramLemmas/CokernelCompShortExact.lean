/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp

/-!
# Cokernels of a composite with a monomorphism

For composable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` in an abelian
category, the last three terms of the kernel--cokernel exact sequence are

`cokernel f ⟶ cokernel (f ≫ g) ⟶ cokernel g`.

This file packages those terms as a short complex.  When `g` is a
monomorphism, the short complex is short exact.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The last three terms in the kernel--cokernel exact sequence of a
composite. -/
noncomputable abbrev cokernelCompShortComplex : ShortComplex C :=
  (kernelCokernelCompSequence_exact f g).sc 3

/-- The cokernel-composite short complex is exact. -/
theorem cokernelCompShortComplex_exact :
    (cokernelCompShortComplex f g).Exact :=
  (kernelCokernelCompSequence_exact f g).exact 3

/-- If the second morphism is mono, then
`cokernel f ⟶ cokernel (f ≫ g) ⟶ cokernel g` is short exact. -/
theorem cokernelCompShortComplex_shortExact [Mono g] :
    (cokernelCompShortComplex f g).ShortExact where
  exact := cokernelCompShortComplex_exact f g
  mono_f := by
    let T := kernelCokernelCompSequence f g
    let hT := kernelCokernelCompSequence_exact f g
    have hz : T.map' 2 3 = 0 :=
      (isZero_kernel_of_mono g).eq_of_src _ _
    have hm : Mono (T.map' 3 4) := (hT.exact 2).mono_g hz
    exact hm
  epi_g := by
    change Epi ((kernelCokernelCompSequence f g).map' 4 5)
    infer_instance

/-- Precomposing the first of two composable morphisms by an isomorphism
induces the canonical isomorphism of their cokernel-composition short
complexes. -/
noncomputable def cokernelCompShortComplexPrecompIso
    {X' : C} (e : X' ≅ X) :
    cokernelCompShortComplex (e.hom ≫ f) g ≅
      cokernelCompShortComplex f g :=
  ShortComplex.isoMk
    (cokernel.mapIso (e.hom ≫ f) f e (Iso.refl _) (by simp))
    (cokernel.mapIso ((e.hom ≫ f) ≫ g) (f ≫ g) e (Iso.refl _)
      (by simp [Category.assoc]))
    (Iso.refl _)
    (by
      dsimp [cokernelCompShortComplex]
      apply (cancel_epi (cokernel.π (e.hom ≫ f))).1
      simp [cokernel.map, Category.assoc])
    (by
      dsimp [cokernelCompShortComplex]
      apply (cancel_epi (cokernel.π ((e.hom ≫ f) ≫ g))).1
      simp [cokernel.map])

/-- Variant of `cokernelCompShortComplexPrecompIso` whose first map is only
propositionally equal to the displayed precomposition. -/
noncomputable def cokernelCompShortComplexPrecompIsoOfEq
    {X' : C} (e : X' ≅ X) (f' : X' ⟶ Y)
    (h : f' = e.hom ≫ f) :
    cokernelCompShortComplex f' g ≅ cokernelCompShortComplex f g :=
  eqToIso (congrArg (fun a => cokernelCompShortComplex a g) h) ≪≫
    cokernelCompShortComplexPrecompIso f g e

/-- First component of the precomposition comparison with a propositionally
equal first map. -/
theorem cokernelCompShortComplexPrecompIsoOfEq_hom_τ₁
    {X' : C} (e : X' ≅ X) (f' : X' ⟶ Y)
    (h : f' = e.hom ≫ f) :
    (cokernelCompShortComplexPrecompIsoOfEq f g e f' h).hom.τ₁ =
      (cokernel.mapIso f' f e (Iso.refl _) (by rw [h]; simp)).hom := by
  subst f'
  simp [cokernelCompShortComplexPrecompIsoOfEq,
    cokernelCompShortComplexPrecompIso]

/-- Third component of the precomposition comparison with a propositionally
equal first map. -/
theorem cokernelCompShortComplexPrecompIsoOfEq_hom_τ₃
    {X' : C} (e : X' ≅ X) (f' : X' ⟶ Y)
    (h : f' = e.hom ≫ f) :
    (cokernelCompShortComplexPrecompIsoOfEq f g e f' h).hom.τ₃ = 𝟙 _ := by
  subst f'
  simp [cokernelCompShortComplexPrecompIsoOfEq,
    cokernelCompShortComplexPrecompIso]

/-- First component after composing the precomposition comparison with a
further short-complex isomorphism. -/
theorem cokernelCompShortComplexPrecompIsoOfEq_trans_hom_τ₁
    {X' : C} (e : X' ≅ X) (f' : X' ⟶ Y)
    (h : f' = e.hom ≫ f) {T : ShortComplex C}
    (E : cokernelCompShortComplex f g ≅ T) :
    ((cokernelCompShortComplexPrecompIsoOfEq f g e f' h ≪≫ E).hom.τ₁) =
      (cokernel.mapIso f' f e (Iso.refl _) (by rw [h]; simp)).hom ≫
        E.hom.τ₁ := by
  rw [Iso.trans_hom]
  change (cokernelCompShortComplexPrecompIsoOfEq f g e f' h).hom.τ₁ ≫
    E.hom.τ₁ = _
  rw [cokernelCompShortComplexPrecompIsoOfEq_hom_τ₁]

/-- Third component after composing the precomposition comparison with a
further short-complex isomorphism. -/
theorem cokernelCompShortComplexPrecompIsoOfEq_trans_hom_τ₃
    {X' : C} (e : X' ≅ X) (f' : X' ⟶ Y)
    (h : f' = e.hom ≫ f) {T : ShortComplex C}
    (E : cokernelCompShortComplex f g ≅ T) :
    ((cokernelCompShortComplexPrecompIsoOfEq f g e f' h ≪≫ E).hom.τ₃) =
      E.hom.τ₃ := by
  rw [Iso.trans_hom]
  change (cokernelCompShortComplexPrecompIsoOfEq f g e f' h).hom.τ₃ ≫
    E.hom.τ₃ = _
  rw [cokernelCompShortComplexPrecompIsoOfEq_hom_τ₃, Category.id_comp]

end CategoryTheory

end
