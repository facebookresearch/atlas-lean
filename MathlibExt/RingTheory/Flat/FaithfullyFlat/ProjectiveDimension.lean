/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Faithfully flat descent of projective-dimension bounds

For a finite module over a Noetherian ring, a projective-dimension bound can
be checked after faithfully flat base change.  The proof inducts on the bound
using finite free covers and the short-exact projective-dimension API.

The `Small` hypothesis is the standard universe boundary required to form a
finite free cover in the same module-category universe as the source module.

## Main declaration

* `ModuleCat.hasProjectiveDimensionLE_of_tensorProduct_of_faithfullyFlat`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ModuleCat

/-- A projective-dimension bound for a finite module over a Noetherian ring
descends from any faithfully flat base change. -/
theorem hasProjectiveDimensionLE_of_tensorProduct_of_faithfullyFlat
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Module.FaithfullyFlat R S]
    {M : Type w} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Small.{w} R]
    (n : ℕ)
    (h : HasProjectiveDimensionLE (ModuleCat.of S (S ⊗[R] M)) n) :
    HasProjectiveDimensionLE (ModuleCat.of R M) n := by
  induction n generalizing M with
  | zero =>
      let _ : HasProjectiveDimensionLE
          (ModuleCat.of S (S ⊗[R] M)) 0 := h
      have hp : CategoryTheory.Projective
          (ModuleCat.of S (S ⊗[R] M)) := inferInstance
      let _ : Module.Projective S (S ⊗[R] M) :=
        (_root_.IsProjective.iff_projective (S ⊗[R] M)).mpr hp
      let _ : Module.Flat S (S ⊗[R] M) := inferInstance
      let _ : Module.Flat R M := Module.Flat.of_flat_tensorProduct R M S
      let _ : Module.FinitePresentation R M :=
        Module.finitePresentation_of_finite R M
      let _ : Module.Projective R M :=
        Module.Flat.projective_of_finitePresentation
      exact (projective_iff_hasProjectiveDimensionLE_zero _).mp
        ((_root_.IsProjective.iff_projective M).mp inferInstance)
  | succ n ih =>
      obtain ⟨P, _, _, _, _, f, hf⟩ :=
        Module.exists_finite_presentation R M
      let K := LinearMap.ker f
      let i : K →ₗ[R] P := (LinearMap.ker f).subtype
      have hKfin : Module.Finite R K := inferInstance
      let C : ShortComplex (ModuleCat R) := f.shortComplexKer
      have hC : C.ShortExact := LinearMap.shortExact_shortComplexKer hf
      let C' : ShortComplex (ModuleCat S) :=
        ShortComplex.mk
          (ModuleCat.ofHom (i.baseChange S))
          (ModuleCat.ofHom (f.baseChange S))
          (by
            apply ModuleCat.hom_ext
            change f.baseChange S ∘ₗ i.baseChange S = 0
            rw [← LinearMap.baseChange_comp]
            have hz : f ∘ₗ i = 0 := by
              ext x
              exact x.property
            rw [hz, LinearMap.baseChange_zero])
      have hC' : C'.ShortExact := by
        apply ModuleCat.shortComplex_shortExact C'
        · change Function.Exact (i.baseChange S) (f.baseChange S)
          rw [LinearMap.baseChange_eq_lTensor,
            LinearMap.baseChange_eq_lTensor]
          exact Module.Flat.lTensor_exact S f.exact_subtype_ker_map
        · change Function.Injective (i.baseChange S)
          rw [LinearMap.baseChange_eq_lTensor]
          exact Module.Flat.lTensor_preserves_injective_linearMap i
            (LinearMap.ker f).injective_subtype
        · change Function.Surjective (f.baseChange S)
          rw [LinearMap.baseChange_eq_lTensor]
          exact LinearMap.lTensor_surjective S hf
      have hPproj : CategoryTheory.Projective
          (ModuleCat.of S (S ⊗[R] P)) :=
        (_root_.IsProjective.iff_projective (S ⊗[R] P)).mp inferInstance
      have hKtarget : HasProjectiveDimensionLE
          (ModuleCat.of S (S ⊗[R] K)) n :=
        (hC'.hasProjectiveDimensionLT_X₃_iff n hPproj).mp h
      have hKsource : HasProjectiveDimensionLE
          (ModuleCat.of R K) n :=
        ih (M := K) hKtarget
      have hPsource : CategoryTheory.Projective
          (ModuleCat.of R P) :=
        (_root_.IsProjective.iff_projective P).mp inferInstance
      exact (hC.hasProjectiveDimensionLT_X₃_iff n hPsource).mpr hKsource

end ModuleCat
