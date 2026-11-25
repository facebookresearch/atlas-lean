/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/AlgebraicGeometry/Flatness/FlatQuotientPullbackMono.lean` (AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b):
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modifications: port the algebraic tensor-base-change statements directly on Mathlib objects; the
geometric stalk and graph producers remain source-covered prerequisites rather than additional
Wanted claims.
-/
module

public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.Localization

/-!
# Base change injectivity with a flat cokernel

These are complete source proofs. The map is the actual tensor base change
of a linear map. Flatness over the base kills its first Tor kernel even
when the intermediate algebra base change is not flat.

References: Stacks Tags 00HL and 0098. In the shtuka application, the
cokernel is a graph-line pushforward, which is flat over the family base.
The corresponding source graph and sheaf producers are credited in
`ShtukaPartialFrobenius`; they are not requested as new gaps.
-/

@[expose] public section

open TensorProduct
open scoped TensorProduct

universe u

section Algebra

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra A C] [Algebra (A ⊗[R] B) C]
  [IsScalarTower A (A ⊗[R] B) C]
  {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module A M] [Module A N] [Module A P] [Module R M] [Module R N] [Module R P]
  [IsScalarTower R A M] [IsScalarTower R A N] [IsScalarTower R A P]

/-- Base change along `A → A ⊗_R B` of an `A`-linear map `g` is, up to the canonical
identification `(A ⊗_R B) ⊗_A M ≅ B ⊗_R M`, the base change of `g` along `R → B`. -/
theorem LinearMap.injective_baseChange_tensorProduct_of_injective_lTensor (g : M →ₗ[A] N)
    (hg : Function.Injective ((g.restrictScalars R).lTensor B)) :
    Function.Injective (g.baseChange (A ⊗[R] B)) := by
  let eM : (A ⊗[R] B) ⊗[A] M ≃+ B ⊗[R] M :=
    ((TensorProduct.comm A (A ⊗[R] B) M).toAddEquiv.trans
      (AlgebraTensorModule.cancelBaseChange R A A M B).toAddEquiv).trans
      (TensorProduct.comm R M B).toAddEquiv
  let eN : (A ⊗[R] B) ⊗[A] N ≃+ B ⊗[R] N :=
    ((TensorProduct.comm A (A ⊗[R] B) N).toAddEquiv.trans
      (AlgebraTensorModule.cancelBaseChange R A A N B).toAddEquiv).trans
      (TensorProduct.comm R N B).toAddEquiv
  have hcomm : ∀ z, eN (g.baseChange (A ⊗[R] B) z) = (g.restrictScalars R).lTensor B (eM z) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul t m =>
      induction t using TensorProduct.inductionOn with
      | add t s ht hs => simp only [TensorProduct.add_tmul, map_add, ht, hs]
      | tmul a b =>
        simp [eM, eN, AlgebraTensorModule.cancelBaseChange_tmul]
  intro z w hzw
  apply eM.injective
  apply hg
  rw [← hcomm, ← hcomm, hzw]

/-- **Tor-vanishing against a module flat over the base, after a flat extension.** Let
`0 → M → N → P → 0` be exact over `A` with `P` flat over a ring `R` below `A`, let `B` be an
`R`-algebra and `C` a flat `A ⊗_R B`-algebra. Then `C ⊗_A M → C ⊗_A N` is injective. -/
theorem LinearMap.injective_baseChange_of_flat_cokernel [Module.Flat (A ⊗[R] B) C]
    [Module.Flat R P] (g : M →ₗ[A] N) (f : N →ₗ[A] P) (hg : Function.Injective g)
    (hf : Function.Surjective f) (hgf : Function.Exact g f) :
    Function.Injective (g.baseChange C) := by
  have h1 : Function.Injective (g.baseChange (A ⊗[R] B)) :=
    g.injective_baseChange_tensorProduct_of_injective_lTensor
      (LinearMap.lTensor_injective_of_exact_of_flat (f.restrictScalars R) hf
        (g.restrictScalars R) hg hgf B)
  have h2 : Function.Injective ((g.baseChange (A ⊗[R] B)).baseChange C) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ h1
  let cM := AlgebraTensorModule.cancelBaseChange A (A ⊗[R] B) C C M
  let cN := AlgebraTensorModule.cancelBaseChange A (A ⊗[R] B) C C N
  rw [LinearMap.baseChange_baseChange] at h2
  have h3 : Function.Injective (cN.symm ∘ g.baseChange C ∘ cM) := h2
  exact (Function.Injective.of_comp_iff' _ cM.bijective).1 ((cN.symm.injective.of_comp_iff _).1 h3)

end Algebra
