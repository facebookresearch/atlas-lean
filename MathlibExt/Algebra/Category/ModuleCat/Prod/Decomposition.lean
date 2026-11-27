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

public import MathlibExt.Algebra.Category.ModuleCat.Prod.EmbeddingComponents
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Product decomposition for `ModuleCat (R × S)`

For `M : ModuleCat (R × S)` with idempotents `e = (1,0)` and `f = (0,1)` we have
`M ≃ₗ eM × fM`.  Using the pinned `biprodIsoProd` and the ambient embedding
identifications we obtain explicit `ModuleCat (R × S)` isomorphisms to binary
biproducts and to the embedded `R`/`S` components, plus simp formulas for
their forward and inverse maps.
-/

@[expose] public section

open CategoryTheory Limits

universe v

namespace ProdIdempotent

variable {R S : Type*} [Ring R] [Ring S]

section DecompositionIso

variable (R S : Type*) [Ring R] [Ring S]

/-- Decomposition `M ≅ of (eM × fM)` as `ModuleCat (R × S)` objects via `decompEquiv`:
the linear equivalence `M ≃ₗ eM × fM` from the idempotents `e = (1, 0)`, `f = (0, 1)`
lifted to an isomorphism in `ModuleCat (R × S)`. -/
noncomputable def decompToProdIso (M : ModuleCat.{v} (R × S)) :
    M ≅ ModuleCat.of (R × S)
      (eSubmodule (R := R) (S := S) (M := M) ×
        fSubmodule (R := R) (S := S) (M := M)) :=
  LinearEquiv.toModuleIso (decompEquiv (R := R) (S := S) (M := (M : Type v)))

/-- Canonical iso `of (eM × fM) ≅ of eM ⊞ of fM` via pinned `biprodIsoProd`.

Bridges explicit product objects to biproducts; used downstream in
`FGModuleCat.Prod.DecompositionBiproduct`. -/
noncomputable def prodToBiprodIso (M : ModuleCat.{v} (R × S)) :
    ModuleCat.of (R × S)
        (eSubmodule (R := R) (S := S) (M := M) ×
          fSubmodule (R := R) (S := S) (M := M)) ≅
      (ModuleCat.of (R × S) (eSubmodule (R := R) (S := S) (M := M)) ⊞
        ModuleCat.of (R × S) (fSubmodule (R := R) (S := S) (M := M))) :=
  (ModuleCat.biprodIsoProd
    (ModuleCat.of (R × S) (eSubmodule (R := R) (S := S) (M := M)))
    (ModuleCat.of (R × S) (fSubmodule (R := R) (S := S) (M := M)))).symm

/-- Decomposition `M ≅ of eM ⊞ of fM` for `M : ModuleCat (R × S)`. -/
noncomputable def decompBiprodIso (M : ModuleCat.{v} (R × S)) :
    M ≅ (ModuleCat.of (R × S) (eSubmodule (R := R) (S := S) (M := M)) ⊞
          ModuleCat.of (R × S) (fSubmodule (R := R) (S := S) (M := M))) :=
  (decompToProdIso R S M).trans (prodToBiprodIso R S M)

/-- Forward map of `decompBiprodIso` via `prodToBiprodIso` and `e • m`, `f • m`. -/
theorem decompBiprodIso_hom_apply (M : ModuleCat.{v} (R × S)) (m : M) :
    (decompBiprodIso R S M).hom.hom m =
      (prodToBiprodIso R S M).hom.hom
        ((⟨ProdIdempotent.e R S • (m : M),
              ProdIdempotent.e_smul_mem_eSubmodule (R := R) (S := S) _⟩ :
            eSubmodule (R := R) (S := S) (M := (M : Type v))),
          (⟨ProdIdempotent.f R S • (m : M),
              ProdIdempotent.f_smul_mem_fSubmodule (R := R) (S := S) _⟩ :
            fSubmodule (R := R) (S := S) (M := (M : Type v)))) :=
  rfl

/-- Inverse of `decompBiprodIso` adds the underlying components. -/
theorem decompBiprodIso_inv_apply (M : ModuleCat.{v} (R × S))
    (x : eSubmodule (R := R) (S := S) (M := (M : Type v)))
    (y : fSubmodule (R := R) (S := S) (M := (M : Type v))) :
    (decompBiprodIso R S M).inv.hom ((prodToBiprodIso R S M).hom.hom (x, y)) =
      x.val + y.val := by
  have h1 : (prodToBiprodIso R S M).hom ≫ (prodToBiprodIso R S M).inv =
      𝟙 (ModuleCat.of (R × S)
          (eSubmodule (R := R) (S := S) (M := M) ×
            fSubmodule (R := R) (S := S) (M := M))) :=
    Iso.hom_inv_id _
  calc
    (decompBiprodIso R S M).inv.hom ((prodToBiprodIso R S M).hom.hom (x, y)) =
        (decompToProdIso R S M).inv.hom
          ((prodToBiprodIso R S M).inv.hom
            ((prodToBiprodIso R S M).hom.hom (x, y))) := by
      rfl
    _ = (decompToProdIso R S M).inv.hom (x, y) := by
      have h2 : ((prodToBiprodIso R S M).hom ≫ (prodToBiprodIso R S M).inv).hom (x, y) =
          (x, y) := by
        rw [h1]
        rfl
      have h3 : (prodToBiprodIso R S M).inv.hom
          ((prodToBiprodIso R S M).hom.hom (x, y)) = (x, y) := by
        exact h2
      rw [h3]
    _ = x.val + y.val := by
      rfl

end DecompositionIso

section ObjectwiseIso

variable {R S : Type*} [Ring R] [Ring S]

/-- Canonical objectwise iso built from `decompEquiv`,
`eSubmoduleIsoEmbeddingFst`, `fSubmoduleIsoEmbeddingSnd`,
and `biprodIsoProd`. -/
noncomputable def prodDecompositionIso (M : ModuleCat.{v} (R × S)) :
    M ≅ ((ModuleCat.prodEmbeddingFst R S).obj (eComponentFunctor.obj M) ⊞
          (ModuleCat.prodEmbeddingSnd R S).obj (fComponentFunctor.obj M)) :=
  (decompBiprodIso (R := R) (S := S) M).trans
    (biprod.mapIso (eSubmoduleIsoEmbeddingFst M) (fSubmoduleIsoEmbeddingSnd M))

/-- Forward map of `prodDecompositionIso` expressed via `prodToBiprodIso`. -/
theorem prodDecompositionIso_hom_apply (M : ModuleCat.{v} (R × S)) (m : M) :
    (prodDecompositionIso (M := M)).hom.hom m =
      (biprod.mapIso (eSubmoduleIsoEmbeddingFst M) (fSubmoduleIsoEmbeddingSnd M)).hom.hom
        ((prodToBiprodIso R S M).hom.hom
          ((⟨ProdIdempotent.e R S • (m : M),
                ProdIdempotent.e_smul_mem_eSubmodule (R := R) (S := S) _⟩ :
              eSubmodule (R := R) (S := S) (M := (M : Type v))),
            (⟨ProdIdempotent.f R S • (m : M),
                ProdIdempotent.f_smul_mem_fSubmodule (R := R) (S := S) _⟩ :
              fSubmodule (R := R) (S := S) (M := (M : Type v))))) :=
  rfl

/-- Inverse of `prodDecompositionIso` adds underlying components after
unfolding the embedding comparison iso. -/
theorem prodDecompositionIso_inv_apply (M : ModuleCat.{v} (R × S))
    (x : eSubmodule (R := R) (S := S) (M := (M : Type v)))
    (y : fSubmodule (R := R) (S := S) (M := (M : Type v))) :
    (prodDecompositionIso (M := M)).inv.hom
        ((biprod.mapIso (eSubmoduleIsoEmbeddingFst M) (fSubmoduleIsoEmbeddingSnd M)).hom.hom
          ((prodToBiprodIso R S M).hom.hom (x, y))) =
      x.val + y.val := by
  calc
    (prodDecompositionIso M).inv.hom
          ((biprod.mapIso (eSubmoduleIsoEmbeddingFst M) (fSubmoduleIsoEmbeddingSnd M)).hom.hom
            ((prodToBiprodIso R S M).hom.hom (x, y))) =
        (decompBiprodIso R S M).inv.hom
          ((biprod.mapIso (eSubmoduleIsoEmbeddingFst M) (fSubmoduleIsoEmbeddingSnd M)).inv.hom
            ((biprod.mapIso (eSubmoduleIsoEmbeddingFst M) (fSubmoduleIsoEmbeddingSnd M)).hom.hom
              ((prodToBiprodIso R S M).hom.hom (x, y)))) := by
      rfl
    _ = (decompBiprodIso R S M).inv.hom ((prodToBiprodIso R S M).hom.hom (x, y)) := by
      have hmap : (biprod.mapIso (eSubmoduleIsoEmbeddingFst M)
            (fSubmoduleIsoEmbeddingSnd M)).hom ≫
            (biprod.mapIso (eSubmoduleIsoEmbeddingFst M)
              (fSubmoduleIsoEmbeddingSnd M)).inv =
          𝟙 _ :=
        Iso.hom_inv_id _
      have hmap2 : ((biprod.mapIso (eSubmoduleIsoEmbeddingFst M)
            (fSubmoduleIsoEmbeddingSnd M)).hom ≫
            (biprod.mapIso (eSubmoduleIsoEmbeddingFst M)
              (fSubmoduleIsoEmbeddingSnd M)).inv).hom
          ((prodToBiprodIso R S M).hom.hom (x, y)) =
          (prodToBiprodIso R S M).hom.hom (x, y) := by
        rw [hmap]
        rfl
      have hmap3 : (biprod.mapIso (eSubmoduleIsoEmbeddingFst M)
            (fSubmoduleIsoEmbeddingSnd M)).inv.hom
          ((biprod.mapIso (eSubmoduleIsoEmbeddingFst M)
              (fSubmoduleIsoEmbeddingSnd M)).hom.hom
            ((prodToBiprodIso R S M).hom.hom (x, y))) =
          (prodToBiprodIso R S M).hom.hom (x, y) := by
        exact hmap2
      rw [hmap3]
    _ = x.val + y.val := by
      exact decompBiprodIso_inv_apply R S M x y

end ObjectwiseIso

end ProdIdempotent
