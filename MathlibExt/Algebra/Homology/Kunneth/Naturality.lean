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

public import MathlibExt.Algebra.Homology.Kunneth.Edge

/-!
# Naturality maps for the Künneth tensor source

This module packages the finite antidiagonal map induced by homology maps in
both complex variables.  It establishes the identity and composition laws
needed by the later naturality theorem for the canonical Künneth homology
tensor map.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace HomologicalComplex

variable {R : Type u} [CommRing R]
variable {K K' K₁ K₂ K₃ L L' L₁ L₂ L₃ :
  ChainComplex (ModuleCat.{u} R) ℕ}

local instance : HasFiniteBiproducts (ModuleCat.{u} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts

/-- The finite antidiagonal map induced by homology maps in both complex
variables. -/
noncomputable def kunnethTensorSourceMap
    (f : K ⟶ K') (g : L ⟶ L') (n : ℕ) :
    (⨁ fun ij : KunnethTensorIndex n =>
      K.homology ij.val.1 ⊗ L.homology ij.val.2) ⟶
    (⨁ fun ij : KunnethTensorIndex n =>
      K'.homology ij.val.1 ⊗ L'.homology ij.val.2) :=
  biproduct.map fun ij =>
    HomologicalComplex.homologyMap f ij.val.1 ⊗ₘ
      HomologicalComplex.homologyMap g ij.val.2

/-- The selected component of the Künneth tensor-source map is the tensor of
the corresponding homology maps. -/
theorem kunnethTensorSourceMap_ι
    (f : K ⟶ K') (g : L ⟶ L') (n : ℕ)
    (ij : KunnethTensorIndex n) :
    biproduct.ι
        (fun kl : KunnethTensorIndex n =>
          K.homology kl.val.1 ⊗ L.homology kl.val.2) ij ≫
        kunnethTensorSourceMap f g n =
      (HomologicalComplex.homologyMap f ij.val.1 ⊗ₘ
          HomologicalComplex.homologyMap g ij.val.2) ≫
        biproduct.ι
          (fun kl : KunnethTensorIndex n =>
            K'.homology kl.val.1 ⊗ L'.homology kl.val.2) ij := by
  simpa only [kunnethTensorSourceMap] using
    (biproduct.ι_map
      (fun kl : KunnethTensorIndex n =>
        HomologicalComplex.homologyMap f kl.val.1 ⊗ₘ
          HomologicalComplex.homologyMap g kl.val.2) ij)

/-- Identity maps induce the identity Künneth tensor-source map. -/
@[simp]
theorem kunnethTensorSourceMap_id
    (K L : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    kunnethTensorSourceMap (𝟙 K) (𝟙 L) n = 𝟙 _ := by
  dsimp only [kunnethTensorSourceMap]
  apply biproduct.hom_ext'
  intro ij
  rw [biproduct.ι_map]
  simp only [HomologicalComplex.homologyMap_id,
    MonoidalCategory.id_tensorHom_id, Category.id_comp, Category.comp_id]

/-- Composition in both variables induces composition of Künneth
tensor-source maps. -/
@[simp]
theorem kunnethTensorSourceMap_comp
    (f₁ : K₁ ⟶ K₂) (f₂ : K₂ ⟶ K₃)
    (g₁ : L₁ ⟶ L₂) (g₂ : L₂ ⟶ L₃) (n : ℕ) :
    kunnethTensorSourceMap f₁ g₁ n ≫
        kunnethTensorSourceMap f₂ g₂ n =
      kunnethTensorSourceMap (f₁ ≫ f₂) (g₁ ≫ g₂) n := by
  dsimp only [kunnethTensorSourceMap]
  apply biproduct.hom_ext'
  intro ij
  rw [biproduct.ι_map_assoc]
  simp only [biproduct.ι_map]
  rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp]

/-- The canonical Künneth homology tensor map is natural in both complex
variables. -/
@[reassoc]
theorem kunnethHomologyTensorMap_naturality
    (f : K ⟶ K') (g : L ⟶ L') (n : ℕ) :
    kunnethTensorSourceMap f g n ≫
        kunnethHomologyTensorMap K' L' n =
      kunnethHomologyTensorMap K L n ≫
        HomologicalComplex.homologyMap (tensorHom f g) n := by
  apply biproduct.hom_ext'
  intro ij
  simp only [kunnethTensorSourceMap, kunnethHomologyTensorMap,
    biproduct.ι_map_assoc, biproduct.ι_desc_assoc, biproduct.ι_desc]
  let P : ChainGradedPairing K L (tensorObj K L) := 𝟙 _
  let Q : ChainGradedPairing K' L' (tensorObj K' L') := 𝟙 _
  let tfg := tensorHom f g
  have hpair : ∀ i j,
      P.pair i j ≫ tfg.f (i + j) =
        (f.f i ⊗ₘ g.f j) ≫ Q.pair i j := by
    intro i j
    exact (ChainGradedPairing.pair_naturality P Q f g tfg
      (by simp [P, Q, tfg]) i j).symm
  have hnat :
      (HomologicalComplex.homologyMap f ij.val.1 ⊗ₘ
          HomologicalComplex.homologyMap g ij.val.2) ≫
          ChainGradedPairing.pairHomology Q
            (ChainGradedPairing.homologyDescentData Q)
            ij.val.1 ij.val.2 =
        ChainGradedPairing.pairHomology P
            (ChainGradedPairing.homologyDescentData P)
            ij.val.1 ij.val.2 ≫
          HomologicalComplex.homologyMap tfg
            (ij.val.1 + ij.val.2) :=
    ChainGradedPairing.pairHomology_naturality
      P (ChainGradedPairing.homologyDescentData P)
      Q (ChainGradedPairing.homologyDescentData Q)
      f g tfg hpair ij.val.1 ij.val.2
  let hij : ij.val.1 + ij.val.2 = n :=
    Finset.mem_antidiagonal.mp ij.property
  change
    (HomologicalComplex.homologyMap f ij.val.1 ⊗ₘ
          HomologicalComplex.homologyMap g ij.val.2) ≫
        ChainGradedPairing.pairHomology Q
          (ChainGradedPairing.homologyDescentData Q)
          ij.val.1 ij.val.2 ≫
        (homologyIsoOfEq (tensorObj K' L') hij).hom =
      (ChainGradedPairing.pairHomology P
          (ChainGradedPairing.homologyDescentData P)
          ij.val.1 ij.val.2 ≫
        (homologyIsoOfEq (tensorObj K L) hij).hom) ≫
        HomologicalComplex.homologyMap tfg n
  slice_rhs 2 3 =>
    rw [← homologyIsoOfEq_hom_naturality tfg hij]
  have hnatTail := congrArg
    (fun k => k ≫
      (homologyIsoOfEq (tensorObj K' L') hij).hom) hnat
  simpa only [Category.assoc] using hnatTail

end HomologicalComplex

end
