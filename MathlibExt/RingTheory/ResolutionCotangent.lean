/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/Cotangent/ResolutionComplex.lean` (AxiomMath/Stacks, revision
`c496df0d9beea9deaeabcea8492605f9a0a2313b`); the source file carries no individual copyright or
author notice.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modifications: only the augmented-simplicial cotangent construction is kept; negative indexing
uses Mathlib's complex embedding `ComplexShape.embeddingUpIntLE`; the dependencies used solely
for the standard-resolution comparison are omitted.
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import MathlibExt.RingTheory.CotangentScalarExtension

/-!
# The cotangent complex of an augmented simplicial algebra

For an augmented simplicial commutative `A`-algebra `ε : P• ⟶ B`, the degreewise base-changed
modules of differentials `B ⊗[Pₙ] Ω[Pₙ⁄A]` form a simplicial `B`-module, and its reindexed
alternating face map complex is the complex `Ω[P•⁄A] ⊗[P•] B` of `B`-modules, with simplicial
degree `n` in cohomological degree `-n`. For the standard resolution of `B` over `A` this is the
cotangent complex `L_{B/A}` of Stacks Tag 08PN, and by Stacks Remark 08QI every resolution gives
a complex isomorphic to it in `D(B)`; neither identification is formalized here.

## Main definitions

* `CommAlgCat.resolutionAugmentationHom`: the augmentation of a term, as a ring map to `B`.
* `CommAlgCat.resolutionCotangentTerm` and `CommAlgCat.resolutionCotangentTermDifferential`: the
  degreewise base-changed module of differentials and its pure differentials `1 ⊗ d p`.
* `CommAlgCat.resolutionCotangentPush`: the map induced by a morphism of terms lying over `B`.
* `CommAlgCat.ResolutionCotangentSimplicialModuleData` and
  `CommAlgCat.resolutionCotangentSimplicialModule`: the simplicial `B`-module together with the
  identifications of its terms and of its action on pure differentials.
* `CommAlgCat.resolutionCotangentComplex`: its associated integer-indexed cochain complex.

## Main results

* `CommAlgCat.resolutionCotangentPush_D` and `CommAlgCat.resolutionCotangentMap_D`: the induced
  maps send `1 ⊗ d p` to `1 ⊗ d (g p)`.
* `CommAlgCat.resolutionCotangentTerm_hom_ext`: a map out of a term is determined by its values
  on the pure differentials `1 ⊗ d p`.

## References

* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite Simplicial
open scoped ChangeOfRings TensorProduct

universe u v

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)
  (P : SimplicialObject (CommAlgCat.{max u v} A))
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{max u v} A)).obj B)

/-- The augmentation of a term of an augmented simplicial algebra, as a ring map to `B`. -/
noncomputable def resolutionAugmentationHom (n : SimplexCategoryᵒᵖ) : P.obj n →+* B :=
  (ε.app n).hom.toRingHom

/-- The augmentation condition on a morphism of terms, read as an identity of ring
homomorphisms. Simplicial operators satisfy it by naturality, but so do morphisms which are not
simplicial operators, and those are the ones a contraction of the augmentation is built from. -/
theorem resolutionAugmentationHom_comp_of_over {i j : SimplexCategoryᵒᵖ}
    (g : P.obj i ⟶ P.obj j) (hg : g ≫ ε.app j = ε.app i) :
    (resolutionAugmentationHom A B P ε j).comp g.hom.toRingHom =
      resolutionAugmentationHom A B P ε i :=
  RingHom.ext fun p => congrArg (fun k : P.obj i ⟶ B => k p) hg

/-- The augmentation is compatible with every simplicial operator. -/
theorem resolutionAugmentationHom_naturality {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    (resolutionAugmentationHom A B P ε j).comp (P.map f).hom.toRingHom =
      resolutionAugmentationHom A B P ε i :=
  resolutionAugmentationHom_comp_of_over A B P ε _ (by simp)

/-- The `n`th module of base-changed differentials of an augmented simplicial algebra. -/
@[implicit_reducible]
noncomputable def resolutionCotangentTerm (n : SimplexCategoryᵒᵖ) : ModuleCat.{max u v} B :=
  (ModuleCat.extendScalars (resolutionAugmentationHom A B P ε n)).obj
    (ModuleCat.of (P.obj n) (KaehlerDifferential A (P.obj n)))

/-- The pure differential `1 ⊗ d p` in the base-changed differential module. -/
noncomputable def resolutionCotangentTermDifferential (n : SimplexCategoryᵒᵖ) (p : P.obj n) :
    resolutionCotangentTerm A B P ε n :=
  (1 : B) ⊗ₜ KaehlerDifferential.D A (P.obj n) p

/-- Data of the simplicial module obtained from the differentials of an augmented simplicial
algebra and extension of scalars along its augmentation. -/
structure ResolutionCotangentSimplicialModuleData where
  /-- The underlying simplicial `B`-module. -/
  object : SimplicialObject (ModuleCat.{max u v} B)
  /-- Identification of its terms with the base-changed modules of differentials. -/
  termIso : ∀ n, object.obj n ≅ resolutionCotangentTerm A B P ε n
  /-- Its simplicial maps send a pure differential to the pure differential of the image. -/
  map_differential : ∀ {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) (p : P.obj i),
    ((termIso i).inv ≫ object.map f ≫ (termIso j).hom)
      (resolutionCotangentTermDifferential A B P ε i p) =
    resolutionCotangentTermDifferential A B P ε j (P.map f p)

/-- The `Pᵢ`-linear map `Ω[Pᵢ⁄A] → B ⊗[Pⱼ] Ω[Pⱼ⁄A]`, `ω ↦ 1 ⊗ Ω(g)(ω)` (so `d p ↦ 1 ⊗ d (g p)`),
attached to a morphism `g : Pᵢ ⟶ Pⱼ` lying over `B`; it is adjoint to
`resolutionCotangentPush`. -/
noncomputable def resolutionCotangentPushAdjoint {i j : SimplexCategoryᵒᵖ}
    (g : P.obj i ⟶ P.obj j)
    (hg : (resolutionAugmentationHom A B P ε j).comp g.hom.toRingHom =
      resolutionAugmentationHom A B P ε i) :
    ModuleCat.of (P.obj i) (KaehlerDifferential A (P.obj i)) ⟶
      (ModuleCat.restrictScalars (resolutionAugmentationHom A B P ε i)).obj
        (resolutionCotangentTerm A B P ε j) := by
  let R := P.obj i
  let Q := P.obj j
  let : Algebra R Q := g.hom.toRingHom.toAlgebra
  let : Algebra R B := (resolutionAugmentationHom A B P ε i).toAlgebra
  let : Algebra Q B := (resolutionAugmentationHom A B P ε j).toAlgebra
  have : IsScalarTower A R Q :=
    IsScalarTower.of_algebraMap_eq (fun a => (g.hom.commutes a).symm)
  have : IsScalarTower R Q B := IsScalarTower.of_algebraMap_eq' hg.symm
  let M := ModuleCat.of R (KaehlerDifferential A R)
  let N := resolutionCotangentTerm A B P ε j
  let e := resolutionAugmentationHom A B P ε i
  exact ModuleCat.ofHom (X := M) (Y := (ModuleCat.restrictScalars e).obj N)
    { toFun := fun x => (1 : B) ⊗ₜ[Q] (KaehlerDifferential.map A A R Q x)
      map_add' := by
        intro x y
        change (TensorProduct.mk Q B (KaehlerDifferential A Q) 1)
            (KaehlerDifferential.map A A R Q (x + y)) = _
        rw [map_add]
        exact (TensorProduct.mk Q B (KaehlerDifferential A Q) 1).map_add _ _
      map_smul' := by
        intro p x
        change (1 : B) ⊗ₜ[Q] (KaehlerDifferential.map A A R Q (p • x)) =
          e p • ((1 : B) ⊗ₜ[Q] (KaehlerDifferential.map A A R Q x))
        rw [map_smul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        congr 1 }

/-- The `B`-linear map `B ⊗[Pᵢ] Ω[Pᵢ⁄A] → B ⊗[Pⱼ] Ω[Pⱼ⁄A]` induced by a morphism `g : Pᵢ ⟶ Pⱼ`
lying over `B`: the `B`-linear extension of `resolutionCotangentPushAdjoint`. -/
noncomputable def resolutionCotangentPush {i j : SimplexCategoryᵒᵖ} (g : P.obj i ⟶ P.obj j)
    (hg : (resolutionAugmentationHom A B P ε j).comp g.hom.toRingHom =
      resolutionAugmentationHom A B P ε i) :
    resolutionCotangentTerm A B P ε i ⟶ resolutionCotangentTerm A B P ε j :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (resolutionAugmentationHom A B P ε i) (resolutionCotangentPushAdjoint A B P ε g hg)

/-- The value of `resolutionCotangentPush` on the pure differential `1 ⊗ d p`. -/
@[simp]
theorem resolutionCotangentPush_D {i j : SimplexCategoryᵒᵖ} (g : P.obj i ⟶ P.obj j)
    (hg : (resolutionAugmentationHom A B P ε j).comp g.hom.toRingHom =
      resolutionAugmentationHom A B P ε i) (p : P.obj i) :
    resolutionCotangentPush A B P ε g hg (resolutionCotangentTermDifferential A B P ε i p) =
      resolutionCotangentTermDifferential A B P ε j (g p) := by
  have key : resolutionCotangentPush A B P ε g hg
      (resolutionCotangentTermDifferential A B P ε i p) =
      (1 : B) • ((resolutionCotangentPushAdjoint A B P ε g hg)
        (KaehlerDifferential.D A (P.obj i) p) : resolutionCotangentTerm A B P ε j) :=
    ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul
      (X := ModuleCat.of (P.obj i) (KaehlerDifferential A (P.obj i)))
      (Y := resolutionCotangentTerm A B P ε j)
      (resolutionAugmentationHom A B P ε i) (resolutionCotangentPushAdjoint A B P ε g hg)
      (1 : B) (KaehlerDifferential.D A (P.obj i) p)
  rw [key, one_smul]
  let R := P.obj i
  let Q := P.obj j
  let _ : Algebra R Q := g.hom.toRingHom.toAlgebra
  let _ : Algebra R B := (resolutionAugmentationHom A B P ε i).toAlgebra
  let _ : Algebra Q B := (resolutionAugmentationHom A B P ε j).toAlgebra
  have : IsScalarTower A R Q :=
    IsScalarTower.of_algebraMap_eq (fun a => (g.hom.commutes a).symm)
  have : IsScalarTower R Q B := IsScalarTower.of_algebraMap_eq' hg.symm
  change (1 : B) ⊗ₜ[Q] (KaehlerDifferential.map A A R Q (KaehlerDifferential.D A R p)) = _
  rw [KaehlerDifferential.map_D]
  rfl

/-- The simplicial structure map of the simplicial module of differentials:
`resolutionCotangentPush` at a simplicial operator. -/
noncomputable def resolutionCotangentMap {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    resolutionCotangentTerm A B P ε i ⟶ resolutionCotangentTerm A B P ε j :=
  resolutionCotangentPush A B P ε (P.map f) (resolutionAugmentationHom_naturality A B P ε f)

/-- The value of `resolutionCotangentMap` on the pure differential `1 ⊗ d p`. -/
@[simp]
theorem resolutionCotangentMap_D {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) (p : P.obj i) :
    resolutionCotangentMap A B P ε f (resolutionCotangentTermDifferential A B P ε i p) =
      resolutionCotangentTermDifferential A B P ε j (P.map f p) :=
  resolutionCotangentPush_D A B P ε (P.map f)
    (resolutionAugmentationHom_naturality A B P ε f) p

/-- Two `B`-linear maps out of `resolutionCotangentTerm A B P ε i` which agree on every pure
differential `1 ⊗ d p` are equal: the differentials `d p` span `Ω[Pᵢ⁄A]`. -/
theorem resolutionCotangentTerm_hom_ext (i : SimplexCategoryᵒᵖ) {N : ModuleCat.{max u v} B}
    (α β : resolutionCotangentTerm A B P ε i ⟶ N)
    (h : ∀ p : P.obj i, α (resolutionCotangentTermDifferential A B P ε i p) =
      β (resolutionCotangentTermDifferential A B P ε i p)) : α = β :=
  ModuleCat.extendScalars_kaehlerDifferential_hom_ext
    (resolutionAugmentationHom A B P ε i) α β h

/-- The simplicial `B`-module `Ω[P•⁄A] ⊗[P•] B` of an augmented simplicial algebra. -/
noncomputable def resolutionCotangentSimplicialModule :
    ResolutionCotangentSimplicialModuleData A B P ε :=
  { object :=
      { obj := resolutionCotangentTerm A B P ε
        map := fun f => resolutionCotangentMap A B P ε f
        map_id i := resolutionCotangentTerm_hom_ext A B P ε i _ _ fun p => by simp
        map_comp := by
          intro i j k f g
          exact resolutionCotangentTerm_hom_ext A B P ε i _ _ fun p => by simp }
    termIso := fun n => Iso.refl _
    map_differential := by
      intro i j f p
      simp }

theorem resolutionCotangentSimplicialModule_object_obj (n : SimplexCategoryᵒᵖ) :
    (resolutionCotangentSimplicialModule A B P ε).object.obj n =
      resolutionCotangentTerm A B P ε n :=
  rfl

@[simp]
theorem resolutionCotangentSimplicialModule_object_map {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    (resolutionCotangentSimplicialModule A B P ε).object.map f =
      resolutionCotangentMap A B P ε f :=
  rfl

/-- The complex `Ω[P•⁄A] ⊗[P•] B` of an augmented simplicial algebra, with simplicial degree `n`
in cohomological degree `-n`. -/
noncomputable def resolutionCotangentComplex : CochainComplex (ModuleCat.{max u v} B) ℤ :=
  (((AlgebraicTopology.alternatingFaceMapComplex (ModuleCat.{max u v} B)).obj
    (resolutionCotangentSimplicialModule A B P ε).object).extend
      (ComplexShape.embeddingUpIntLE 0))


end CommAlgCat
