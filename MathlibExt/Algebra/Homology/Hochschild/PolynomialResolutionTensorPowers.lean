/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor.Exact
public import MathlibExt.AlgebraicTopology.SimplicialObject.ModuleTensorPowerDiagram
public import MathlibExt.Algebra.Category.CommAlgCat.PolynomialResolutionAdditiveAsphericity
public import MathlibExt.AlgebraicTopology.SimplicialObject.AugmentationQuasiIso

/-!
# Tensor-power augmentations of a polynomial resolution

Let `k` be a commutative ring and `B` a commutative `k`-algebra. The underlying
module diagram of the canonical polynomial resolution has an additively aspherical
augmentation to `B`, and every simplicial degree is flat over `k`.

Taking degreewise tensor powers gives augmentations to `B^⊗q` whose pure-tensor maps
apply the polynomial augmentation to each factor. If `B` is flat over `k`, these maps
are quasi-isomorphisms of alternating-face complexes. The same flatness gives the
coefficient-first augmentation `B ⊗[k] P^⊗q → const (B ⊗[k] B^⊗q)` as a
quasi-isomorphism. The ground-ring and algebra-carrier universes are independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory Opposite AlgebraicTopology
open scoped TensorProduct Simplicial

universe u v

namespace ModuleCat.Algebra.Hochschild.AndreQuillenResolution

open CategoryTheory.SimplicialObject.ModuleTensor

variable (k : Type u) [CommRing k] (B : CommAlgCat.{max u v} k)

/--
The augmented simplicial `k`-module obtained from the canonical polynomial
resolution of `B` by forgetting the algebra structure.
-/
abbrev additiveResolution : SimplicialObject.Augmented (ModuleCat.{max u v} k) :=
  CommAlgCat.polynomialAdditiveResolution k B

/--
The underlying `k`-module of the augmentation target `B`.
-/
abbrev coefficientModule : (ModuleCat.{max u v} k) := (additiveResolution k B).right

/--
The simplicial `k`-module diagram of the canonical polynomial resolution of `B`.
-/
abbrev additiveDiagram : SimplicialObject (ModuleCat.{max u v} k) := (additiveResolution k B).left

/--
The coefficient module of the augmented polynomial resolution is `ModuleCat.of k B`.
-/
theorem coefficientModule_eq : coefficientModule k B = ModuleCat.of k B := rfl

/--
The simplicial module augmentation from the polynomial resolution diagram to the
constant diagram on the underlying module of `B`.
-/
abbrev additiveAugmentation : additiveDiagram k B ⟶
    (SimplicialObject.const (ModuleCat.{max u v} k)).obj (coefficientModule k B) := (additiveResolution k B).hom

/--
The underlying polynomial augmentation induces a quasi-isomorphism of
alternating-face complexes, for every commutative `k`-algebra `B`.
-/
theorem additiveAugmentation_quasiIso :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).map (additiveAugmentation k B)) := by
  apply quasiIso_alternating_of_normalized k (additiveAugmentation k B)
  exact ModuleResolutionAsphericity.normalizationMap_quasiIso (additiveResolution k B)
    (CommAlgCat.polynomialAdditiveResolution_condition k B)

/--
Every simplicial degree of the underlying polynomial resolution is flat over `k`,
via its polynomial presentation and the freeness of a polynomial algebra as a module.
-/
theorem additiveDiagram_flat (p : ℕ) : Module.Flat k ((additiveDiagram k B).obj (op ⦋p⦌)) := by
  let e := CommAlgCat.polynomialResolutionObjIso k B p
  letI : Module.Flat k (MvPolynomial ((CommAlgCat.polynomialPower k p).obj B) k) := inferInstance
  exact Module.Flat.of_linearEquiv (CommAlgCat.algEquivOfIso e).toLinearEquiv

/--
The simplicial diagram whose degree-`p` term is the `q`-fold tensor power over `k`
of the underlying polynomial resolution term `P_p`.
-/
abbrev tensorPowerDiagram (q : ℕ) : SimplicialObject (ModuleCat.{max u v} k) := powerDiagram k q (additiveDiagram k B)

/--
The simplicial augmentation from the degreewise tensor-power diagram `P^⊗q` to the
constant diagram on `B^⊗q`, obtained by applying the polynomial augmentation to each
factor.
-/
def tensorPowerAugmentation (q : ℕ) : tensorPowerDiagram k B q ⟶
    (SimplicialObject.const (ModuleCat.{max u v} k)).obj ((powerFunctor k q).obj (coefficientModule k B)) :=
  powerMap k q (additiveAugmentation k B) ≫ (powerConstantIso k q (coefficientModule k B)).hom

/--
In each simplicial degree, the tensor-power augmentation sends `⊗_j a_j` to
`⊗_j ε(a_j)`, with the original order of the `q` factors.
-/
theorem tensorPowerAugmentation_tprod (q : ℕ) (i : SimplexCategoryᵒᵖ)
    (a : Fin q → (additiveDiagram k B).obj i) :
    ((tensorPowerAugmentation k B q).app i).hom (PiTensorProduct.tprod k a) =
      PiTensorProduct.tprod k (fun j => ((additiveAugmentation k B).app i).hom (a j)) := by
  change PiTensorProduct.map (fun _ : Fin q => ((additiveAugmentation k B).app i).hom)
    (PiTensorProduct.tprod k a) = _
  rw [PiTensorProduct.map_tprod]

section Flat

variable [Module.Flat k B]

/--
If `B` is flat over `k`, the tensor-power polynomial augmentation induces a
quasi-isomorphism of alternating-face complexes for every tensor power `q`.
-/
theorem tensorPowerAugmentation_quasiIso (q : ℕ) :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).map (tensorPowerAugmentation k B q)) := by
  have htarget : ∀ p : ℕ, Module.Flat k
      (((SimplicialObject.const (ModuleCat.{max u v} k)).obj (coefficientModule k B)).obj (op ⦋p⦌)) := by
    intro p
    change Module.Flat k B
    infer_instance
  letI : QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).map
      (powerMap k q (additiveAugmentation k B))) :=
    quasiIso_powerMap k (additiveAugmentation k B) (additiveAugmentation_quasiIso k B)
      (additiveDiagram_flat k B) htarget q
  unfold tensorPowerAugmentation
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

end Flat

/--
The simplicial diagram `B ⊗[k] P^⊗q`, with the underlying module of `B` as its
first tensor factor.
-/
abbrev coefficientTensorDiagram (q : ℕ) : SimplicialObject (ModuleCat.{max u v} k) :=
  tensorPowerDiagram k B q ⋙ (ModuleCat.tensorBifunctorAt.{u, max u v, max u v} k).obj (coefficientModule k B)

/--
The underlying ground-ring module `B ⊗[k] B^⊗q`, with the regular coefficient
module `B` as the first factor.
-/
abbrev coefficientTarget (q : ℕ) : (ModuleCat.{max u v} k) :=
  ((ModuleCat.tensorBifunctorAt.{u, max u v, max u v} k).obj (coefficientModule k B)).obj
    ((powerFunctor k q).obj (coefficientModule k B))

/--
The simplicial augmentation `B ⊗[k] P^⊗q → const (B ⊗[k] B^⊗q)`, preserving the
coefficient factor and applying the polynomial augmentation to each tail factor.
-/
def coefficientTensorAugmentation (q : ℕ) : coefficientTensorDiagram k B q ⟶
    (SimplicialObject.const (ModuleCat.{max u v} k)).obj (coefficientTarget k B q) :=
  Functor.whiskerRight (tensorPowerAugmentation k B q)
      ((ModuleCat.tensorBifunctorAt.{u, max u v, max u v} k).obj (coefficientModule k B)) ≫
    (whiskerConstantIso k ((ModuleCat.tensorBifunctorAt.{u, max u v, max u v} k).obj (coefficientModule k B))
      ((powerFunctor k q).obj (coefficientModule k B))).hom

/--
If `B` is flat over `k`, the coefficient-first polynomial tensor augmentation is a
quasi-isomorphism on alternating-face complexes in every tensor-power degree `q`.
-/
theorem coefficientTensorAugmentation_quasiIso [Module.Flat k B] (q : ℕ) :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).map (coefficientTensorAugmentation k B q)) := by
  let F : ModuleCat.{max u v} k ⥤ ModuleCat.{max u v} k :=
    (ModuleCat.tensorBifunctorAt.{u, max u v, max u v} k).obj (coefficientModule k B)
  letI : Module.Flat k (coefficientModule k B) := by change Module.Flat k B; infer_instance
  letI : F.PreservesHomology :=
    ModuleCat.tensorBifunctorAt_obj_preservesHomology.{u, max u v, max u v} k (coefficientModule k B)
  let α : coefficientTensorDiagram k B q ⟶
      (SimplicialObject.const (ModuleCat.{max u v} k)).obj
        ((powerFunctor k q).obj (coefficientModule k B)) ⋙ F :=
    Functor.whiskerRight (tensorPowerAugmentation k B q) F
  let β : (SimplicialObject.const (ModuleCat.{max u v} k)).obj
        ((powerFunctor k q).obj (coefficientModule k B)) ⋙ F ⟶
      (SimplicialObject.const (ModuleCat.{max u v} k)).obj (coefficientTarget k B q) :=
    (whiskerConstantIso k F ((powerFunctor k q).obj (coefficientModule k B))).hom
  letI : QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).map α) :=
    quasiIso_alternatingWhisker k F _ (tensorPowerAugmentation_quasiIso k B q)
  letI : IsIso β := by dsimp only [β]; infer_instance
  have hmap := (alternatingFaceMapComplex (ModuleCat.{max u v} k)).map_comp α β
  have hq : QuasiIso
      ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).map α ≫
        (alternatingFaceMapComplex (ModuleCat.{max u v} k)).map β) := inferInstance
  exact hmap.symm ▸ hq

end ModuleCat.Algebra.Hochschild.AndreQuillenResolution
