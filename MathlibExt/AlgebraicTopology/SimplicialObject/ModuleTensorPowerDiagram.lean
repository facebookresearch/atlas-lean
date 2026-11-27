/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.ModuleTensorDiagram
public import MathlibExt.LinearAlgebra.TensorPower.Cons
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence

/-!
# Simplicial tensor powers and flat comparison

The `q`-fold tensor-power functor on modules over a commutative ring `k` acts on
linear maps by applying the same map in all `q` factors. Applying it degreewise gives
simplicial tensor powers and the natural successor identification
`X ⊗[k] X^⊗q ≅ X^⊗(q+1)`.

The empty tensor power sends every map to an isomorphism, and tensor powers of a
flat module are flat. If a simplicial map induces an alternating-face quasi-isomorphism
and both its source and target have flat modules in every degree, every tensor power
of the map induces an alternating-face quasi-isomorphism.
-/

@[expose] public section
noncomputable section

open CategoryTheory AlgebraicTopology Opposite
open scoped TensorProduct Simplicial

universe u v

namespace CategoryTheory.SimplicialObject.ModuleTensor

variable (k : Type u) [CommRing k]

/--
The functor `M ↦ M^⊗q` whose action on a linear map applies that map to each of
the `q` tensor factors, including the empty tensor power when `q = 0`.
-/
def powerFunctor (q : ℕ) : (ModuleCat.{max u v} k) ⥤ (ModuleCat.{max u v} k) where
  obj M := ModuleCat.of k (TensorPower k q M)
  map f := ModuleCat.ofHom (PiTensorProduct.map (fun _ : Fin q => f.hom))
  map_id M := by
    apply ModuleCat.hom_ext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro a
    change PiTensorProduct.map (fun _ : Fin q => (LinearMap.id : M →ₗ[k] M))
      (PiTensorProduct.tprod k a) = PiTensorProduct.tprod k a
    rw [PiTensorProduct.map_tprod]
    rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro a
    change PiTensorProduct.map (fun _ : Fin q => g.hom.comp f.hom) (PiTensorProduct.tprod k a) =
      PiTensorProduct.map (fun _ : Fin q => g.hom)
        (PiTensorProduct.map (fun _ : Fin q => f.hom) (PiTensorProduct.tprod k a))
    simp only [PiTensorProduct.map_tprod, LinearMap.comp_apply]

/--
The simplicial module `X^⊗q` obtained by taking the `q`-fold tensor power in every
degree and applying each simplicial operator to all factors.
-/
abbrev powerDiagram (q : ℕ) (X : SimplicialObject (ModuleCat.{max u v} k)) :
    SimplicialObject (ModuleCat.{max u v} k) := X ⋙ powerFunctor k q

/--
The simplicial map whose components are the `q`-fold tensor powers of the components
of `f : X → Y`.
-/
abbrev powerMap (q : ℕ) {X Y : SimplicialObject (ModuleCat.{max u v} k)} (f : X ⟶ Y) :
    powerDiagram k q X ⟶ powerDiagram k q Y := Functor.whiskerRight f (powerFunctor k q)

/--
The natural simplicial isomorphism `X ⊗[k] X^⊗q ≅ X^⊗(q+1)`, using the first
coordinate to identify a tensor with one more factor.
-/
def successorIso (q : ℕ) (X : SimplicialObject (ModuleCat.{max u v} k)) :
    diagram k X (powerDiagram k q X) ≅ powerDiagram k (q + 1) X :=
  NatIso.ofComponents (fun i => (TensorPower.consEquiv k (X.obj i) q).toModuleIso) (by
    intro i j θ
    apply ModuleCat.hom_ext
    change (TensorPower.consEquiv k (X.obj j) q).toLinearMap.comp
      (TensorProduct.map (X.map θ).hom (PiTensorProduct.map (fun _ : Fin q => (X.map θ).hom))) =
      (PiTensorProduct.map (fun _ : Fin (q + 1) => (X.map θ).hom)).comp
        (TensorPower.consEquiv k (X.obj i) q).toLinearMap
    exact TensorPower.consEquiv_naturality (X.map θ).hom q)

/--
For a simplicial map `f`, the successor identification commutes with
`f ⊗ f^⊗q` and the tensor-power map `f^⊗(q+1)`.
-/
@[reassoc]
theorem successorIso_naturality (q : ℕ) {X Y : SimplicialObject (ModuleCat.{max u v} k)} (f : X ⟶ Y) :
    map k f (powerMap k q f) ≫ (successorIso k q Y).hom =
      (successorIso k q X).hom ≫ powerMap k (q + 1) f := by
  apply NatTrans.ext
  funext i
  apply ModuleCat.hom_ext
  change (TensorPower.consEquiv k (Y.obj i) q).toLinearMap.comp
    (TensorProduct.map (f.app i).hom (PiTensorProduct.map (fun _ : Fin q => (f.app i).hom))) =
    (PiTensorProduct.map (fun _ : Fin (q + 1) => (f.app i).hom)).comp
      (TensorPower.consEquiv k (X.obj i) q).toLinearMap
  exact TensorPower.consEquiv_naturality (f.app i).hom q

/--
The canonical identification of the degreewise tensor power of the constant diagram
on `M` with the constant diagram on `M^⊗q`.
-/
def powerConstantIso (q : ℕ) (M : (ModuleCat.{max u v} k)) :
    powerDiagram k q ((SimplicialObject.const (ModuleCat.{max u v} k)).obj M) ≅
      (SimplicialObject.const (ModuleCat.{max u v} k)).obj ((powerFunctor k q).obj M) :=
  NatIso.ofComponents (fun i => Iso.refl _) (by
    intro i j θ
    change (powerFunctor k q).map (𝟙 M) ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    rw [CategoryTheory.Functor.map_id])

/--
For a module functor `F`, the simplicial isomorphism between applying `F` to the
constant diagram on `M` and the constant diagram on `F(M)`.
-/
def whiskerConstantIso (F : (ModuleCat.{max u v} k) ⥤ (ModuleCat.{max u v} k)) (M : (ModuleCat.{max u v} k)) :
    ((SimplicialObject.const (ModuleCat.{max u v} k)).obj M) ⋙ F ≅
      (SimplicialObject.const (ModuleCat.{max u v} k)).obj (F.obj M) :=
  NatIso.ofComponents (fun i => Iso.refl _) (by
    intro i j θ
    change F.map (𝟙 M) ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    rw [CategoryTheory.Functor.map_id])

/--
The map induced by any module morphism on the empty tensor power is an isomorphism.
-/
theorem zeroPowerMap_isIso {M N : (ModuleCat.{max u v} k)} (f : M ⟶ N) : IsIso ((powerFunctor k 0).map f) := by
  let e := (TensorPower.zeroEquiv k M).trans (TensorPower.zeroEquiv k N).symm
  let E : (powerFunctor k 0).obj M ≅ (powerFunctor k 0).obj N := e.toModuleIso
  have h : (powerFunctor k 0).map f = E.hom := by
    apply ModuleCat.hom_ext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro a
    change PiTensorProduct.map (fun _ : Fin 0 => f.hom) (PiTensorProduct.tprod k a) =
      e (PiTensorProduct.tprod k a)
    apply (TensorPower.zeroEquiv k N).injective
    rw [PiTensorProduct.map_tprod]
    have he (z : TensorPower k 0 M) :
        e z = (TensorPower.zeroEquiv k N).symm (TensorPower.zeroEquiv k M z) := rfl
    rw [he, LinearEquiv.apply_symm_apply]
    simp only [TensorPower.zeroEquiv, PiTensorProduct.isEmptyEquiv_apply_tprod]
  rw [h]
  infer_instance

/--
Every finite tensor power `M^⊗q` of a flat `k`-module `M` is flat over `k`, including
the empty tensor power.
-/
theorem power_flat (M : (ModuleCat.{max u v} k)) [Module.Flat k M] (q : ℕ) : Module.Flat k (TensorPower k q M) := by
  induction q with
  | zero =>
      exact Module.Flat.of_linearEquiv (TensorPower.zeroEquiv k M)
  | succ q ih =>
      letI := ih
      letI : Module.Flat k (M ⊗[k] TensorPower k q M) := inferInstance
      exact Module.Flat.of_linearEquiv (TensorPower.consEquiv k M q).symm

/--
If a simplicial map is an alternating-face quasi-isomorphism and every source and
target degree is flat over `k`, each of its tensor powers is an alternating-face
quasi-isomorphism.
-/
theorem quasiIso_powerMap {X Y : SimplicialObject (ModuleCat.{max u v} k)} (f : X ⟶ Y)
    (hf : QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).map f))
    (hX : ∀ p : ℕ, Module.Flat k (X.obj (op ⦋p⦌)))
    (hY : ∀ p : ℕ, Module.Flat k (Y.obj (op ⦋p⦌))) (q : ℕ) :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).map (powerMap k q f)) := by
  induction q with
  | zero =>
      letI (i : SimplexCategoryᵒᵖ) : IsIso ((powerMap k 0 f).app i) :=
        zeroPowerMap_isIso k (f.app i)
      letI : IsIso (powerMap k 0 f) := NatIso.isIso_of_isIso_app (powerMap k 0 f)
      infer_instance
  | succ q ih =>
      have hPX : ∀ p : ℕ, Module.Flat k ((powerDiagram k q X).obj (op ⦋p⦌)) := by
        intro p
        letI := hX p
        exact power_flat k _ q
      let A := alternatingFaceMapComplex (ModuleCat.{max u v} k)
      letI : QuasiIso (A.map (map k f (powerMap k q f))) := quasiIso_map k f _ hf ih hPX hY
      have e := congrArg (fun t => A.map t) (successorIso_naturality k q f)
      rw [A.map_comp, A.map_comp] at e
      have h : QuasiIso (A.map (map k f (powerMap k q f)) ≫ A.map (successorIso k q Y).hom) :=
        inferInstance
      rw [e] at h
      letI := h
      exact quasiIso_of_comp_left (A.map (successorIso k q X).hom) (A.map (powerMap k (q + 1) f))

/--
A simplicial map inducing a quasi-isomorphism of normalized Moore complexes also
induces a quasi-isomorphism of alternating-face complexes.
-/
theorem quasiIso_alternating_of_normalized {X Y : SimplicialObject (ModuleCat.{max u v} k)} (f : X ⟶ Y)
    (hf : QuasiIso ((normalizedMooreComplex (ModuleCat.{max u v} k)).map f)) :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).map f) := by
  letI := hf
  letI : QuasiIso (inclusionOfMooreComplexMap X) :=
    (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := X)).quasiIso_hom
  letI : QuasiIso (inclusionOfMooreComplexMap Y) :=
    (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := Y)).quasiIso_hom
  have h : QuasiIso
      ((normalizedMooreComplex (ModuleCat.{max u v} k)).map f ≫ inclusionOfMooreComplexMap Y) :=
    inferInstance
  have e := (inclusionOfMooreComplex (ModuleCat.{max u v} k)).naturality f
  dsimp only [inclusionOfMooreComplex] at e
  rw [e] at h
  letI := h
  exact quasiIso_of_comp_left (inclusionOfMooreComplexMap X) ((alternatingFaceMapComplex (ModuleCat.{max u v} k)).map f)

end CategoryTheory.SimplicialObject.ModuleTensor
