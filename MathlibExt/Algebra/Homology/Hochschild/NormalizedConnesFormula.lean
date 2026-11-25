/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.NormalizedMixedBicomplex

/-!
# Normalized regular Connes formulas

The regular normalized Connes B is
head-unit insertion after the signed
cyclic norm on the quotient factors.
The formula uses the ground-unit quotient
and does not require rational Eulerian
projectors.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k]
  (A : Type v) [CommRing A] [Algebra k A]

local notation "Q" => ModuleCat.Algebra.Hochschild.quotientCarrier k A
local notation "q" => Submodule.mkQ (ModuleCat.Algebra.Hochschild.unitSubmodule k A)

/-- The literal original regular normalized B coordinate, with head-unit and signed norm. -/
def normalizedConnesFormula (n : ℕ) :
    A ⊗[k] TensorPower k n Q →ₗ[k] A ⊗[k] TensorPower k (n + 1) Q :=
  (TensorProduct.mk k A (TensorPower k (n + 1) Q) 1).comp
    ((TensorPower.norm k Q n).comp
      ((TensorPower.consEquiv k Q n).toLinearMap.comp (TensorProduct.map q LinearMap.id)))

/-- The original normalized Connes map has exactly its literal signed norm formula. -/
theorem normalizedConnesBoundary_eq_formula (n : ℕ) :
    (NonUnital.normalizedBoundary k A n).hom = normalizedConnesFormula k A n := by
  let p : A ⊗[k] TensorPower k n A →ₗ[k] A ⊗[k] TensorPower k n Q :=
    (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A n).hom
  let b : A ⊗[k] TensorPower k n Q →ₗ[k] A ⊗[k] TensorPower k (n + 1) Q :=
    (NonUnital.normalizedBoundary k A n).hom
  have hp : Function.Surjective p :=
    (ModuleCat.epi_iff_surjective
      (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A n)).mp inferInstance
  have h : b.comp p = (normalizedConnesFormula k A n).comp p := by
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro m a
    change b (p (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      normalizedConnesFormula k A n (p (m ⊗ₜ[k] PiTensorProduct.tprod k a))
    have hproj : p (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
        m ⊗ₜ[k] PiTensorProduct.tprod k (fun i => q (a i)) :=
      ModuleCat.Algebra.Hochschild.normalizationLevelMap_tmul_tprod k A A n m a
    rw [hproj]
    have hcoord := DFunLike.congr_fun (TensorPower.consEquiv_naturality q n)
      (m ⊗ₜ[k] PiTensorProduct.tprod k a)
    change TensorPower.consEquiv k Q n
        (TensorProduct.map q (TensorPower.quotientMap
          (ModuleCat.Algebra.Hochschild.unitSubmodule k A) n)
            (m ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      TensorPower.quotientMap (ModuleCat.Algebra.Hochschild.unitSubmodule k A) (n + 1)
        (TensorPower.consEquiv k A n (m ⊗ₜ[k] PiTensorProduct.tprod k a)) at hcoord
    simp only [TensorProduct.map_tmul, TensorPower.quotientMap_tprod] at hcoord
    have hB : b (m ⊗ₜ[k] PiTensorProduct.tprod k (fun i => q (a i))) =
        (1 : A) ⊗ₜ[k] TensorPower.norm k Q n
          (TensorPower.quotientMap (ModuleCat.Algebra.Hochschild.unitSubmodule k A) (n + 1)
            (TensorPower.consEquiv k A n (m ⊗ₜ[k] PiTensorProduct.tprod k a))) :=
      (NonUnital.normalizedBoundary_eq_projected_consInsert_norm k A n m a).trans
        (NonUnital.normalizationLevelMap_consInsert_norm k A n _)
    have hFormula : normalizedConnesFormula k A n
        (m ⊗ₜ[k] PiTensorProduct.tprod k (fun i => q (a i))) =
      (1 : A) ⊗ₜ[k] TensorPower.norm k Q n
        (TensorPower.consEquiv k Q n (q m ⊗ₜ[k] PiTensorProduct.tprod k (fun i => q (a i)))) := by
      rfl
    have hc : (1 : A) ⊗ₜ[k] TensorPower.norm k Q n
        (TensorPower.quotientMap (ModuleCat.Algebra.Hochschild.unitSubmodule k A) (n + 1)
          (TensorPower.consEquiv k A n (m ⊗ₜ[k] PiTensorProduct.tprod k a))) =
      (1 : A) ⊗ₜ[k] TensorPower.norm k Q n
        (TensorPower.consEquiv k Q n (q m ⊗ₜ[k] PiTensorProduct.tprod k (fun i => q (a i)))) :=
      congrArg (fun y => (1 : A) ⊗ₜ[k] TensorPower.norm k Q n y) hcoord.symm
    exact hB.trans (hc.trans hFormula.symm)
  change b = normalizedConnesFormula k A n
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := hp y
  exact DFunLike.congr_fun h x

end ModuleCat.Algebra.Hochschild.Symmetric
