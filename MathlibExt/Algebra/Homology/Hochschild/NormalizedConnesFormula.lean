/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.NormalizedMixedBicomplex

/-!
# The integral normalized regular Connes operator

Let `k` be a commutative ring and `A` a commutative `k`-algebra. Put `Ā = A / k·1` as a ground
module. The normalized regular Hochschild term is `A ⊗[k] Ā^⊗n`.

The Connes operator first projects the coefficient to `Ā`, joins it to the `n` tail factors,
applies the signed cyclic norm `N_n = 1 + t_n + ⋯ + t_n^n`, and inserts `1 ∈ A` as the new
coefficient. Thus `B_n(a₀ ⊗ ā₁ ⊗ ⋯ ⊗ āₙ) = 1 ⊗ N_n(ā₀ ⊗ ā₁ ⊗ ⋯ ⊗ āₙ)`. This formula is over
the given commutative base ring and uses the ground-unit quotient.
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

/-- The signed-norm formula for normalized regular Connes boundary.

On `A ⊗[k] Ā^⊗n`, project the coefficient to `Ā`, form the `(n+1)`-fold tail tensor, apply its
signed cyclic norm, and insert the unit as the leading coefficient. -/
def normalizedConnesFormula (n : ℕ) :
    A ⊗[k] TensorPower k n Q →ₗ[k] A ⊗[k] TensorPower k (n + 1) Q :=
  (TensorProduct.mk k A (TensorPower k (n + 1) Q) 1).comp
    ((TensorPower.norm k Q n).comp
      ((TensorPower.consEquiv k Q n).toLinearMap.comp (TensorProduct.map q LinearMap.id)))

/-- The normalized Connes boundary as coefficient projection and cyclic norm.

The normalized regular Connes map equals `a₀ ⊗ ā₁ ⊗ ⋯ ⊗ āₙ ↦ 1 ⊗ N_n(ā₀ ⊗ ā₁ ⊗ ⋯ ⊗ āₙ)` over
an arbitrary commutative ground ring. -/
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
