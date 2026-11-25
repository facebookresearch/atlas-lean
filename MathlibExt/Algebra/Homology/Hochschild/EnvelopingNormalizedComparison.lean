/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.AdjacentBarResolutionComparison
public import MathlibExt.Algebra.Homology.Hochschild.Normalized

/-!
# Normalized Hochschild homology and enveloping resolutions

The enveloping bar tensor comparison followed by factorwise
normalization computes normalized Hochschild homology with
arbitrary bimodule coefficients over commutative ground rings.
Ground projectivity is required when using a projective
enveloping resolution and the derived balanced tensor functor.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct
open MulOpposite

universe u v w

namespace ModuleCat.Algebra.Hochschild.AdjacentBar

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M] [Module Aᵐᵒᵖ M]
  [SMulCommClass A Aᵐᵒᵖ M] [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M]
  [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]

/-- The balanced bar tensor projects to the original normalized Hochschild complex. -/
def coefficientTensorNormalizedProjection : coefficientTensorComplex k A M ⟶
    ModuleCat.Algebra.Hochschild.normalizedChainComplex k A M :=
  (coefficientTensorChainIso k A M).hom ≫ ModuleCat.Algebra.Hochschild.normalizationProjection k A M

/-- The constructed normalized projection is a quasi-isomorphism without ground projectivity. -/
instance coefficientTensorNormalizedProjection_quasiIso :
    QuasiIso (coefficientTensorNormalizedProjection k A M) := by
  unfold coefficientTensorNormalizedProjection
  infer_instance

/-- On representatives the original endpoint actions are retained, and every middle
factor is projected to the original ground-unit quotient. -/
theorem coefficientTensorNormalizedProjection_mk_tprod
    (n : ℕ) (m : M) (a0 : A) (a : Fin (n + 1) → A) :
    letI := EnvelopingCoefficient.rightEnvelopingModule k A M
    letI : Module k (envelopingBarDegree k A n).carrier :=
      Module.compHom _ (algebraMap k (EnvelopingAlgebra k A))
    ((coefficientTensorNormalizedProjection k A M).f n).hom
        (TensorProduct.Balanced.mk k (EnvelopingAlgebra k A) M (envelopingBarDegree k A n).carrier
          m (a0 ⊗ₜ[k] PiTensorProduct.tprod k a)) =
      (op a0 • (a (Fin.last n) • m)) ⊗ₜ[k]
        PiTensorProduct.tprod k (fun i =>
          (ModuleCat.Algebra.Hochschild.unitSubmodule k A).mkQ (Fin.init a i)) := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI : Module k (envelopingBarDegree k A n).carrier :=
    Module.compHom _ (algebraMap k (EnvelopingAlgebra k A))
  let x : (envelopingBarDegree k A n).carrier := a0 ⊗ₜ[k] PiTensorProduct.tprod k a
  let z := TensorProduct.Balanced.mk k (EnvelopingAlgebra k A) M
    (envelopingBarDegree k A n).carrier m x
  have hc : ((coefficientTensorNormalizedProjection k A M).f n).hom =
      (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A M n).hom.comp
        (coefficientTensorLevelEquiv k A M n).toLinearMap := by
    simp only [coefficientTensorNormalizedProjection, HomologicalComplex.comp_f,
      ModuleCat.Algebra.Hochschild.normalizationProjection_f]
    exact (ModuleCat.hom_comp ((coefficientTensorChainIso k A M).hom.f n)
      (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A M n)).trans
        (congrArg (fun g =>
          (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A M n).hom.comp g)
          (coefficientTensorChainIso_hom_f k A M n))
  have hstart := congrArg (fun g => g z) hc
  have he := coefficientTensorLevelEquiv_mk_tprod k A M n m a0 a
  have hn := ModuleCat.Algebra.Hochschild.normalizationLevelMap_tmul_tprod k A M n
    (op a0 • (a (Fin.last n) • m)) (Fin.init a)
  exact hstart.trans
    ((congrArg (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A M n).hom he).trans hn)

/-- Homology of the normalized projection identifies the bar tensor with normalized
Hochschild homology, independently of a resolution hypothesis. -/
def coefficientTensorNormalizedHomologyIso (n : ℕ) :
    (coefficientTensorComplex k A M).homology n ≅
      (ModuleCat.Algebra.Hochschild.normalizedChainComplex k A M).homology n :=
  _root_.isoOfQuasiIsoAt (coefficientTensorNormalizedProjection k A M) n

/-- The forward normalized homology map is the original constructed projection. -/
theorem coefficientTensorNormalizedHomologyIso_hom (n : ℕ) :
    (coefficientTensorNormalizedHomologyIso k A M n).hom =
      HomologicalComplex.homologyMap (coefficientTensorNormalizedProjection k A M) n := by
  exact _root_.isoOfQuasiIsoAt_hom (coefficientTensorNormalizedProjection k A M) n

/-- Normalized Hochschild homology is computed by the tensor of an projective
resolution of the original regular enveloping target. -/
def normalizedHochschildHomologyIsoForResolution [Module.Projective k A]
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) (n : ℕ) :
    (ModuleCat.Algebra.Hochschild.normalizedChainComplex k A M).homology n ≅
      (coefficientResolutionTensorComplex k A M P).homology n :=
  (_root_.isoOfQuasiIsoAt (ModuleCat.Algebra.Hochschild.normalizationProjection k A M) n).symm ≪≫
    coefficientHochschildHomologyIsoForResolution k A M P n

/-- The same original normalized complex computes the derived balanced tensor. -/
def normalizedHochschildHomologyIsoDerived [Module.Projective k A] (n : ℕ) :
    (ModuleCat.Algebra.Hochschild.normalizedChainComplex k A M).homology n ≅
      ((coefficientTensorFunctor k A M).leftDerived n).obj (regularEnvelopingTarget k A) :=
  (_root_.isoOfQuasiIsoAt (ModuleCat.Algebra.Hochschild.normalizationProjection k A M) n).symm ≪≫
    coefficientHochschildHomologyIsoDerived k A M n

/-- Computing the native derived object with the chosen resolution gives exactly the
constructed normalized homology comparison. -/
theorem normalizedHochschildHomologyIsoForResolution_derived [Module.Projective k A]
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) (n : ℕ) :
    (normalizedHochschildHomologyIsoDerived k A M n).hom ≫
        (P.isoLeftDerivedObj (coefficientTensorFunctor k A M) n).hom =
      (normalizedHochschildHomologyIsoForResolution k A M P n).hom := by
  change (_ ≫ (coefficientHochschildHomologyIsoDerived k A M n).hom) ≫ _ = _
  rw [Category.assoc, coefficientHochschildHomologyIsoForResolution_derived]
  rfl

end ModuleCat.Algebra.Hochschild.AdjacentBar
