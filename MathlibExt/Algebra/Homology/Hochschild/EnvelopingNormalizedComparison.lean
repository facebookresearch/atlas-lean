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
# Normalized Hochschild chains from enveloping bar tensors

Let k be commutative, A an associative unital k-algebra and M a
compatible A-bimodule. With E=A⊗[k]Aᵐᵒᵖ acting on the right of M
by m·(a⊗bᵐᵒᵖ)=bma, tensor the enveloping bar P_n=A⊗[k]A^{⊗(n+1)}.
Its comparison with Hochschild chains followed by normalization is
a quasi-isomorphism F_M(P_*)→N_*(A,M).

On a balanced bar representative, the map has value
[m⊗(a_0⊗a_1⊗⋯⊗a_{n+1})] ↦
(a_{n+1}ma_0)⊗[a_1]⊗⋯⊗[a_n],
where the classes belong to the ground module A/span_k{1}.

If A is projective as a k-module, normalized Hochschild homology
is computed by F_M applied to any projective E-resolution of the
lifted regular E-module A. This agrees with L_n F_M(A).
The coefficient bimodule M is arbitrary.

Reference: J.-L. Loday, Cyclic Homology, §1.1.
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

/-- Let k be commutative, A an associative unital k-algebra and M a
compatible A-bimodule with commuting k-linear left and right actions.
Put E=A⊗[k]Aᵐᵒᵖ and F_M(X)=M⊗_E X using m·(a⊗bᵐᵒᵖ)=bma.
The bar coefficient tensor complex maps to the normalized
Hochschild complex by balanced endpoint cancellation followed by
the factorwise ground-unit quotient. -/
def coefficientTensorNormalizedProjection : coefficientTensorComplex k A M ⟶
    ModuleCat.Algebra.Hochschild.normalizedChainComplex k A M :=
  (coefficientTensorChainIso k A M).hom ≫ ModuleCat.Algebra.Hochschild.normalizationProjection k A M

/-- Let k be commutative, A an associative unital k-algebra and M a
compatible A-bimodule with commuting k-linear left and right actions.
Put E=A⊗[k]Aᵐᵒᵖ and F_M(X)=M⊗_E X using m·(a⊗bᵐᵒᵖ)=bma.
The bar-tensor-to-normalized-chain projection is a quasi-isomorphism,
so it preserves homology in every degree. -/
instance coefficientTensorNormalizedProjection_quasiIso :
    QuasiIso (coefficientTensorNormalizedProjection k A M) := by
  unfold coefficientTensorNormalizedProjection
  infer_instance

/-- Let k be commutative, A an associative unital k-algebra and M a
compatible A-bimodule with commuting k-linear left and right actions.
Put E=A⊗[k]Aᵐᵒᵖ and F_M(X)=M⊗_E X using m·(a⊗bᵐᵒᵖ)=bma.
For a balanced representative in degree n, its normalized value is
[m⊗(a_0⊗⋯⊗a_{n+1})] ↦
(a_{n+1}ma_0)⊗[a_1]⊗⋯⊗[a_n],
with the last factor acting on M on the left and the first on the right. -/
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

/-- Let k be commutative, A an associative unital k-algebra and M a
compatible A-bimodule with commuting k-linear left and right actions.
Put E=A⊗[k]Aᵐᵒᵖ and F_M(X)=M⊗_E X using m·(a⊗bᵐᵒᵖ)=bma.
The bar tensor projection induces a k-module isomorphism
H_n(F_M(P_bar))≅H_n(N_*(A,M)) for every n. -/
def coefficientTensorNormalizedHomologyIso (n : ℕ) :
    (coefficientTensorComplex k A M).homology n ≅
      (ModuleCat.Algebra.Hochschild.normalizedChainComplex k A M).homology n :=
  _root_.isoOfQuasiIsoAt (coefficientTensorNormalizedProjection k A M) n

/-- Let k be commutative, A an associative unital k-algebra and M a
compatible A-bimodule with commuting k-linear left and right actions.
Put E=A⊗[k]Aᵐᵒᵖ and F_M(X)=M⊗_E X using m·(a⊗bᵐᵒᵖ)=bma.
The forward map of H_n(F_M(P_bar))≅H_n(N_*(A,M)) is
homology of the constructed bar-tensor normalization projection. -/
theorem coefficientTensorNormalizedHomologyIso_hom (n : ℕ) :
    (coefficientTensorNormalizedHomologyIso k A M n).hom =
      HomologicalComplex.homologyMap (coefficientTensorNormalizedProjection k A M) n := by
  exact _root_.isoOfQuasiIsoAt_hom (coefficientTensorNormalizedProjection k A M) n

/-- Let k be commutative, A an associative unital k-algebra and M a
compatible A-bimodule with commuting k-linear left and right actions.
Put E=A⊗[k]Aᵐᵒᵖ and F_M(X)=M⊗_E X using m·(a⊗bᵐᵒᵖ)=bma.
If A is projective as a k-module and P is a projective E-resolution
of the lifted regular module A, there is a k-module isomorphism
H_n(N_*(A,M))≅H_n(F_M(P)). -/
def normalizedHochschildHomologyIsoForResolution [Module.Projective k A]
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) (n : ℕ) :
    (ModuleCat.Algebra.Hochschild.normalizedChainComplex k A M).homology n ≅
      (coefficientResolutionTensorComplex k A M P).homology n :=
  (_root_.isoOfQuasiIsoAt (ModuleCat.Algebra.Hochschild.normalizationProjection k A M) n).symm ≪≫
    coefficientHochschildHomologyIsoForResolution k A M P n

/-- Let k be commutative, A an associative unital k-algebra and M a
compatible A-bimodule with commuting k-linear left and right actions.
Put E=A⊗[k]Aᵐᵒᵖ and F_M(X)=M⊗_E X using m·(a⊗bᵐᵒᵖ)=bma.
If A is projective as a k-module, the normalized Hochschild
homology is isomorphic to L_n F_M(A), with A the lifted regular
left E-module. -/
def normalizedHochschildHomologyIsoDerived [Module.Projective k A] (n : ℕ) :
    (ModuleCat.Algebra.Hochschild.normalizedChainComplex k A M).homology n ≅
      ((coefficientTensorFunctor k A M).leftDerived n).obj (regularEnvelopingTarget k A) :=
  (_root_.isoOfQuasiIsoAt (ModuleCat.Algebra.Hochschild.normalizationProjection k A M) n).symm ≪≫
    coefficientHochschildHomologyIsoDerived k A M n

/-- Let k be commutative, A an associative unital k-algebra and M a
compatible A-bimodule with commuting k-linear left and right actions.
Put E=A⊗[k]Aᵐᵒᵖ and F_M(X)=M⊗_E X using m·(a⊗bᵐᵒᵖ)=bma.
If A is projective over k, computing L_n F_M(A) with a
projective E-resolution P after the normalized derived-tensor
isomorphism gives exactly H_n(N_*(A,M))≅H_n(F_M(P)). -/
theorem normalizedHochschildHomologyIsoForResolution_derived [Module.Projective k A]
    (P : ProjectiveResolution (regularEnvelopingTarget k A)) (n : ℕ) :
    (normalizedHochschildHomologyIsoDerived k A M n).hom ≫
        (P.isoLeftDerivedObj (coefficientTensorFunctor k A M) n).hom =
      (normalizedHochschildHomologyIsoForResolution k A M P n).hom := by
  change (_ ≫ (coefficientHochschildHomologyIsoDerived k A M n).hom) ≫ _ = _
  rw [Category.assoc, coefficientHochschildHomologyIsoForResolution_derived]
  rfl

end ModuleCat.Algebra.Hochschild.AdjacentBar
