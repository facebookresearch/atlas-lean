/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.DifferentialFormProjection
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEnvelopingBarComparison

/-!
# Coefficient naturality of the differential-form projection

Let k be a commutative ring, A a commutative unital k-algebra,
and M,N compatible A-modules. For an A-linear map f : M → N,
the tensor map f ⊗ id on Hochschild words and the map f ⊗ id on
M ⊗_A Ω^n_{A/k} satisfy
(f ⊗ id_Ω) φ_M = φ_N (f ⊗ id_{A^{⊗n}}).
The underlying source and target coefficient universes are independent
in this linear-map statement.

For coefficients M,P in one carrier universe w, these maps define
chain maps in ModuleCat over k at max{u,v,w}. The form complex has
terms ULift.{u}(M ⊗_A Ω^n_{A/k}) and differential zero. Its map sends
the lift of m ⊗ ω to the lift of f(m) ⊗ ω. The corresponding chain
projection and homology projection squares commute.

Reference: J.-L. Loday, Cyclic Homology, §3.2.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w w'

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  {M : Type w} {N : Type w'} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N] [Module A M] [Module A N]
  [SMulCommClass k A M] [SMulCommClass k A N]
  [IsScalarTower k A M] [IsScalarTower k A N]

local notation "Ω" => KaehlerDifferential k A

/-- Let k be commutative, A a commutative unital k-algebra, M,N
compatible A-modules in independent carrier universes, and f : M → N
A-linear. With Ω^n = ∧_A^n Ω_{A/k}, the form projections satisfy
(f ⊗_A id_Ω) φ_M = φ_N (f ⊗_k id_{A^{⊗n}})
as k-linear maps from M ⊗[k] A^{⊗n} to N ⊗_A Ω^n. -/
theorem coefficientFormProjection_coefficient (f : M →ₗ[A] N) (n : ℕ) :
    ((TensorProduct.map f (LinearMap.id : (⋀[A]^n Ω) →ₗ[A] (⋀[A]^n Ω))).restrictScalars k).comp
        (coefficientFormProjection k A M n) =
      (coefficientFormProjection k A N n).comp
        (TensorProduct.map (f.restrictScalars k) (LinearMap.id : TensorPower k n A →ₗ[k] TensorPower k n A)) := by
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    TensorProduct.map_tmul, LinearMap.id_apply, coefficientFormProjection_tprod]

section CommonWorld

variable {P : Type w} [AddCommGroup P] [Module k P] [Module A P]
  [SMulCommClass k A P] [IsScalarTower k A P]

/-- Let k be a commutative ring, A a commutative unital k-algebra,
and M,P compatible A-modules in the same coefficient universe w.
Put Ω^n = ∧_A^n Ω_{A/k}, and let f : M → P be A-linear.
The coefficient form complexes have degree-n terms
ULift.{u}(M ⊗_A Ω^n) and ULift.{u}(P ⊗_A Ω^n), with zero
differentials. The maps up ∘ (f ⊗_A id) ∘ down define a chain
map between them. -/
def coefficientDifferentialFormComplexMap (f : M →ₗ[A] P) :
    coefficientDifferentialFormComplex k A M ⟶ coefficientDifferentialFormComplex k A P where
  f n := ModuleCat.ofHom
    ((ULift.moduleEquiv : ULift.{u} (P ⊗[A] (⋀[A]^n Ω)) ≃ₗ[k]
      P ⊗[A] (⋀[A]^n Ω)).symm.toLinearMap.comp
        (((TensorProduct.map f (LinearMap.id : (⋀[A]^n Ω) →ₗ[A] (⋀[A]^n Ω))).restrictScalars k).comp
          (ULift.moduleEquiv : ULift.{u} (M ⊗[A] (⋀[A]^n Ω)) ≃ₗ[k]
            M ⊗[A] (⋀[A]^n Ω)).toLinearMap))
  comm' i j _h := by
    rw [coefficientDifferentialFormComplex_d_eq_zero,
      coefficientDifferentialFormComplex_d_eq_zero]
    erw [CategoryTheory.Limits.comp_zero]

/-- Let k be a commutative ring, A a commutative unital k-algebra,
and M,P compatible A-modules in the same coefficient universe w.
Put Ω^n = ∧_A^n Ω_{A/k}, and let f : M → P be A-linear.
The degree-n component of the form-complex map is the full k-linear
operator up ∘ (f ⊗_A id_{Ω^n}) ∘ down on the lifted form
objects. -/
theorem coefficientDifferentialFormComplexMap_f (f : M →ₗ[A] P) (n : ℕ) :
    ((coefficientDifferentialFormComplexMap k A f).f n).hom =
      (ULift.moduleEquiv : ULift.{u} (P ⊗[A] (⋀[A]^n Ω)) ≃ₗ[k]
        P ⊗[A] (⋀[A]^n Ω)).symm.toLinearMap.comp
          (((TensorProduct.map f (LinearMap.id : (⋀[A]^n Ω) →ₗ[A] (⋀[A]^n Ω))).restrictScalars k).comp
            (ULift.moduleEquiv : ULift.{u} (M ⊗[A] (⋀[A]^n Ω)) ≃ₗ[k]
              M ⊗[A] (⋀[A]^n Ω)).toLinearMap) := rfl

/-- Let k be a commutative ring, A a commutative unital k-algebra,
and M,P compatible A-modules in the same coefficient universe w.
Put Ω^n = ∧_A^n Ω_{A/k}, and let f : M → P be A-linear.
The degree-n component of the Hochschild coefficient chain map is
f ⊗_k id_{A^{⊗n}}, after restricting f to a k-linear map. -/
theorem symmetricOriginalCoefficientChainMap_tensor (f : M →ₗ[A] P) (n : ℕ) :
    ((symmetricOriginalCoefficientChainMap k A M f).f n).hom =
      TensorProduct.map (f.restrictScalars k)
        (LinearMap.id : TensorPower k n A →ₗ[k] TensorPower k n A) := by
  rw [symmetricOriginalCoefficientChainMap_f]
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  simp only [LinearMap.restrictScalars_apply, algebraCoefficientLevelMap_tmul,
    TensorProduct.map_tmul, LinearMap.id_apply]

/-- Let k be a commutative ring, A a commutative unital k-algebra,
and M,P compatible A-modules in the same coefficient universe w.
Put Ω^n = ∧_A^n Ω_{A/k}, and let f : M → P be A-linear.
Let C(f) be the Hochschild coefficient chain map, F(f) the map of
zero-differential form complexes, and η_M,η_P their form projections.
The chain square is η_P C(f) = F(f) η_M. -/
@[reassoc]
theorem coefficientDifferentialFormChainMap_coefficient (f : M →ₗ[A] P) :
    symmetricOriginalCoefficientChainMap k A M f ≫ coefficientDifferentialFormChainMap k A P =
      coefficientDifferentialFormChainMap k A M ≫ coefficientDifferentialFormComplexMap k A f := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp]
  apply ModuleCat.Algebra.Hochschild.tensorPower_ext
  intro m a
  let word := m ⊗ₜ[k] PiTensorProduct.tprod k a
  have hhead : ((symmetricOriginalCoefficientChainMap k A M f).f n).hom word =
      f m ⊗ₜ[k] PiTensorProduct.tprod k a := by
    exact (LinearMap.congr_fun (symmetricOriginalCoefficientChainMap_tensor k A f n) word).trans
      ((TensorProduct.map_tmul (f.restrictScalars k)
        (LinearMap.id : TensorPower k n A →ₗ[k] TensorPower k n A) m
          (PiTensorProduct.tprod k a)).trans (by rfl))
  have hleft := (LinearMap.comp_apply
    ((coefficientDifferentialFormChainMap k A P).f n).hom
    ((symmetricOriginalCoefficientChainMap k A M f).f n).hom word).trans
      ((congrArg ((coefficientDifferentialFormChainMap k A P).f n).hom hhead).trans
        (coefficientDifferentialFormChainMap_tprod k A P n (f m) a))
  let raw : M ⊗[A] (⋀[A]^n Ω) →ₗ[k] P ⊗[A] (⋀[A]^n Ω) :=
    (TensorProduct.map f (LinearMap.id : (⋀[A]^n Ω) →ₗ[A] (⋀[A]^n Ω))).restrictScalars k
  have hup (x : M ⊗[A] (⋀[A]^n Ω)) :
      ((coefficientDifferentialFormComplexMap k A f).f n).hom (ULift.up x) =
        ULift.up (raw x) := rfl
  have hraw : raw (m ⊗ₜ[A] exteriorPower.ιMulti A n
      (fun j => KaehlerDifferential.D k A (a j))) =
        f m ⊗ₜ[A] exteriorPower.ιMulti A n
          (fun j => KaehlerDifferential.D k A (a j)) := by
    simp only [raw, LinearMap.restrictScalars_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  have hright := (LinearMap.comp_apply
    ((coefficientDifferentialFormComplexMap k A f).f n).hom
    ((coefficientDifferentialFormChainMap k A M).f n).hom word).trans
      ((congrArg ((coefficientDifferentialFormComplexMap k A f).f n).hom
        (coefficientDifferentialFormChainMap_tprod k A M n m a)).trans
          ((hup _).trans (congrArg ULift.up hraw)))
  exact hleft.trans hright.symm

/-- Let k be a commutative ring, A a commutative unital k-algebra,
and M,P compatible A-modules in the same coefficient universe w.
Put Ω^n = ∧_A^n Ω_{A/k}, and let f : M → P be A-linear.
The degree-n map of coefficient form objects sends
ULift(m ⊗_A ω) to ULift(f(m) ⊗_A ω), extended k-linearly.
Its source and target lie in the common module universe max{u,v,w}. -/
def coefficientDifferentialFormObjectMap (f : M →ₗ[A] P) (n : ℕ) :
    ModuleCat.of k (ULift.{u} (M ⊗[A] (⋀[A]^n Ω))) ⟶
      ModuleCat.of k (ULift.{u} (P ⊗[A] (⋀[A]^n Ω))) :=
  (coefficientDifferentialFormComplexMap k A f).f n

/-- Let k be a commutative ring, A a commutative unital k-algebra,
and M,P compatible A-modules in the same coefficient universe w.
Put Ω^n = ∧_A^n Ω_{A/k}, and let f : M → P be A-linear.
For the induced form maps η^H_M,η^H_P on Hochschild homology,
the degree-n square is
η^H_P H_n(C(f)) = F_n(f) η^H_M,
where F_n(f) acts by f on the lifted coefficient and fixes the form. -/
@[reassoc]
theorem coefficientDifferentialFormHomologyMap_coefficient (f : M →ₗ[A] P) (n : ℕ) :
    HomologicalComplex.homologyMap (symmetricOriginalCoefficientChainMap k A M f) n ≫
        coefficientDifferentialFormHomologyMap k A P n =
      coefficientDifferentialFormHomologyMap k A M n ≫ coefficientDifferentialFormObjectMap k A f n := by
  have h := congrArg (fun g => HomologicalComplex.homologyMap g n)
    (coefficientDifferentialFormChainMap_coefficient k A f)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h
  have hnat := HomologicalComplex.zeroDifferentialHomologyIso_naturality
    (coefficientDifferentialFormComplexMap k A f) n
    (coefficientDifferentialFormComplex_d_eq_zero k A M)
    (coefficientDifferentialFormComplex_d_eq_zero k A P)
  unfold coefficientDifferentialFormHomologyMap coefficientDifferentialFormObjectMap
  let a := HomologicalComplex.homologyMap (symmetricOriginalCoefficientChainMap k A M f) n
  let b := HomologicalComplex.homologyMap (coefficientDifferentialFormChainMap k A P) n
  let c := HomologicalComplex.homologyMap (coefficientDifferentialFormChainMap k A M) n
  let d := HomologicalComplex.homologyMap (coefficientDifferentialFormComplexMap k A f) n
  let qM := (HomologicalComplex.zeroDifferentialHomologyIso (coefficientDifferentialFormComplex k A M) n
    (coefficientDifferentialFormComplex_d_eq_zero k A M)).hom
  let qP := (HomologicalComplex.zeroDifferentialHomologyIso (coefficientDifferentialFormComplex k A P) n
    (coefficientDifferentialFormComplex_d_eq_zero k A P)).hom
  let F := (coefficientDifferentialFormComplexMap k A f).f n
  exact (Category.assoc a b qP).symm.trans
    ((congrArg (fun g : (chainComplex k A M).homology n ⟶
      (coefficientDifferentialFormComplex k A P).homology n => g ≫ qP) h).trans
        ((Category.assoc c d qP).trans
          ((congrArg (fun g : (coefficientDifferentialFormComplex k A M).homology n ⟶
            (coefficientDifferentialFormComplex k A P).X n => c ≫ g) hnat).trans
              (Category.assoc c qM F).symm)))

end CommonWorld

end ModuleCat.Algebra.Hochschild.Symmetric
