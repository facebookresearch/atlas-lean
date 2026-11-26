/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.PolynomialAntisymmetrization
public import MathlibExt.Algebra.Homology.Hochschild.DifferentialFormProjection

/-!
# The factorial in polynomial differential-form projection

Let `k` be a commutative ring, `A = k[X_s | s ∈ σ]`, and `M` a compatible symmetric
`A`-module. The free cotangent generator is `dX_s`, and the polynomial exterior comparison
identifies `M ⊗[k] ⋀ⁿ[k](σ →₀ k)` with `M ⊗[A] ⋀ⁿ[A] Ω[A/k]`.

Signed polynomial antisymmetrization `ε_n` maps forms to Hochschild homology. The unscaled
universal-form projection `π_n` satisfies `π_n ∘ ε_n = n! • id` over every commutative base
ring. Equivalently, `π_n` is `n!` times the inverse polynomial exterior comparison. The same
factorial identity holds on tensor representatives before taking homology.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.PolynomialDiagonal

variable (k : Type u) [CommRing k] (σ : Type v)

local notation "A" => MvPolynomial σ k
local notation "V" => (σ →₀ k)
local notation "Ω" => KaehlerDifferential k A

/-- The universal differential of a linear polynomial generator.

The linear polynomial map from `σ →₀ k` followed by the universal derivation is the free
cotangent-generator map, sending a basis variable to `dX_s`. -/
theorem polynomialGenerator_differential :
    (KaehlerDifferential.D k A).toLinearMap.comp (polynomialGeneratorLinear k σ) =
      KaehlerDifferential.mvPolynomialCotangentGenerator k σ := by
  apply (Finsupp.basisSingleOne (R := k) (ι := σ)).ext
  intro i
  simp only [Finsupp.coe_basisSingleOne, LinearMap.comp_apply,
    polynomialGeneratorLinear_single, KaehlerDifferential.mvPolynomialCotangentGenerator_single]
  exact congrFun (Derivation.coeFn_coe (KaehlerDifferential.D k A)) (MvPolynomial.X i)

variable (M : Type w) [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [SMulCommClass k (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k) M]

/-- The form projection of a signed free exterior representative.

For `x ∈ M ⊗[k] ⋀ⁿ[k](σ →₀ k)`, first form its signed polynomial tensor representative and
then apply the coefficient differential-form projection. -/
def freeExteriorFormProjection (n : ℕ) :
    M ⊗[k] (⋀[k]^n V) →ₗ[k] M ⊗[A] (⋀[A]^n Ω) :=
  (Symmetric.coefficientFormProjection k A M n).comp
    (TensorProduct.map LinearMap.id
      (AdjacentBar.exteriorAntisymmetrizationAlong k A V (polynomialGeneratorLinear k σ) n))

/-- The integral factorial law for free exterior form projection.

The projection of signed polynomial antisymmetrization equals `n!` times the coefficient
exterior-form equivalence, as a ground-linear map. -/
theorem freeExteriorFormProjection_factorial (n : ℕ) :
    freeExteriorFormProjection k σ M n =
      n.factorial •
        (KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv k σ M n).toLinearMap.restrictScalars k := by
  let e := KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv k σ M n
  let F : (M ⊗[k] (⋀[k]^n V)) →ₗ[k] M ⊗[A] (⋀[A]^n Ω) := freeExteriorFormProjection k σ M n
  let R : (M ⊗[k] (⋀[k]^n V)) →ₗ[k] M ⊗[A] (⋀[A]^n Ω) := e.toLinearMap.restrictScalars k
  let T := n.factorial • R
  change F = T
  apply TensorProduct.curry_injective
  apply LinearMap.ext
  intro m
  let S : (M ⊗[k] TensorPower k n A) →ₗ[k] M ⊗[A] (⋀[A]^n Ω) :=
    Symmetric.coefficientFormProjection k A M n
  let q : TensorPower k n A →ₗ[k] M ⊗[k] TensorPower k n A :=
    TensorProduct.mk k M (TensorPower k n A) m
  let P : TensorPower k n V →ₗ[k] TensorPower k n A :=
    PiTensorProduct.map (fun _ : Fin n => polynomialGeneratorLinear k σ)
  let b : (⋀[k]^n V) →ₗ[k] TensorPower k n V := TensorPower.exteriorAntisymmetrization k V n
  let G : (⋀[k]^n V) →ₗ[k] TensorPower k n A :=
    AdjacentBar.exteriorAntisymmetrizationAlong k A V (polynomialGeneratorLinear k σ) n
  let qA : (⋀[A]^n Ω) →ₗ[k] M ⊗[A] (⋀[A]^n Ω) :=
    (TensorProduct.mk A M (⋀[A]^n Ω) m).restrictScalars k
  let a : V [⋀^Fin n]→ₗ[k] M ⊗[A] (⋀[A]^n Ω) :=
    qA.compAlternatingMap
      ((Symmetric.differentialWord k A n).compLinearMap (polynomialGeneratorLinear k σ))
  have htail : S.comp (q.comp P) = PiTensorProduct.lift a.toMultilinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod,
      TensorProduct.mk_apply, Symmetric.coefficientFormProjection_tprod, PiTensorProduct.lift.tprod]
    rfl
  let L : TensorPower k n V →ₗ[k] M ⊗[A] (⋀[A]^n Ω) := PiTensorProduct.lift a.toMultilinearMap
  let I : (⋀[k]^n V) →ₗ[k] M ⊗[A] (⋀[A]^n Ω) := exteriorPower.alternatingMapLinearEquiv a
  have h : L.comp b = n.factorial • I :=
    TensorPower.lift_alternating_comp_exteriorAntisymmetrization k V n a
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  let w := exteriorPower.ιMulti k n v
  let t := b w
  let z := m ⊗ₜ[k] w
  have hI : I w = a v :=
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti (R := k) (M := V)
      (N := M ⊗[A] (⋀[A]^n Ω)) (n := n) a v
  have hv : L t = n.factorial • a v :=
    (LinearMap.comp_apply L b w).symm.trans
      ((LinearMap.congr_fun h w).trans ((LinearMap.smul_apply n.factorial I w).trans
        (congrArg (fun z : M ⊗[A] (⋀[A]^n Ω) => n.factorial • z) hI)))
  have hFval : ((TensorProduct.curry F m).compAlternatingMap (exteriorPower.ιMulti k n)) v = F z :=
    (LinearMap.compAlternatingMap_apply (TensorProduct.curry F m) (exteriorPower.ιMulti k n) v).trans
      (TensorProduct.curry_apply F m w)
  have hTval : ((TensorProduct.curry T m).compAlternatingMap (exteriorPower.ιMulti k n)) v = T z :=
    (LinearMap.compAlternatingMap_apply (TensorProduct.curry T m) (exteriorPower.ιMulti k n) v).trans
      (TensorProduct.curry_apply T m w)
  have hFstart : F z = S (m ⊗ₜ[k] G w) :=
    (LinearMap.comp_apply S (TensorProduct.map (LinearMap.id : M →ₗ[k] M) G) z).trans
      (congrArg S (TensorProduct.map_tmul (LinearMap.id : M →ₗ[k] M) G m w))
  have hTvalue : T z = n.factorial • e z :=
    (LinearMap.smul_apply n.factorial R z).trans
      (congrArg (fun a : M ⊗[A] (⋀[A]^n Ω) => n.factorial • a)
        ((LinearMap.restrictScalars_apply k e.toLinearMap z).trans
          (congrFun (LinearEquiv.coe_toLinearMap e) z)))
  have ht : S (q (P t)) = PiTensorProduct.lift a.toMultilinearMap t :=
    ((LinearMap.comp_apply S (q.comp P) t).trans
      (congrArg S (LinearMap.comp_apply q P t))).symm.trans (LinearMap.congr_fun htail t)
  have hG : G w = P t := LinearMap.comp_apply P b w
  have hstart : S (m ⊗ₜ[k] G w) = S (q (P t)) :=
    (congrArg S (TensorProduct.mk_apply m (G w)).symm).trans
      (congrArg (fun z : TensorPower k n A => S (q z)) hG)
  have hg := polynomialGenerator_differential k σ
  have hgen (z : V) : KaehlerDifferential.D k A (polynomialGeneratorLinear k σ z) =
      KaehlerDifferential.mvPolynomialCotangentGenerator k σ z :=
    (congrFun (Derivation.coeFn_coe (KaehlerDifferential.D k A))
      (polynomialGeneratorLinear k σ z)).symm.trans
        ((LinearMap.comp_apply (KaehlerDifferential.D k A).toLinearMap
          (polynomialGeneratorLinear k σ) z).symm.trans (LinearMap.congr_fun hg z))
  have ha : a v = m ⊗ₜ[A] Symmetric.differentialWord k A n
      (fun j => polynomialGeneratorLinear k σ (v j)) :=
    (LinearMap.compAlternatingMap_apply qA
      ((Symmetric.differentialWord k A n).compLinearMap (polynomialGeneratorLinear k σ)) v).trans
        ((congrArg qA (AlternatingMap.compLinearMap_apply (Symmetric.differentialWord k A n)
          (polynomialGeneratorLinear k σ) v)).trans (TensorProduct.mk_apply m _))
  have hword : a v = m ⊗ₜ[A] exteriorPower.ιMulti A n
      (fun j => KaehlerDifferential.D k A (polynomialGeneratorLinear k σ (v j))) :=
    ha.trans (congrArg (fun z : ⋀[A]^n Ω => m ⊗ₜ[A] z)
      (Symmetric.differentialWord_apply k A n (fun j => polynomialGeneratorLinear k σ (v j))))
  have hforms : a v = e (m ⊗ₜ[k] w) :=
    hword.trans ((congrArg (fun a : Fin n → Ω => m ⊗ₜ[A] exteriorPower.ιMulti A n a)
      (funext fun j => hgen (v j))).trans
        (KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv_tmul_ιMulti k σ M n m v).symm)
  have hraw : S (m ⊗ₜ[k] G w) = n.factorial • e z :=
    hstart.trans (ht.trans (hv.trans
      (congrArg (fun z : M ⊗[A] (⋀[A]^n Ω) => n.factorial • z) hforms)))
  exact hFval.trans ((hFstart.trans (hraw.trans hTvalue.symm)).trans hTval.symm)

/-- The factorial value on a free exterior coefficient element.

For every `x ∈ M ⊗[k] ⋀ⁿ[k](σ →₀ k)`, the projected signed representative is `n!` times its
image in `M ⊗[A] ⋀ⁿ[A] Ω[A/k]`. -/
theorem freeExteriorFormProjection_factorial_apply
    (n : ℕ) (x : M ⊗[k] (⋀[k]^n V)) :
    freeExteriorFormProjection k σ M n x =
      n.factorial • KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv k σ M n x :=
  DFunLike.congr_fun (freeExteriorFormProjection_factorial k σ M n) x

/-- The form projection of a signed polynomial homology class.

Applying the coefficient-form homology map to the class of a signed polynomial exterior
representative equals the form projection of that representative before taking homology. -/
theorem coefficientFormHomologyMap_signed_class
    (n : ℕ) (x : M ⊗[k] (⋀[k]^n V)) :
    Symmetric.coefficientDifferentialFormHomologyLinearMap k A M n
      (polynomialAntisymmetricExteriorClass k σ M n x) =
        freeExteriorFormProjection k σ M n x := by
  letI := Symmetric.opModule A M
  letI := Symmetric.actionsComm A M
  letI := Symmetric.kOpComm k A M
  letI := Symmetric.kOpTower k A M
  let C : ChainComplex (ModuleCat.{max u v w} k) ℕ := symmetricCoefficientComplex k σ M
  let H : ChainComplex (ModuleCat.{max u v w} k) ℕ := Symmetric.chainComplex k A M
  let D : ChainComplex (ModuleCat.{max u v w} k) ℕ := Symmetric.coefficientDifferentialFormComplex k A M
  let ε : C ⟶ H := polynomialAntisymmetricCoefficientMap k σ M
  let π : H ⟶ D := Symmetric.coefficientDifferentialFormChainMap k A M
  let z : C.X n ⟶ C.homology n := HomologicalComplex.zeroDifferentialClassMap C n
    (symmetricCoefficientComplex_d_eq_zero k σ M)
  let iC : C.homology n ≅ C.X n := HomologicalComplex.zeroDifferentialHomologyIso C n
    (symmetricCoefficientComplex_d_eq_zero k σ M)
  let iD : D.homology n ≅ D.X n := HomologicalComplex.zeroDifferentialHomologyIso D n
    (Symmetric.coefficientDifferentialFormComplex_d_eq_zero k A M)
  let hε : C.homology n ⟶ H.homology n := HomologicalComplex.homologyMap ε n
  let hπ : H.homology n ⟶ D.homology n := HomologicalComplex.homologyMap π n
  let p : H.homology n ⟶ D.X n := Symmetric.coefficientDifferentialFormHomologyMap k A M n
  have hp : p = hπ ≫ iD.hom := rfl
  have hnat : HomologicalComplex.homologyMap (ε ≫ π) n ≫ iD.hom = iC.hom ≫ (ε ≫ π).f n :=
    HomologicalComplex.zeroDifferentialHomologyIso_naturality (ε ≫ π) n
      (symmetricCoefficientComplex_d_eq_zero k σ M)
      (Symmetric.coefficientDifferentialFormComplex_d_eq_zero k A M)
  have h : (z ≫ hε) ≫ p = (ε ≫ π).f n := by
    calc
      (z ≫ hε) ≫ p = (z ≫ hε) ≫ (hπ ≫ iD.hom) :=
        congrArg (fun a : H.homology n ⟶ D.X n => (z ≫ hε) ≫ a) hp
      _ = (z ≫ (hε ≫ hπ)) ≫ iD.hom := by simp only [Category.assoc]
      _ = (z ≫ HomologicalComplex.homologyMap (ε ≫ π) n) ≫ iD.hom :=
        congrArg (fun a : C.homology n ⟶ D.homology n => (z ≫ a) ≫ iD.hom)
          (HomologicalComplex.homologyMap_comp ε π n).symm
      _ = z ≫ (iC.hom ≫ (ε ≫ π).f n) :=
        (Category.assoc z (HomologicalComplex.homologyMap (ε ≫ π) n) iD.hom).trans
          (congrArg (fun a : C.homology n ⟶ D.X n => z ≫ a) hnat)
      _ = (ε ≫ π).f n :=
        (Category.assoc z iC.hom ((ε ≫ π).f n)).symm.trans
          ((congrArg (fun a : C.X n ⟶ C.X n => a ≫ (ε ≫ π).f n)
            (HomologicalComplex.zeroDifferentialClassMap_homologyIso C n
              (symmetricCoefficientComplex_d_eq_zero k σ M))).trans (Category.id_comp _))
  let E : C.X n ≃ₗ[k] M ⊗[k] (⋀[k]^n V) := symmetricFreeExteriorEquiv k σ M n
  let y : C.X n := E.symm x
  let c : C.X n →ₗ[k] H.homology n := (z ≫ hε).hom
  have hclass : polynomialAntisymmetricExteriorClass k σ M n x = c y :=
    (LinearMap.comp_apply c E.symm.toLinearMap x).trans
      (congrArg c (congrFun (LinearEquiv.coe_toLinearMap E.symm) x))
  have hproj : p.hom (c y) = ((ε ≫ π).f n).hom y :=
    (ModuleCat.comp_apply (z ≫ hε) p y).symm.trans (ConcreteCategory.congr_hom h y)
  let eL : ULift.{u} (M ⊗[A] (⋀[A]^n Ω)) ≃ₗ[k] M ⊗[A] (⋀[A]^n Ω) := ULift.moduleEquiv
  let U : D.X n →ₗ[k] M ⊗[A] (⋀[A]^n Ω) := eL.toLinearMap
  let Uup : (M ⊗[A] (⋀[A]^n Ω)) →ₗ[k] D.X n := eL.symm.toLinearMap
  let S : H.X n →ₗ[k] M ⊗[A] (⋀[A]^n Ω) := Symmetric.coefficientFormProjection k A M n
  let Q : (M ⊗[k] (⋀[k]^n V)) →ₗ[k] H.X n := TensorProduct.map LinearMap.id
    (AdjacentBar.exteriorAntisymmetrizationAlong k A V (polynomialGeneratorLinear k σ) n)
  have hπ : (π.f n).hom = Uup.comp S := rfl
  have hπraw (a : H.X n) : U ((π.f n).hom a) = S a :=
    (congrArg U ((LinearMap.congr_fun hπ a).trans (LinearMap.comp_apply Uup S a))).trans
      ((congrArg U (congrFun (LinearEquiv.coe_toLinearMap eL.symm) (S a))).trans
        ((congrFun (LinearEquiv.coe_toLinearMap eL) (eL.symm (S a))).trans (eL.apply_symm_apply (S a))))
  let EF : C.X n ≃ₗ[k] M ⊗[k] (⋀[k]^n V) := coefficientFreeExteriorEquiv k σ M n
  have hy : EF.symm.toLinearMap x = y := congrFun (LinearEquiv.coe_toLinearMap EF.symm) x
  have hcoords : (ε.f n).hom.comp EF.symm.toLinearMap = Q :=
    polynomialAntisymmetricCoefficientMap_free_coordinates k σ M n
  have hεvalue : (ε.f n).hom y = Q x :=
    (congrArg (ε.f n).hom hy).symm.trans
      ((LinearMap.comp_apply (ε.f n).hom EF.symm.toLinearMap x).symm.trans
        (LinearMap.congr_fun hcoords x))
  have hcomponent : ((ε ≫ π).f n).hom y = (π.f n).hom ((ε.f n).hom y) :=
    ModuleCat.comp_apply (ε.f n) (π.f n) y
  have htail : U (((ε ≫ π).f n).hom y) = freeExteriorFormProjection k σ M n x :=
    (congrArg U hcomponent).trans ((hπraw _).trans
      ((congrArg S hεvalue).trans (LinearMap.comp_apply S Q x).symm))
  have hraw : Symmetric.coefficientDifferentialFormHomologyLinearMap k A M n
      (polynomialAntisymmetricExteriorClass k σ M n x) = U (p.hom (c y)) :=
    (LinearMap.comp_apply U p.hom (polynomialAntisymmetricExteriorClass k σ M n x)).trans
      (congrArg (fun a : H.homology n => U (p.hom a)) hclass)
  exact hraw.trans ((congrArg U hproj).trans htail)

/-- The factorial value of polynomial antisymmetrization followed by form projection.

For a coefficient form `ω` in degree `n`, the unscaled form homology map sends `ε_n(ω)` to `n!
• ω`. -/
theorem coefficientFormHomologyMap_antisymmetrization
    (n : ℕ) (ω : M ⊗[A] (⋀[A]^n Ω)) :
    Symmetric.coefficientDifferentialFormHomologyLinearMap k A M n
      (polynomialAntisymmetrizationHomology k σ M n ω) = n.factorial • ω := by
  let e := KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv k σ M n
  let z := (e.symm.restrictScalars k).toLinearMap ω
  have hz : e z = ω :=
    (congrArg e ((congrFun (LinearEquiv.coe_toLinearMap (e.symm.restrictScalars k)) ω).trans
      (LinearEquiv.restrictScalars_apply k e.symm ω))).trans (e.apply_symm_apply ω)
  have ha : polynomialAntisymmetrizationHomology k σ M n ω =
      polynomialAntisymmetricExteriorClass k σ M n z :=
    LinearMap.comp_apply (polynomialAntisymmetricExteriorClass k σ M n)
      (e.symm.restrictScalars k).toLinearMap ω
  exact (congrArg (Symmetric.coefficientDifferentialFormHomologyLinearMap k A M n) ha).trans
    ((coefficientFormHomologyMap_signed_class k σ M n z).trans
      ((freeExteriorFormProjection_factorial_apply k σ M n z).trans
        (congrArg (fun a : M ⊗[A] (⋀[A]^n Ω) => n.factorial • a) hz)))

/-- The factorial composite of polynomial homology comparison maps.

As ground-linear maps in degree `n`, `π_n ∘ ε_n = n! • id` on the coefficient differential-
form module. -/
theorem coefficientFormHomologyMap_comp_antisymmetrization (n : ℕ) :
    (Symmetric.coefficientDifferentialFormHomologyLinearMap k A M n).comp
        (polynomialAntisymmetrizationHomology k σ M n) =
      n.factorial • (LinearMap.id : M ⊗[A] (⋀[A]^n Ω) →ₗ[k] M ⊗[A] (⋀[A]^n Ω)) := by
  ext ω
  exact coefficientFormHomologyMap_antisymmetrization k σ M n ω

/-- The unscaled form map as a factorial multiple of the polynomial inverse.

The coefficient-form homology map in degree `n` equals `n!` times the inverse polynomial
exterior comparison, over every commutative base ring. -/
theorem coefficientFormHomologyMap_eq_factorial_inverse (n : ℕ) :
    Symmetric.coefficientDifferentialFormHomologyLinearMap k A M n =
      n.factorial • (symmetricHochschildDifferentialFormEquiv k σ M n).toLinearMap := by
  ext z
  let e := polynomialAntisymmetrizationHomologyEquiv k σ M n
  let E := symmetricHochschildDifferentialFormEquiv k σ M n
  obtain ⟨ω, rfl⟩ := e.surjective z
  have he : e ω = polynomialAntisymmetrizationHomology k σ M n ω :=
    (congrFun (LinearEquiv.coe_toLinearMap e) ω).symm.trans
      (LinearMap.congr_fun (polynomialAntisymmetrizationHomologyEquiv_toLinearMap k σ M n) ω)
  have hl : Symmetric.coefficientDifferentialFormHomologyLinearMap k A M n (e ω) = n.factorial • ω :=
    (congrArg (Symmetric.coefficientDifferentialFormHomologyLinearMap k A M n) he).trans
      (coefficientFormHomologyMap_antisymmetrization k σ M n ω)
  have hr : (n.factorial • E.toLinearMap) (e ω) = n.factorial • ω :=
    (LinearMap.smul_apply n.factorial E.toLinearMap (e ω)).trans
      (congrArg (fun a : M ⊗[A] (⋀[A]^n Ω) => n.factorial • a)
        ((congrFun (LinearEquiv.coe_toLinearMap E) (e ω)).trans
          ((congrArg E he).trans (polynomialAntisymmetrizationHomology_coordinates k σ M n ω))))
  exact hl.trans hr.symm

end ModuleCat.Algebra.Hochschild.PolynomialDiagonal
