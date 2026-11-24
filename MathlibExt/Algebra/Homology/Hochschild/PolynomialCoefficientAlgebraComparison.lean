/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.PolynomialDiagonalAlgebraHomotopy
public import MathlibExt.Algebra.Homology.Hochschild.DifferentialFormAlgebraNaturality
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.Along

/-!
# Polynomial change of algebra with symmetric coefficients

The original coefficient tensor functor carries the augmentation homotopy
through an scalar-changing balanced coefficient map. Native Bar
cancellation gives the original coefficient-first Hochschild algebra map.
Thus the signed polynomial comparison is natural up to a chain
homotopy for arbitrary compatible symmetric coefficient maps.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.PolynomialDiagonal

variable (k : Type u) [CommRing k] {σ τ : Type v}
  {M N : Type w} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N]
  [Module (MvPolynomial σ k) M] [Module (MvPolynomial τ k) N]
  [SMulCommClass k (MvPolynomial σ k) M]
  [SMulCommClass k (MvPolynomial τ k) N]
  [IsScalarTower k (MvPolynomial σ k) M]
  [IsScalarTower k (MvPolynomial τ k) N]
  (g : MvPolynomial σ k →ₐ[k] MvPolynomial τ k) (f : M →ₗ[k] N)
  (hf : ∀ a m, f (a • m) = g a • f m)

local notation "AS" => MvPolynomial σ k
local notation "AT" => MvPolynomial τ k
local notation "ES" => MvPolynomial.PolynomialEnveloping k σ
local notation "ET" => MvPolynomial.PolynomialEnveloping k τ
local notation "φ" => MvPolynomial.polynomialEnvelopingMap k τ g
local notation "R" => ModuleCat.restrictScalars (AlgHom.toRingHom φ)
local notation "TM" => AdjacentBar.coefficientTensorFunctor k AS M
local notation "TN" => AdjacentBar.coefficientTensorFunctor k AT N
local notation "TMc" => Functor.mapHomologicalComplex TM (ComplexShape.down ℕ)
local notation "TNc" => Functor.mapHomologicalComplex TN (ComplexShape.down ℕ)

/-- The source coefficient has its canonical symmetric opposite action. -/
local instance polynomialCoefficientSourceOpModule :
    Module ASᵐᵒᵖ M :=
  Symmetric.opModule AS M
/-- The original source left and opposite actions commute. -/
local instance polynomialCoefficientSourceActionsComm :
    SMulCommClass AS ASᵐᵒᵖ M :=
  Symmetric.actionsComm AS M
/-- The source opposite action commutes with the original ground action. -/
local instance polynomialCoefficientSourceGroundOpComm :
    SMulCommClass k ASᵐᵒᵖ M :=
  Symmetric.kOpComm k AS M
/-- The source opposite action retains the original ground scalar tower. -/
local instance polynomialCoefficientSourceGroundOpTower :
    IsScalarTower k ASᵐᵒᵖ M :=
  Symmetric.kOpTower k AS M
/-- The target coefficient has its canonical symmetric opposite action. -/
local instance polynomialCoefficientTargetOpModule :
    Module ATᵐᵒᵖ N :=
  Symmetric.opModule AT N
/-- The original target left and opposite actions commute. -/
local instance polynomialCoefficientTargetActionsComm :
    SMulCommClass AT ATᵐᵒᵖ N :=
  Symmetric.actionsComm AT N
/-- The target opposite action commutes with the original ground action. -/
local instance polynomialCoefficientTargetGroundOpComm :
    SMulCommClass k ATᵐᵒᵖ N :=
  Symmetric.kOpComm k AT N
/-- The target opposite action retains the original ground scalar tower. -/
local instance polynomialCoefficientTargetGroundOpTower :
    IsScalarTower k ATᵐᵒᵖ N :=
  Symmetric.kOpTower k AT N
/-- The source coefficient carries the right enveloping action. -/
local instance polynomialCoefficientSourceEnvelopingModule :
    Module ESᵐᵒᵖ M :=
  EnvelopingCoefficient.rightEnvelopingModule k AS M
/-- The target coefficient carries the right enveloping action. -/
local instance polynomialCoefficientTargetEnvelopingModule :
    Module ETᵐᵒᵖ N :=
  EnvelopingCoefficient.rightEnvelopingModule k AT N

include hf in
/-- Symmetry and the original coefficient action law earn compatibility
with the mapped right-enveloping actions. -/
theorem coefficientEnvelopingAlgebraLaw (e : ES) (m : M) :
    f (MulOpposite.op e • m) = MulOpposite.op (φ e) • f m := by
  change f (EnvelopingCoefficient.rightEnvelopingAction k AS M (MulOpposite.op e) m) =
    EnvelopingCoefficient.rightEnvelopingAction k AT N (MulOpposite.op (φ e)) (f m)
  rw [symmetricRightEnvelopingAction_multiplication,
    symmetricRightEnvelopingAction_multiplication,
    MvPolynomial.polynomialEnvelopingMap_multiplication]
  exact hf (MvPolynomial.diagonalMultiplication k σ e) m

/-- The scalar-changing coefficient natural transformation on
the original target enveloping left modules. -/
def polynomialCoefficientTensorAlong :
    (R ⋙ TM).mapHomologicalComplex (.down ℕ) ⟶ TNc :=
  ModuleCat.BalancedTensor.Along.chainNatTrans k φ f
    (coefficientEnvelopingAlgebraLaw k g f hf)

/-- The coefficient map on the two original polynomial diagonal complexes. -/
def polynomialCoefficientDiagonalAlgebraMap :
    symmetricCoefficientComplex k σ M ⟶ symmetricCoefficientComplex k τ N :=
  (TMc).map (polynomialDiagonalRestrictedMap k g) ≫
    (polynomialCoefficientTensorAlong k g f hf).app (KoszulComplex.polynomialDiagonalComplex k τ)

/-- The coefficient map on the two original tensor-of-Bar complexes. -/
def polynomialCoefficientBarAlgebraMap :
    AdjacentBar.coefficientTensorComplex k AS M ⟶ AdjacentBar.coefficientTensorComplex k AT N :=
  (TMc).map (AdjacentBar.envelopingBarAlgebraMap k g) ≫
    (polynomialCoefficientTensorAlong k g f hf).app (AdjacentBar.envelopingBar k AT)

/-- Scalar-changing coefficient tensoring retains its original pure Bar
representative and applies the original algebra map to every factor. -/
theorem polynomialCoefficientBarAlgebraMap_mk (n : ℕ) (m : M)
    (z : AdjacentBar.envelopingBarDegree k AS n) :
    letI : Module k (AdjacentBar.envelopingBarDegree k AS n) := Module.compHom _ (algebraMap k ES)
    letI : Module k (AdjacentBar.envelopingBarDegree k AT n) := Module.compHom _ (algebraMap k ET)
    ((polynomialCoefficientBarAlgebraMap k g f hf).f n).hom
      (TensorProduct.Balanced.mk k ES M (AdjacentBar.envelopingBarDegree k AS n) m z) =
      TensorProduct.Balanced.mk k ET N (AdjacentBar.envelopingBarDegree k AT n) (f m)
        (AdjacentBar.barAlgebraLevelMap k g n z) := by
  letI : Module k (AdjacentBar.envelopingBarDegree k AS n) := Module.compHom _ (algebraMap k ES)
  letI : Module k (AdjacentBar.envelopingBarDegree k AT n) := Module.compHom _ (algebraMap k ET)
  let X := AdjacentBar.envelopingBarDegree k AS n
  let Y := AdjacentBar.envelopingBarDegree k AT n
  let b : X ⟶ (R).obj Y := (AdjacentBar.envelopingBarAlgebraMap k g).f n
  let c := ModuleCat.BalancedTensor.Along.component k φ f
    (coefficientEnvelopingAlgebraLaw k g f hf) Y
  let q := TensorProduct.Balanced.mk k ES M X m z
  have hmap := ModuleCat.BalancedTensor.map_mk k ES M b m z
  have hc := ModuleCat.BalancedTensor.Along.component_mk k φ f
    (coefficientEnvelopingAlgebraLaw k g f hf) Y m (b.hom z)
  have hb : b.hom z = AdjacentBar.barAlgebraLevelMap k g n z := rfl
  have hvalue : ((polynomialCoefficientBarAlgebraMap k g f hf).f n).hom q =
      c.hom ((ModuleCat.BalancedTensor.map k ES M b).hom q) := rfl
  exact hvalue.trans ((congrArg c.hom hmap).trans
    (hc.trans (congrArg (fun y : Y => ModuleCat.BalancedTensor.Along.targetMk k Y (f m) y) hb)))

/-- Apply the coefficient Bar map between the original raw Hochschild
coordinates. Unit outer factors stay units, and the middle tensor map is literal. -/
theorem polynomialCoefficientBarAlgebraMap_inverse_word
    (n : ℕ) (m : M) (a : Fin n → AS) :
    ((AdjacentBar.coefficientTensorChainIso k AT N).hom.f n).hom
      (((polynomialCoefficientBarAlgebraMap k g f hf).f n).hom
        (((AdjacentBar.coefficientTensorChainIso k AS M).inv.f n).hom
          (m ⊗ₜ[k] PiTensorProduct.tprod k a))) =
      f m ⊗ₜ[k] PiTensorProduct.tprod k (fun j => g (a j)) := by
  letI : Module k (AdjacentBar.envelopingBarDegree k AS n) := Module.compHom _ (algebraMap k ES)
  letI : Module k (AdjacentBar.envelopingBarDegree k AT n) := Module.compHom _ (algebraMap k ET)
  let wS := m ⊗ₜ[k] PiTensorProduct.tprod k a
  let zS : AdjacentBar.envelopingBarDegree k AS n :=
    (1 : AS) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.snoc a 1)
  let aT : Fin n → AT := fun j => g (a j)
  let zT : AdjacentBar.envelopingBarDegree k AT n :=
    (1 : AT) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.snoc aT 1)
  let qS := TensorProduct.Balanced.mk k ES M (AdjacentBar.envelopingBarDegree k AS n) m zS
  let qT := TensorProduct.Balanced.mk k ET N (AdjacentBar.envelopingBarDegree k AT n) (f m) zT
  let cS := ((AdjacentBar.coefficientTensorChainIso k AS M).inv.f n).hom
  let cT := ((AdjacentBar.coefficientTensorChainIso k AT N).hom.f n).hom
  let b := ((polynomialCoefficientBarAlgebraMap k g f hf).f n).hom
  have hInv : cS wS = qS := by
    have hmap := LinearMap.congr_fun (AdjacentBar.coefficientTensorChainIso_inv_f k AS M n) wS
    have hpure := AdjacentBar.coefficientTensorLevelEquiv_symm_tprod k AS M n m a
    exact hmap.trans hpure
  have hbar : b qS = qT := by
    have h := polynomialCoefficientBarAlgebraMap_mk k g f hf n m zS
    have hz : AdjacentBar.barAlgebraLevelMap k g n zS = zT :=
      AdjacentBar.barAlgebraLevelMap_unit_word k g n a
    exact h.trans (congrArg
      (fun z : AdjacentBar.envelopingBarDegree k AT n =>
        TensorProduct.Balanced.mk k ET N (AdjacentBar.envelopingBarDegree k AT n) (f m) z) hz)
  have hOut : cT qT = f m ⊗ₜ[k] PiTensorProduct.tprod k aT := by
    have hmap := LinearMap.congr_fun (AdjacentBar.coefficientTensorChainIso_hom_f k AT N n) qT
    have hpure := AdjacentBar.coefficientTensorLevelEquiv_mk_tprod k AT N n (f m) 1 (Fin.snoc aT 1)
    exact hmap.trans (hpure.trans (by
      simp only [Fin.snoc_last, Fin.init_snoc, MulOpposite.op_one, one_smul]))
  exact (congrArg (fun x => cT (b x)) hInv).trans ((congrArg cT hbar).trans hOut)

/-- Actual endpoint-sensitive Bar cancellation gives the original raw
coefficient-first Hochschild algebra map. -/
@[reassoc]
theorem polynomialCoefficientBarAlgebraMap_cancellation :
    polynomialCoefficientBarAlgebraMap k g f hf ≫ (AdjacentBar.coefficientTensorChainIso k AT N).hom =
      (AdjacentBar.coefficientTensorChainIso k AS M).hom ≫
        Symmetric.originalAlgebraCoefficientChainMap k g f hf := by
  let cS := AdjacentBar.coefficientTensorChainIso k AS M
  let cT := AdjacentBar.coefficientTensorChainIso k AT N
  let b := polynomialCoefficientBarAlgebraMap k g f hf
  let F := Symmetric.originalAlgebraCoefficientChainMap k g f hf
  apply (cancel_epi cS.inv).1
  have hLeft : cS.inv ≫ (b ≫ cT.hom) = F := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply ModuleCat.Algebra.Hochschild.tensorPower_ext
    intro m a
    have h := (polynomialCoefficientBarAlgebraMap_inverse_word k g f hf n m a).trans
      (Symmetric.originalAlgebraCoefficientChainMap_tprod k g f hf n m a).symm
    have hcomp :
        (((cT.hom.f n).hom.comp (b.f n).hom).comp (cS.inv.f n).hom)
            (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
          (cT.hom.f n).hom ((b.f n).hom ((cS.inv.f n).hom
            (m ⊗ₜ[k] PiTensorProduct.tprod k a))) := rfl
    exact hcomp.trans h
  have hRight : cS.inv ≫ (cS.hom ≫ F) = F :=
    (Category.assoc cS.inv cS.hom F).symm.trans
      ((congrArg (fun t : chainComplex k AS M ⟶ chainComplex k AS M => t ≫ F)
        cS.inv_hom_id).trans (Category.id_comp F))
  exact hLeft.trans hRight.symm

/-- Actual scalar-changing diagonal tensoring keeps the original arbitrary
diagonal element and the semilinear Koszul image. -/
theorem polynomialCoefficientDiagonalAlgebraMap_mk (n : ℕ) (m : M)
    (z : ⋀[ES]^n (σ →₀ ES)) :
    letI : Module k (⋀[ES]^n (σ →₀ ES)) := Module.compHom _ (algebraMap k ES)
    letI : Module k (⋀[ET]^n (τ →₀ ET)) := Module.compHom _ (algebraMap k ET)
    ((polynomialCoefficientDiagonalAlgebraMap k g f hf).f n).hom
      (TensorProduct.Balanced.mk k ES M (⋀[ES]^n (σ →₀ ES)) m z) =
      TensorProduct.Balanced.mk k ET N (⋀[ET]^n (τ →₀ ET)) (f m)
        (exteriorPower.mapSemilinear (φ).toRingHom (MvPolynomial.polynomialDiagonalGeneratorMap k τ g) n z) := by
  letI : Module k (⋀[ES]^n (σ →₀ ES)) := Module.compHom _ (algebraMap k ES)
  letI : Module k (⋀[ET]^n (τ →₀ ET)) := Module.compHom _ (algebraMap k ET)
  let X := ModuleCat.of ES (⋀[ES]^n (σ →₀ ES))
  let Y := ModuleCat.of ET (⋀[ET]^n (τ →₀ ET))
  let d : X ⟶ (R).obj Y := (polynomialDiagonalRestrictedMap k g).f n
  let c := ModuleCat.BalancedTensor.Along.component k φ f
    (coefficientEnvelopingAlgebraLaw k g f hf) Y
  let q := TensorProduct.Balanced.mk k ES M X m z
  have hmap := ModuleCat.BalancedTensor.map_mk k ES M d m z
  have hc := ModuleCat.BalancedTensor.Along.component_mk k φ f
    (coefficientEnvelopingAlgebraLaw k g f hf) Y m (d.hom z)
  have hd : d.hom z = exteriorPower.mapSemilinear (φ).toRingHom
      (MvPolynomial.polynomialDiagonalGeneratorMap k τ g) n z :=
    polynomialDiagonalRestrictedMap_f_apply k g n z
  have hvalue : ((polynomialCoefficientDiagonalAlgebraMap k g f hf).f n).hom q =
      c.hom ((ModuleCat.BalancedTensor.map k ES M d).hom q) := rfl
  exact hvalue.trans ((congrArg c.hom hmap).trans
    (hc.trans (congrArg (fun y : Y => ModuleCat.BalancedTensor.Along.targetMk k Y (f m) y) hd)))

/-- The signed polynomial coefficient comparison is algebra-natural up to
the tensor image of the projective augmentation homotopy. -/
def polynomialAntisymmetricCoefficientMap_algebraHomotopy :
    Homotopy
      (polynomialAntisymmetricCoefficientMap k σ M ≫
        Symmetric.originalAlgebraCoefficientChainMap k g f hf)
      (polynomialCoefficientDiagonalAlgebraMap k g f hf ≫
        polynomialAntisymmetricCoefficientMap k τ N) := by
  let α := polynomialCoefficientTensorAlong k g f hf
  let cS := AdjacentBar.coefficientTensorChainIso k AS M
  let cT := AdjacentBar.coefficientTensorChainIso k AT N
  let Q := KoszulComplex.polynomialDiagonalComplex k τ
  let BT := AdjacentBar.envelopingBar k AT
  let aS := polynomialAntisymmetricBarMap k σ
  let aT := polynomialAntisymmetricBarMap k τ
  let d := polynomialDiagonalRestrictedMap k g
  let b := AdjacentBar.envelopingBarAlgebraMap k g
  let H := ((TM).mapHomotopy (polynomialAntisymmetricBarMap_algebraHomotopy k g)).compRight
    (α.app BT ≫ cT.hom)
  have hα : (TMc).map (((R).mapHomologicalComplex (.down ℕ)).map aT) ≫ α.app BT =
      α.app Q ≫ (TNc).map aT := α.naturality aT
  let KS := KoszulComplex.polynomialDiagonalComplex k σ
  let BS := AdjacentBar.envelopingBar k AS
  let RF := (R).mapHomologicalComplex (.down ℕ)
  let rQ := RF.obj Q
  let rBT := RF.obj BT
  let fA : (TMc).obj KS ⟶ (TMc).obj BS := (TMc).map aS
  let fB : (TMc).obj BS ⟶ (TMc).obj rBT := (TMc).map b
  let fD : (TMc).obj KS ⟶ (TMc).obj rQ := (TMc).map d
  let fR : (TMc).obj rQ ⟶ (TMc).obj rBT := (TMc).map (RF.map aT)
  let fT : (TNc).obj Q ⟶ (TNc).obj BT := (TNc).map aT
  let aB : (TMc).obj rBT ⟶ (TNc).obj BT := α.app BT
  let aQ : (TMc).obj rQ ⟶ (TNc).obj Q := α.app Q
  let c : (TNc).obj BT ⟶ chainComplex k AT N := cT.hom
  let F := Symmetric.originalAlgebraCoefficientChainMap k g f hf
  have hleft : (TMc).map (aS ≫ b) ≫ (α.app BT ≫ cT.hom) =
      polynomialAntisymmetricCoefficientMap k σ M ≫ F := by
    have hc : (fB ≫ aB) ≫ c = cS.hom ≫ F :=
      polynomialCoefficientBarAlgebraMap_cancellation k g f hf
    have h1 : (TMc).map (aS ≫ b) ≫ (aB ≫ c) = (fA ≫ fB) ≫ (aB ≫ c) :=
      congrArg (fun t : (TMc).obj KS ⟶ (TMc).obj rBT => t ≫ (aB ≫ c))
        ((TMc).map_comp aS b)
    have h2 : (fA ≫ fB) ≫ (aB ≫ c) = fA ≫ ((fB ≫ aB) ≫ c) :=
      (Category.assoc fA fB (aB ≫ c)).trans
        (congrArg (fun t : (TMc).obj BS ⟶ chainComplex k AT N => fA ≫ t)
          (Category.assoc fB aB c).symm)
    have h3 : fA ≫ ((fB ≫ aB) ≫ c) = fA ≫ (cS.hom ≫ F) :=
      congrArg (fun t : (TMc).obj BS ⟶ chainComplex k AT N => fA ≫ t) hc
    have h4 : fA ≫ (cS.hom ≫ F) = (fA ≫ cS.hom) ≫ F :=
      (Category.assoc fA cS.hom F).symm
    have h5 : (fA ≫ cS.hom) ≫ F = polynomialAntisymmetricCoefficientMap k σ M ≫ F := rfl
    exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
  have hright : (TMc).map (d ≫ RF.map aT) ≫ (α.app BT ≫ cT.hom) =
      polynomialCoefficientDiagonalAlgebraMap k g f hf ≫
        polynomialAntisymmetricCoefficientMap k τ N := by
    have h1 : (TMc).map (d ≫ RF.map aT) ≫ (aB ≫ c) = (fD ≫ fR) ≫ (aB ≫ c) :=
      congrArg (fun t : (TMc).obj KS ⟶ (TMc).obj rBT => t ≫ (aB ≫ c))
        ((TMc).map_comp d (RF.map aT))
    have h2 : (fD ≫ fR) ≫ (aB ≫ c) = fD ≫ ((fR ≫ aB) ≫ c) :=
      (Category.assoc fD fR (aB ≫ c)).trans
        (congrArg (fun t : (TMc).obj rQ ⟶ chainComplex k AT N => fD ≫ t)
          (Category.assoc fR aB c).symm)
    have h3 : fD ≫ ((fR ≫ aB) ≫ c) = fD ≫ ((aQ ≫ fT) ≫ c) :=
      congrArg (fun t : (TMc).obj rQ ⟶ (TNc).obj BT => fD ≫ (t ≫ c)) hα
    have h4 : fD ≫ ((aQ ≫ fT) ≫ c) = (fD ≫ aQ) ≫ (fT ≫ c) :=
      (congrArg (fun t : (TMc).obj rQ ⟶ chainComplex k AT N => fD ≫ t)
        (Category.assoc aQ fT c)).trans (Category.assoc fD aQ (fT ≫ c)).symm
    have h5 : (fD ≫ aQ) ≫ (fT ≫ c) = polynomialCoefficientDiagonalAlgebraMap k g f hf ≫
        polynomialAntisymmetricCoefficientMap k τ N := rfl
    exact h1.trans (h2.trans (h3.trans (h4.trans h5)))
  exact ((Homotopy.ofEq hleft).symm.trans H).trans (Homotopy.ofEq hright)

end ModuleCat.Algebra.Hochschild.PolynomialDiagonal
