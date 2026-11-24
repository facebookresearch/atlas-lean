/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.PolynomialDiagonalComparison
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricCoefficients
public import MathlibExt.Algebra.Homology.ZeroDifferentialHomology

/-!
# Polynomial diagonal coefficient differentials

For an arbitrary bimodule, the diagonal variable differential
is its right action minus its left action, matching the
Hochschild endpoint convention. For symmetric coefficients
the enveloping action factors through multiplication, and
all diagonal differentials vanish after coefficient tensoring.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct
open MulOpposite

universe u v w

namespace ModuleCat.Algebra.Hochschild.PolynomialDiagonal

variable (k : Type u) [CommRing k] (σ : Type v)

local notation "A" => MvPolynomial σ k
local notation "E" => MvPolynomial.PolynomialEnveloping k σ
local notation "V" => (σ →₀ E)
local notation "δ" => MvPolynomial.diagonalDifference k σ
local notation "x" => KoszulComplex.finsuppFunctional E δ

section ArbitraryBimodule

variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module (MvPolynomial σ k) M] [Module (MvPolynomial σ k)ᵐᵒᵖ M]
  [SMulCommClass (MvPolynomial σ k) (MvPolynomial σ k)ᵐᵒᵖ M]
  [SMulCommClass k (MvPolynomial σ k) M] [SMulCommClass k (MvPolynomial σ k)ᵐᵒᵖ M]
  [IsScalarTower k (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k)ᵐᵒᵖ M]

omit [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M] in
/-- The polynomial coefficient model is the canonical balanced tensor of the original Koszul complex. -/
theorem coefficientComplex_eq_balanced :
    letI := EnvelopingCoefficient.rightEnvelopingModule k A M
    coefficientComplex k σ M = KoszulComplex.balancedCoefficientComplex k E V M x := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  rfl

omit [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M] in
/-- Each coefficient degree is the same canonical balanced degree. -/
theorem coefficientComplex_X_eq_balanced (n : ℕ) :
    letI := EnvelopingCoefficient.rightEnvelopingModule k A M
    (coefficientComplex k σ M).X n =
      (KoszulComplex.balancedCoefficientComplex k E V M x).X n := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  rfl

omit [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M] in
/-- Each differential is the balanced original Koszul differential. -/
theorem coefficientComplex_d_eq_balanced (i j : ℕ) :
    letI := EnvelopingCoefficient.rightEnvelopingModule k A M
    (coefficientComplex k σ M).d i j =
      (KoszulComplex.balancedCoefficientComplex k E V M x).d i j := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  rfl

omit [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M] in
/-- The original diagonal difference acts on a coefficient by original right-minus-left multiplication. -/
theorem rightDiagonalDifference_action (i : σ) (m : M) :
    letI := EnvelopingCoefficient.rightEnvelopingModule k A M
    op (δ i) • m = op (MvPolynomial.X i : A) • m - (MvPolynomial.X i : A) • m := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  change EnvelopingCoefficient.rightEnvelopingAction k A M (op (δ i)) m = _
  rw [MvPolynomial.diagonalDifference, MulOpposite.op_sub, map_sub, LinearMap.sub_apply,
    EnvelopingCoefficient.rightEnvelopingAction_tmul,
    EnvelopingCoefficient.rightEnvelopingAction_tmul]
  simp only [op_one, one_smul]

omit [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M] in
/-- Signed deletion in the coefficient model keeps every original coefficient operator. -/
theorem coefficientComplex_d_mk_basis (n : ℕ) (m : M) (f : Fin (n + 1) → σ) :
    letI := EnvelopingCoefficient.rightEnvelopingModule k A M
    letI : Module k (⋀[E]^(n + 1) V) := Module.compHom _ (algebraMap k E)
    letI : Module k (⋀[E]^n V) := Module.compHom _ (algebraMap k E)
    ((coefficientComplex k σ M).d (n + 1) n).hom
        (TensorProduct.Balanced.mk k E M (⋀[E]^(n + 1) V) m
          (exteriorPower.ιMulti E (n + 1) (fun j => Finsupp.single (f j) 1))) =
      ∑ j : Fin (n + 1), TensorProduct.Balanced.mk k E M (⋀[E]^n V)
        (op (((-1 : E) ^ j.val) * δ (f j)) • m)
        (exteriorPower.ιMulti E n (fun q => Finsupp.single (f (j.succAbove q)) 1)) := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI : Module k (⋀[E]^(n + 1) V) := Module.compHom _ (algebraMap k E)
  letI : Module k (⋀[E]^n V) := Module.compHom _ (algebraMap k E)
  let z : (coefficientComplex k σ M).X (n + 1) :=
    TensorProduct.Balanced.mk k E M (⋀[E]^(n + 1) V) m
      (exteriorPower.ιMulti E (n + 1) (fun j => Finsupp.single (f j) 1))
  have hd := congrArg
    (fun d : (coefficientComplex k σ M).X (n + 1) ⟶ (coefficientComplex k σ M).X n => d.hom z)
    (coefficientComplex_d_eq_balanced k σ M (n + 1) n)
  have hv := KoszulComplex.balancedCoefficientComplex_d_mk_ιMulti k E V M x n m
    (fun j => Finsupp.single (f j) 1)
  simp only [KoszulComplex.finsuppFunctional_single] at hv
  exact hd.trans hv

end ArbitraryBimodule

section Symmetric

variable (M : Type w) [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [SMulCommClass k (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k) M]

/-- The original symmetric right action is added canonically, leaving the coefficient carrier unchanged. -/
def symmetricCoefficientComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ := by
  letI := Symmetric.opModule A M
  letI := Symmetric.actionsComm A M
  letI := Symmetric.kOpComm k A M
  letI := Symmetric.kOpTower k A M
  exact coefficientComplex k σ M

omit [SMulCommClass k (MvPolynomial σ k) M] in
/-- The symmetric right enveloping action factors through original multiplication. -/
theorem symmetricRightEnvelopingAction_multiplication (z : E) (m : M) :
    letI := Symmetric.opModule A M
    letI := Symmetric.actionsComm A M
    letI := Symmetric.kOpComm k A M
    letI := Symmetric.kOpTower k A M
    EnvelopingCoefficient.rightEnvelopingAction k A M (op z) m =
      MvPolynomial.diagonalMultiplication k σ z • m := by
  letI := Symmetric.opModule A M
  letI := Symmetric.actionsComm A M
  letI := Symmetric.kOpComm k A M
  letI := Symmetric.kOpTower k A M
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
      have h := EnvelopingCoefficient.rightEnvelopingAction_tmul k A M a b.unop m
      have hm := MvPolynomial.diagonalMultiplication_tmul k σ a b.unop
      rw [op_unop] at h hm
      rw [h, Symmetric.opModule_smul, smul_smul, hm]
      simp only [MulOpposite.unop_op]
  | add z z' hz hz' =>
      simp only [MulOpposite.op_add, map_add, LinearMap.add_apply, add_smul, hz, hz']

omit [SMulCommClass k (MvPolynomial σ k) M] in
/-- Functional values are killed by the original symmetric coefficient, by the multiplication kernel. -/
theorem symmetricFunctional_action_eq_zero (a : V) (m : M) :
    letI := Symmetric.opModule A M
    letI := Symmetric.actionsComm A M
    letI := Symmetric.kOpComm k A M
    letI := Symmetric.kOpTower k A M
    letI := EnvelopingCoefficient.rightEnvelopingModule k A M
    op (x a) • m = 0 := by
  letI := Symmetric.opModule A M
  letI := Symmetric.actionsComm A M
  letI := Symmetric.kOpComm k A M
  letI := Symmetric.kOpTower k A M
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  change EnvelopingCoefficient.rightEnvelopingAction k A M (op (x a)) m = 0
  rw [symmetricRightEnvelopingAction_multiplication]
  have hmem : x a ∈ KoszulComplex.ideal E V x := LinearMap.mem_range_self x a
  rw [KoszulComplex.polynomialDiagonalIdeal_eq_ker_multiplication] at hmem
  change MvPolynomial.diagonalMultiplication k σ (x a) = 0 at hmem
  rw [hmem, zero_smul]

omit [SMulCommClass k (MvPolynomial σ k) M] in
/-- Every original symmetric coefficient diagonal differential vanishes. -/
theorem symmetricCoefficientComplex_d_succ (n : ℕ) :
    (symmetricCoefficientComplex k σ M).d (n + 1) n = 0 := by
  letI := Symmetric.opModule A M
  letI := Symmetric.actionsComm A M
  letI := Symmetric.kOpComm k A M
  letI := Symmetric.kOpTower k A M
  letI nativeRight : Module Eᵐᵒᵖ M := EnvelopingCoefficient.rightEnvelopingModule k A M
  have hx : ∀ (a : V) (m : M), op (x a) • m = 0 := by
    intro a m
    exact symmetricFunctional_action_eq_zero k σ M a m
  have hz : (KoszulComplex.balancedCoefficientComplex k E V M x).d (n + 1) n = 0 :=
    @KoszulComplex.balancedCoefficientComplex_d_eq_zero k inferInstance E inferInstance
      inferInstance V inferInstance inferInstance M inferInstance inferInstance nativeRight x hx n
  change (coefficientComplex k σ M).d (n + 1) n = 0
  exact @Eq.trans
    ((coefficientComplex k σ M).X (n + 1) ⟶ (coefficientComplex k σ M).X n)
    ((coefficientComplex k σ M).d (n + 1) n)
    ((KoszulComplex.balancedCoefficientComplex k E V M x).d (n + 1) n) 0
    (coefficientComplex_d_eq_balanced k σ M (n + 1) n)
    hz

omit [SMulCommClass k (MvPolynomial σ k) M] in
/-- The entire original symmetric coefficient complex has zero differentials, including shape-zero components. -/
theorem symmetricCoefficientComplex_d_eq_zero (i j : ℕ) :
    (symmetricCoefficientComplex k σ M).d i j = 0 := by
  by_cases h : (ComplexShape.down ℕ).Rel i j
  · change j + 1 = i at h
    subst i
    exact symmetricCoefficientComplex_d_succ k σ M j
  · exact (symmetricCoefficientComplex k σ M).shape i j h

/-- The original symmetric Hochschild complex is computed by this zero-differential coefficient model. -/
def symmetricCoefficientComparison :
    HomotopyEquiv (Symmetric.chainComplex k A M) (symmetricCoefficientComplex k σ M) := by
  letI := Symmetric.opModule A M
  letI := Symmetric.actionsComm A M
  letI := Symmetric.kOpComm k A M
  letI := Symmetric.kOpTower k A M
  exact coefficientComparison k σ M

/-- All original symmetric polynomial Hochschild homology is the degree object of the zero-differential
  diagonal model. -/
def symmetricCoefficientHomologyIsoDegree (n : ℕ) :
    (Symmetric.chainComplex k A M).homology n ≅ (symmetricCoefficientComplex k σ M).X n :=
  (symmetricCoefficientComparison k σ M).toHomologyIso n ≪≫
    HomologicalComplex.zeroDifferentialHomologyIso (symmetricCoefficientComplex k σ M) n
      (symmetricCoefficientComplex_d_eq_zero k σ M)

/-- The first part of the comparison is homology of the constructed original resolution lift. -/
theorem symmetricCoefficientHomologyIsoDegree_hom (n : ℕ) :
    (symmetricCoefficientHomologyIsoDegree k σ M n).hom =
      HomologicalComplex.homologyMap (symmetricCoefficientComparison k σ M).hom n ≫
        (HomologicalComplex.zeroDifferentialHomologyIso (symmetricCoefficientComplex k σ M) n
          (symmetricCoefficientComplex_d_eq_zero k σ M)).hom := rfl

/-- The original diagonal class transported by the inverse chain comparison. -/
def symmetricHochschildClassFromDiagonal (n : ℕ) :
    (symmetricCoefficientComplex k σ M).X n ⟶ (Symmetric.chainComplex k A M).homology n :=
  HomologicalComplex.zeroDifferentialClassMap (symmetricCoefficientComplex k σ M) n
      (symmetricCoefficientComplex_d_eq_zero k σ M) ≫
    HomologicalComplex.homologyMap (symmetricCoefficientComparison k σ M).inv n

/-- The transported native class has exactly the original degree-object coordinates. -/
@[reassoc]
theorem symmetricHochschildClassFromDiagonal_coordinates (n : ℕ) :
    symmetricHochschildClassFromDiagonal k σ M n ≫
        (symmetricCoefficientHomologyIsoDegree k σ M n).hom =
      𝟙 ((symmetricCoefficientComplex k σ M).X n) := by
  let e := (symmetricCoefficientComparison k σ M).toHomologyIso n
  change (HomologicalComplex.zeroDifferentialClassMap (symmetricCoefficientComplex k σ M) n
    (symmetricCoefficientComplex_d_eq_zero k σ M) ≫ e.inv) ≫
      (e.hom ≫ (HomologicalComplex.zeroDifferentialHomologyIso (symmetricCoefficientComplex k σ M) n
        (symmetricCoefficientComplex_d_eq_zero k σ M)).hom) = _
  rw [Category.assoc, ← Category.assoc e.inv, Iso.inv_hom_id, Category.id_comp]
  exact HomologicalComplex.zeroDifferentialClassMap_homologyIso (symmetricCoefficientComplex k σ M) n
    (symmetricCoefficientComplex_d_eq_zero k σ M)

/-- Native zero-exterior coordinates recover the original coefficient module at degree zero. -/
def symmetricCoefficientDegreeZeroEquiv :
    (symmetricCoefficientComplex k σ M).X 0 ≃ₗ[k] M := by
  letI := Symmetric.opModule A M
  letI := Symmetric.actionsComm A M
  letI := Symmetric.kOpComm k A M
  letI := Symmetric.kOpTower k A M
  letI nativeRight : Module Eᵐᵒᵖ M := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI nativeTower : IsScalarTower k Eᵐᵒᵖ M := EnvelopingCoefficient.rightEnvelopingScalarTower k A M
  change (coefficientComplex k σ M).X 0 ≃ₗ[k] M
  let e : (coefficientComplex k σ M).X 0 ≅
      (KoszulComplex.balancedCoefficientComplex k E V M x).X 0 :=
    eqToIso (coefficientComplex_X_eq_balanced k σ M 0)
  let f : (KoszulComplex.balancedCoefficientComplex k E V M x).X 0 ≃ₗ[k] M :=
    @KoszulComplex.balancedCoefficientDegreeZeroEquiv k inferInstance E inferInstance
      inferInstance V inferInstance inferInstance M inferInstance inferInstance nativeRight nativeTower x
  exact e.toLinearEquiv.trans f

/-- Actual original symmetric polynomial HH0 has the original coefficient as a raw linear equivalence across
  independent worlds. -/
def symmetricHochschildHomologyZeroEquivCoefficient :
    (Symmetric.chainComplex k A M).homology 0 ≃ₗ[k] M :=
  (symmetricCoefficientHomologyIsoDegree k σ M 0).toLinearEquiv.trans
    (symmetricCoefficientDegreeZeroEquiv k σ M)

/-- The categorical HH0 comparison uses only the canonical coefficient lift in the joint world. -/
def symmetricHochschildHomologyZeroIsoCoefficient :
    (Symmetric.chainComplex k A M).homology 0 ≅ ModuleCat.of k (ULift.{max u v w, w} M) :=
  ((symmetricHochschildHomologyZeroEquivCoefficient k σ M).trans
    (ULift.moduleEquiv : ULift.{max u v w, w} M ≃ₗ[k] M).symm).toModuleIso

/-- The original coefficient balanced with the native degree-zero unit gives its HH0 class. -/
def symmetricHochschildZeroClass (m : M) : (Symmetric.chainComplex k A M).homology 0 := by
  letI := Symmetric.opModule A M
  letI := Symmetric.actionsComm A M
  letI := Symmetric.kOpComm k A M
  letI := Symmetric.kOpTower k A M
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI : Module k (⋀[E]^0 V) := Module.compHom _ (algebraMap k E)
  exact (symmetricHochschildClassFromDiagonal k σ M 0)
    (TensorProduct.Balanced.mk k E M (⋀[E]^0 V) m
      (exteriorPower.ιMulti E 0 (fun i : Fin 0 => Fin.elim0 i)))

/-- The raw across-world comparison returns the same original coefficient of the independent native class. -/
theorem symmetricHochschildZeroClass_equiv_value (m : M) :
    symmetricHochschildHomologyZeroEquivCoefficient k σ M
        (symmetricHochschildZeroClass k σ M m) = m := by
  letI := Symmetric.opModule A M
  letI := Symmetric.actionsComm A M
  letI := Symmetric.kOpComm k A M
  letI := Symmetric.kOpTower k A M
  letI nativeRight : Module Eᵐᵒᵖ M := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI nativeTower : IsScalarTower k Eᵐᵒᵖ M := EnvelopingCoefficient.rightEnvelopingScalarTower k A M
  letI : Module k (⋀[E]^0 V) := Module.compHom _ (algebraMap k E)
  let a : ⋀[E]^0 V := exteriorPower.ιMulti E 0 (fun i : Fin 0 => Fin.elim0 i)
  let z : (symmetricCoefficientComplex k σ M).X 0 :=
    TensorProduct.Balanced.mk k E M (⋀[E]^0 V) m a
  have hc : (symmetricCoefficientHomologyIsoDegree k σ M 0).hom.hom
      ((symmetricHochschildClassFromDiagonal k σ M 0).hom z) = z :=
    (ModuleCat.comp_apply (symmetricHochschildClassFromDiagonal k σ M 0)
      (symmetricCoefficientHomologyIsoDegree k σ M 0).hom z).symm.trans
        ((ConcreteCategory.congr_hom (symmetricHochschildClassFromDiagonal_coordinates k σ M 0) z).trans
          (ModuleCat.id_apply ((symmetricCoefficientComplex k σ M).X 0) z))
  have he : symmetricHochschildHomologyZeroEquivCoefficient k σ M
      (symmetricHochschildZeroClass k σ M m) =
    symmetricCoefficientDegreeZeroEquiv k σ M
      ((symmetricCoefficientHomologyIsoDegree k σ M 0).hom.hom
        ((symmetricHochschildClassFromDiagonal k σ M 0).hom z)) := rfl
  let e : (coefficientComplex k σ M).X 0 ≅
      (KoszulComplex.balancedCoefficientComplex k E V M x).X 0 :=
    eqToIso (coefficientComplex_X_eq_balanced k σ M 0)
  let f : (KoszulComplex.balancedCoefficientComplex k E V M x).X 0 ≃ₗ[k] M :=
    @KoszulComplex.balancedCoefficientDegreeZeroEquiv k inferInstance E inferInstance
      inferInstance V inferInstance inferInstance M inferInstance inferInstance nativeRight nativeTower x
  have ht : e.hom.hom z = TensorProduct.Balanced.mk k E M (⋀[E]^0 V) m a := rfl
  have hf : symmetricCoefficientDegreeZeroEquiv k σ M z = f (e.hom.hom z) := rfl
  have hu := @KoszulComplex.balancedCoefficientDegreeZeroEquiv_mk k inferInstance E inferInstance
    inferInstance V inferInstance inferInstance M inferInstance inferInstance nativeRight nativeTower x m a
  simp only [a, exteriorPower.zeroEquiv_ιMulti, op_one, one_smul] at hu
  exact he.trans ((congrArg (symmetricCoefficientDegreeZeroEquiv k σ M) hc).trans
    (hf.trans ((congrArg f ht).trans hu)))

/-- The categorical comparison sends the independent original class to its canonical coefficient lift. -/
theorem symmetricHochschildZeroClass_value (m : M) :
    (symmetricHochschildHomologyZeroIsoCoefficient k σ M).hom.hom
        (symmetricHochschildZeroClass k σ M m) = ULift.up m := by
  change ULift.up (symmetricHochschildHomologyZeroEquivCoefficient k σ M
    (symmetricHochschildZeroClass k σ M m)) = ULift.up m
  rw [symmetricHochschildZeroClass_equiv_value]

/-- Canonical down recovers the original coefficient from the joint-world categorical value. -/
theorem symmetricHochschildZeroClass_value_down (m : M) :
    ((symmetricHochschildHomologyZeroIsoCoefficient k σ M).hom.hom
      (symmetricHochschildZeroClass k σ M m)).down = m := by
  exact congrArg ULift.down (symmetricHochschildZeroClass_value k σ M m)

/-- The inverse categorical comparison returns the independently specified class of an original coefficient. -/
theorem symmetricHochschildZeroClass_inv_up (m : M) :
    (symmetricHochschildHomologyZeroIsoCoefficient k σ M).inv.hom (ULift.up m) =
      symmetricHochschildZeroClass k σ M m := by
  have h := ConcreteCategory.congr_hom
    (symmetricHochschildHomologyZeroIsoCoefficient k σ M).hom_inv_id
    (symmetricHochschildZeroClass k σ M m)
  change (symmetricHochschildHomologyZeroIsoCoefficient k σ M).inv.hom
    ((symmetricHochschildHomologyZeroIsoCoefficient k σ M).hom.hom
      (symmetricHochschildZeroClass k σ M m)) = symmetricHochschildZeroClass k σ M m at h
  rw [symmetricHochschildZeroClass_value] at h
  exact h

end Symmetric

end ModuleCat.Algebra.Hochschild.PolynomialDiagonal
