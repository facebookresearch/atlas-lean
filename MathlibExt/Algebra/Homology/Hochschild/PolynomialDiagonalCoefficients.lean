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
# Polynomial diagonal coefficient differentials and symmetric homology

Let k be a commutative ring, A = k[σ] and E = A ⊗[k] Aᵐᵒᵖ. Tensoring the diagonal Koszul complex
with a compatible A-bimodule M gives a complex with terms M ⊗_E ∧ⁿ_E(⊕ᵢE·eᵢ). Its differential
is the alternating deletion sum with coefficient operators m ↦ m·Xᵢ − Xᵢ·m.

For symmetric coefficients, the right E-action factors through multiplication E → A. Every
diagonal difference acts trivially, and all coefficient diagonal differentials vanish. The
projective-resolution comparison then identifies HHₙ(A,M) with the degree-n diagonal term. In
degree zero this term is M; the class, forward coordinate and inverse coordinate formulas are
given both as linear maps and as categorical maps to a canonically lifted coefficient module.

The diagonal resolution is the polynomial Koszul description of Hochschild homology; its
differential-form interpretation is the polynomial case of the Hochschild–Kostant–Rosenberg
theorem.
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
/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-bimodule with commuting left and right actions
compatible with its k-module structure. With the induced right E-action on M, coefficientComplex
k σ M equals the balanced coefficient Koszul complex M ⊗_E K(E,V,δ). -/
theorem coefficientComplex_eq_balanced :
    letI := EnvelopingCoefficient.rightEnvelopingModule k A M
    coefficientComplex k σ M = KoszulComplex.balancedCoefficientComplex k E V M x := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  rfl

omit [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M] in
/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-bimodule with commuting left and right actions
compatible with its k-module structure. In every n : ℕ, the degree-n term of coefficientComplex
k σ M equals the degree-n balanced Koszul term M ⊗_E ∧ⁿ_EV. -/
theorem coefficientComplex_X_eq_balanced (n : ℕ) :
    letI := EnvelopingCoefficient.rightEnvelopingModule k A M
    (coefficientComplex k σ M).X n =
      (KoszulComplex.balancedCoefficientComplex k E V M x).X n := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  rfl

omit [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M] in
/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-bimodule with commuting left and right actions
compatible with its k-module structure. For all i,j : ℕ, the differential of coefficientComplex
k σ M equals the corresponding differential of the balanced coefficient complex M ⊗_E K(E,V,δ). -/
theorem coefficientComplex_d_eq_balanced (i j : ℕ) :
    letI := EnvelopingCoefficient.rightEnvelopingModule k A M
    (coefficientComplex k σ M).d i j =
      (KoszulComplex.balancedCoefficientComplex k E V M x).d i j := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  rfl

omit [SMulCommClass k A M] [SMulCommClass k Aᵐᵒᵖ M] in
/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-bimodule with commuting left and right actions
compatible with its k-module structure. For i ∈ σ and m ∈ M, the right E-action of δᵢ on m is
m·Xᵢ − Xᵢ·m; equivalently (δᵢ)ᵐᵒᵖ·m = (Xᵢ)ᵐᵒᵖ·m − Xᵢ·m. -/
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
/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-bimodule with commuting left and right actions
compatible with its k-module structure. For m ∈ M and f : Fin(n+1) → σ, the differential of m
⊗_E(e_{f(0)}∧…∧e_{f(n)}) is ∑ⱼ (m·((-1)ʲδ_{f(j)})) ⊗_E(e_{f(0)}∧…∧ê_{f(j)}∧…∧e_{f(n)}).
Positions j are counted from zero; the diagonal action is right minus left multiplication. -/
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

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-module with compatible k-action, regarded as a
symmetric A-bimodule. Tensor the diagonal Koszul complex K(E,V,δ) with the right E-module M
induced by the symmetric right A-action. This defines symmetricCoefficientComplex, an ℕ-indexed
chain complex of k-modules with terms M ⊗_E ∧ⁿ_EV. -/
def symmetricCoefficientComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ := by
  letI := Module.oppositeOfCommutingAction A M
  letI := Module.oppositeOfCommutingAction_actionsComm A M
  letI := Module.oppositeOfCommutingAction_smulComm A M (R := k)
  letI := Module.oppositeOfCommutingAction_isScalarTower A M (R := k)
  exact coefficientComplex k σ M

omit [SMulCommClass k (MvPolynomial σ k) M] in
/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-module with compatible k-action, regarded as a
symmetric A-bimodule. For z ∈ E and m ∈ M, the right enveloping action satisfies m·z = μ(z)·m,
where μ : E → A is multiplication. In the displayed opposite-module notation this is
rightEnvelopingAction(zᵐᵒᵖ,m) = μ(z)·m. -/
theorem symmetricRightEnvelopingAction_multiplication (z : E) (m : M) :
    letI := Module.oppositeOfCommutingAction A M
    letI := Module.oppositeOfCommutingAction_actionsComm A M
    letI := Module.oppositeOfCommutingAction_smulComm A M (R := k)
    letI := Module.oppositeOfCommutingAction_isScalarTower A M (R := k)
    EnvelopingCoefficient.rightEnvelopingAction k A M (op z) m =
      MvPolynomial.diagonalMultiplication k σ z • m := by
  letI := Module.oppositeOfCommutingAction A M
  letI := Module.oppositeOfCommutingAction_actionsComm A M
  letI := Module.oppositeOfCommutingAction_smulComm A M (R := k)
  letI := Module.oppositeOfCommutingAction_isScalarTower A M (R := k)
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
      have h := EnvelopingCoefficient.rightEnvelopingAction_tmul k A M a b.unop m
      have hm := MvPolynomial.diagonalMultiplication_tmul k σ a b.unop
      rw [op_unop] at h hm
      rw [h, Module.oppositeOfCommutingAction_smul, smul_smul, hm]
      simp only [MulOpposite.unop_op]
  | add z z' hz hz' =>
      simp only [MulOpposite.op_add, map_add, LinearMap.add_apply, add_smul, hz, hz']

omit [SMulCommClass k (MvPolynomial σ k) M] in
/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-module with compatible k-action, regarded as a
symmetric A-bimodule. Let δ : V → E be the diagonal-difference functional. For every a ∈ V and m
∈ M, m·δ(a) = 0. Its value lies in ker μ, and the symmetric right E-action factors through μ : E
→ A. -/
theorem symmetricFunctional_action_eq_zero (a : V) (m : M) :
    letI := Module.oppositeOfCommutingAction A M
    letI := Module.oppositeOfCommutingAction_actionsComm A M
    letI := Module.oppositeOfCommutingAction_smulComm A M (R := k)
    letI := Module.oppositeOfCommutingAction_isScalarTower A M (R := k)
    letI := EnvelopingCoefficient.rightEnvelopingModule k A M
    op (x a) • m = 0 := by
  letI := Module.oppositeOfCommutingAction A M
  letI := Module.oppositeOfCommutingAction_actionsComm A M
  letI := Module.oppositeOfCommutingAction_smulComm A M (R := k)
  letI := Module.oppositeOfCommutingAction_isScalarTower A M (R := k)
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  change EnvelopingCoefficient.rightEnvelopingAction k A M (op (x a)) m = 0
  rw [symmetricRightEnvelopingAction_multiplication]
  have hmem : x a ∈ KoszulComplex.ideal E V x := LinearMap.mem_range_self x a
  rw [KoszulComplex.polynomialDiagonalIdeal_eq_ker_multiplication] at hmem
  change MvPolynomial.diagonalMultiplication k σ (x a) = 0 at hmem
  rw [hmem, zero_smul]

omit [SMulCommClass k (MvPolynomial σ k) M] in
/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-module with compatible k-action, regarded as a
symmetric A-bimodule. For each n : ℕ, the differential from degree n+1 to degree n of
symmetricCoefficientComplex k σ M is zero, because every diagonal functional value acts
trivially on M. -/
theorem symmetricCoefficientComplex_d_succ (n : ℕ) :
    (symmetricCoefficientComplex k σ M).d (n + 1) n = 0 := by
  letI := Module.oppositeOfCommutingAction A M
  letI := Module.oppositeOfCommutingAction_actionsComm A M
  letI := Module.oppositeOfCommutingAction_smulComm A M (R := k)
  letI := Module.oppositeOfCommutingAction_isScalarTower A M (R := k)
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
/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-module with compatible k-action, regarded as a
symmetric A-bimodule. For every i,j : ℕ, the differential (symmetricCoefficientComplex k σ M).d
i j is zero, including the maps outside the consecutive-degree chain shape. -/
theorem symmetricCoefficientComplex_d_eq_zero (i j : ℕ) :
    (symmetricCoefficientComplex k σ M).d i j = 0 := by
  by_cases h : (ComplexShape.down ℕ).Rel i j
  · change j + 1 = i at h
    subst i
    exact symmetricCoefficientComplex_d_succ k σ M j
  · exact (symmetricCoefficientComplex k σ M).shape i j h

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-module with compatible k-action, regarded as a
symmetric A-bimodule. The Hochschild chain complex Cₙ(A,M) = M ⊗[k] A^{⊗n} is homotopy
equivalent to symmetricCoefficientComplex k σ M. The comparison is induced by the
augmentation-preserving enveloping bar and diagonal projective resolutions. -/
def symmetricCoefficientComparison :
    HomotopyEquiv (Symmetric.chainComplex k A M) (symmetricCoefficientComplex k σ M) := by
  letI := Module.oppositeOfCommutingAction A M
  letI := Module.oppositeOfCommutingAction_actionsComm A M
  letI := Module.oppositeOfCommutingAction_smulComm A M (R := k)
  letI := Module.oppositeOfCommutingAction_isScalarTower A M (R := k)
  exact coefficientComparison k σ M

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-module with compatible k-action, regarded as a
symmetric A-bimodule. For n : ℕ, the resolution comparison and the zero diagonal differential
give an isomorphism HHₙ(A,M) ≅ (symmetricCoefficientComplex k σ M).X n = M ⊗_E ∧ⁿ_EV. -/
def symmetricCoefficientHomologyIsoDegree (n : ℕ) :
    (Symmetric.chainComplex k A M).homology n ≅ (symmetricCoefficientComplex k σ M).X n :=
  (symmetricCoefficientComparison k σ M).toHomologyIso n ≪≫
    HomologicalComplex.zeroDifferentialHomologyIso (symmetricCoefficientComplex k σ M) n
      (symmetricCoefficientComplex_d_eq_zero k σ M)

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-module with compatible k-action, regarded as a
symmetric A-bimodule. In degree n : ℕ, the forward map of symmetricCoefficientHomologyIsoDegree
is the homology map of symmetricCoefficientComparison.hom followed by the zero-differential
homology isomorphism from the diagonal homology to its degree-n term. -/
theorem symmetricCoefficientHomologyIsoDegree_hom (n : ℕ) :
    (symmetricCoefficientHomologyIsoDegree k σ M n).hom =
      HomologicalComplex.homologyMap (symmetricCoefficientComparison k σ M).hom n ≫
        (HomologicalComplex.zeroDifferentialHomologyIso (symmetricCoefficientComplex k σ M) n
          (symmetricCoefficientComplex_d_eq_zero k σ M)).hom := rfl

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-module with compatible k-action, regarded as a
symmetric A-bimodule. In degree n : ℕ, take a diagonal term z ∈ M ⊗_E ∧ⁿ_EV to its homology
class in the zero-differential diagonal complex, then apply the homology map of
symmetricCoefficientComparison.inv. This defines symmetricHochschildClassFromDiagonal : M ⊗_E
∧ⁿ_EV → HHₙ(A,M). -/
def symmetricHochschildClassFromDiagonal (n : ℕ) :
    (symmetricCoefficientComplex k σ M).X n ⟶ (Symmetric.chainComplex k A M).homology n :=
  HomologicalComplex.zeroDifferentialClassMap (symmetricCoefficientComplex k σ M) n
      (symmetricCoefficientComplex_d_eq_zero k σ M) ≫
    HomologicalComplex.homologyMap (symmetricCoefficientComparison k σ M).inv n

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-module with compatible k-action, regarded as a
symmetric A-bimodule. For n : ℕ, symmetricHochschildClassFromDiagonal followed by the forward
map of symmetricCoefficientHomologyIsoDegree is the identity on the degree-n diagonal
coefficient term. -/
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
  exact HomologicalComplex.zeroDifferentialClassMap_homologyIso (symmetricCoefficientComplex k σ M)
      n
    (symmetricCoefficientComplex_d_eq_zero k σ M)

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-module with compatible k-action, regarded as a
symmetric A-bimodule. The degree-zero diagonal coefficient term is k-linearly equivalent to M,
by ∧⁰_EV ≅ E and the balanced tensor unit isomorphism M ⊗_E E ≅ M. -/
def symmetricCoefficientDegreeZeroEquiv :
    (symmetricCoefficientComplex k σ M).X 0 ≃ₗ[k] M := by
  letI := Module.oppositeOfCommutingAction A M
  letI := Module.oppositeOfCommutingAction_actionsComm A M
  letI := Module.oppositeOfCommutingAction_smulComm A M (R := k)
  letI := Module.oppositeOfCommutingAction_isScalarTower A M (R := k)
  letI nativeRight : Module Eᵐᵒᵖ M := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI nativeTower : IsScalarTower k Eᵐᵒᵖ M := EnvelopingCoefficient.rightEnvelopingScalarTower k A
      M
  change (coefficientComplex k σ M).X 0 ≃ₗ[k] M
  let e : (coefficientComplex k σ M).X 0 ≅
      (KoszulComplex.balancedCoefficientComplex k E V M x).X 0 :=
    eqToIso (coefficientComplex_X_eq_balanced k σ M 0)
  let f : (KoszulComplex.balancedCoefficientComplex k E V M x).X 0 ≃ₗ[k] M :=
    @KoszulComplex.balancedCoefficientDegreeZeroEquiv k inferInstance E inferInstance
      inferInstance V inferInstance inferInstance M inferInstance inferInstance nativeRight
          nativeTower x
  exact e.toLinearEquiv.trans f

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-module with compatible k-action, regarded as a
symmetric A-bimodule. Composing the diagonal homology comparison in degree zero with M ⊗_E ∧⁰_EV
≅ M gives a k-linear equivalence HH₀(A,M) ≅ M. -/
def symmetricHochschildHomologyZeroEquivCoefficient :
    (Symmetric.chainComplex k A M).homology 0 ≃ₗ[k] M :=
  (symmetricCoefficientHomologyIsoDegree k σ M 0).toLinearEquiv.trans
    (symmetricCoefficientDegreeZeroEquiv k σ M)

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-module with compatible k-action, regarded as a
symmetric A-bimodule. If k, σ and M lie in universes u,v,w, the k-linear equivalence HH₀(A,M) ≅
M gives an isomorphism of k-modules to the canonical lift of M to the common universe
max(u,v,w). -/
def symmetricHochschildHomologyZeroIsoCoefficient :
    (Symmetric.chainComplex k A M).homology 0 ≅ ModuleCat.of k (ULift.{max u v w, w} M) :=
  ((symmetricHochschildHomologyZeroEquivCoefficient k σ M).trans
    (ULift.moduleEquiv : ULift.{max u v w, w} M ≃ₗ[k] M).symm).toModuleIso

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-module with compatible k-action, regarded as a
symmetric A-bimodule. For m ∈ M, form the balanced degree-zero tensor m ⊗_E 1, where 1 is the
empty exterior wedge, and transport its diagonal cycle class through the inverse resolution
comparison. The resulting element of HH₀(A,M) is symmetricHochschildZeroClass k σ M m. -/
def symmetricHochschildZeroClass (m : M) : (Symmetric.chainComplex k A M).homology 0 := by
  letI := Module.oppositeOfCommutingAction A M
  letI := Module.oppositeOfCommutingAction_actionsComm A M
  letI := Module.oppositeOfCommutingAction_smulComm A M (R := k)
  letI := Module.oppositeOfCommutingAction_isScalarTower A M (R := k)
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI : Module k (⋀[E]^0 V) := Module.compHom _ (algebraMap k E)
  exact (symmetricHochschildClassFromDiagonal k σ M 0)
    (TensorProduct.Balanced.mk k E M (⋀[E]^0 V) m
      (exteriorPower.ιMulti E 0 (fun i : Fin 0 => Fin.elim0 i)))

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-module with compatible k-action, regarded as a
symmetric A-bimodule. For m ∈ M, symmetricHochschildHomologyZeroEquivCoefficient sends
symmetricHochschildZeroClass k σ M m to m. -/
theorem symmetricHochschildZeroClass_equiv_value (m : M) :
    symmetricHochschildHomologyZeroEquivCoefficient k σ M
        (symmetricHochschildZeroClass k σ M m) = m := by
  letI := Module.oppositeOfCommutingAction A M
  letI := Module.oppositeOfCommutingAction_actionsComm A M
  letI := Module.oppositeOfCommutingAction_smulComm A M (R := k)
  letI := Module.oppositeOfCommutingAction_isScalarTower A M (R := k)
  letI nativeRight : Module Eᵐᵒᵖ M := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI nativeTower : IsScalarTower k Eᵐᵒᵖ M := EnvelopingCoefficient.rightEnvelopingScalarTower k A
      M
  letI : Module k (⋀[E]^0 V) := Module.compHom _ (algebraMap k E)
  let a : ⋀[E]^0 V := exteriorPower.ιMulti E 0 (fun i : Fin 0 => Fin.elim0 i)
  let z : (symmetricCoefficientComplex k σ M).X 0 :=
    TensorProduct.Balanced.mk k E M (⋀[E]^0 V) m a
  have hc : (symmetricCoefficientHomologyIsoDegree k σ M 0).hom.hom
      ((symmetricHochschildClassFromDiagonal k σ M 0).hom z) = z :=
    (ModuleCat.comp_apply (symmetricHochschildClassFromDiagonal k σ M 0)
      (symmetricCoefficientHomologyIsoDegree k σ M 0).hom z).symm.trans
        ((ConcreteCategory.congr_hom (symmetricHochschildClassFromDiagonal_coordinates k σ M 0)
            z).trans
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
      inferInstance V inferInstance inferInstance M inferInstance inferInstance nativeRight
          nativeTower x
  have ht : e.hom.hom z = TensorProduct.Balanced.mk k E M (⋀[E]^0 V) m a := rfl
  have hf : symmetricCoefficientDegreeZeroEquiv k σ M z = f (e.hom.hom z) := rfl
  have hu := @KoszulComplex.balancedCoefficientDegreeZeroEquiv_mk k inferInstance E inferInstance
    inferInstance V inferInstance inferInstance M inferInstance inferInstance nativeRight
        nativeTower x m a
  simp only [a, exteriorPower.zeroEquiv_ιMulti, op_one, one_smul] at hu
  exact he.trans ((congrArg (symmetricCoefficientDegreeZeroEquiv k σ M) hc).trans
    (hf.trans ((congrArg f ht).trans hu)))

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-module with compatible k-action, regarded as a
symmetric A-bimodule. For m ∈ M, the forward map of
symmetricHochschildHomologyZeroIsoCoefficient sends symmetricHochschildZeroClass k σ M m to the
canonical lift of m in the lifted coefficient module. -/
theorem symmetricHochschildZeroClass_value (m : M) :
    (symmetricHochschildHomologyZeroIsoCoefficient k σ M).hom.hom
        (symmetricHochschildZeroClass k σ M m) = ULift.up m := by
  change ULift.up (symmetricHochschildHomologyZeroEquivCoefficient k σ M
    (symmetricHochschildZeroClass k σ M m)) = ULift.up m
  rw [symmetricHochschildZeroClass_equiv_value]

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-module with compatible k-action, regarded as a
symmetric A-bimodule. For m ∈ M, apply the categorical degree-zero homology comparison to
symmetricHochschildZeroClass k σ M m and then the projection from the lifted coefficient module
to M. The result is m. -/
theorem symmetricHochschildZeroClass_value_down (m : M) :
    ((symmetricHochschildHomologyZeroIsoCoefficient k σ M).hom.hom
      (symmetricHochschildZeroClass k σ M m)).down = m := by
  exact congrArg ULift.down (symmetricHochschildZeroClass_value k σ M m)

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Put E = A ⊗[k] Aᵐᵒᵖ, V = ⊕ᵢ∈σ E·eᵢ
and δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Let M be an A-module with compatible k-action, regarded as a
symmetric A-bimodule. For m ∈ M, the inverse of symmetricHochschildHomologyZeroIsoCoefficient
sends the canonical lift of m to symmetricHochschildZeroClass k σ M m. -/
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
