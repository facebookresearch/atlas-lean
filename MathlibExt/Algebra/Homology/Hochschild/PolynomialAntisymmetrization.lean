/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.KoszulAntisymmetrization
public import MathlibExt.Algebra.Homology.Hochschild.PolynomialExteriorCoordinates

/-!
# Polynomial antisymmetrization from the diagonal Koszul resolution

Let k be a commutative ring, σ any variable set and A = k[σ]. The diagonal Koszul resolution
over E = A ⊗[k] Aᵐᵒᵖ has generators δᵢ = Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ. Antisymmetrization sends an
exterior generator word to its signed permutation sum in the enveloping bar resolution, with
outer entries equal to 1. This chain map preserves the multiplication augmentation and is
homotopic to the inverse projective-resolution comparison.

Tensoring with an arbitrary compatible A-bimodule M gives a homotopy equivalence with the
Hochschild chain complex. For symmetric coefficients, the diagonal differential vanishes, so the
signed chain map yields the coefficient-form isomorphism M ⊗[A] ∧ⁿ_AΩ¹_{A/k} ≅ HHₙ(A,M). The
comparison is constructed over k without division by n! and without a finiteness assumption on
σ.

The relation between polynomial diagonal resolutions and differential forms is the polynomial
case of the Hochschild–Kostant–Rosenberg theorem; see G. Hochschild, B. Kostant and A.
Rosenberg, “Differential forms on regular affine algebras,” Transactions of the American
Mathematical Society 102 (1962), 383–408.
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
local notation "V" => (σ →₀ k)
local notation "VE" => (σ →₀ E)
local notation "δ" => MvPolynomial.diagonalDifference k σ
local notation "P" => KoszulComplex.polynomialDiagonalProjectiveResolution k σ

attribute [local instance] Module.Projective.of_free

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. The k-linear map V → A sends each standard basis vector eᵢ to the variable Xᵢ;
equivalently it sends a finitely supported family c to ∑ᵢ cᵢXᵢ. -/
def polynomialGeneratorLinear : V →ₗ[k] A := Finsupp.linearCombination k MvPolynomial.X

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. For i ∈ σ, polynomialGeneratorLinear sends Finsupp.single i 1 to Xᵢ. -/
theorem polynomialGeneratorLinear_single (i : σ) :
    polynomialGeneratorLinear k σ (Finsupp.single i (1 : k)) = MvPolynomial.X i := by
  rw [polynomialGeneratorLinear, Finsupp.linearCombination_single, one_smul]

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. Under E ⊗[k] V ≅ ⊕ᵢ∈σ E·eᵢ, the generator-difference functional becomes the E-linear
functional eᵢ ↦ Xᵢ ⊗ 1 − 1 ⊗ Xᵢᵐᵒᵖ, denoted δᵢ. The equality is stated after precomposition with
the inverse scalar-coordinate isomorphism. -/
theorem polynomialGeneratorDifference_comp_scalarCoordinates :
    (AdjacentBar.generatorDifferenceFunctional k A V (polynomialGeneratorLinear k σ)).comp
        (Finsupp.scalarExtensionCoordinates k E σ).symm.toLinearMap =
      KoszulComplex.finsuppFunctional E δ := by
  classical
  apply LinearMap.ext
  intro z
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single i r =>
    have hs : (Finsupp.scalarExtensionCoordinates k E σ).symm.toLinearMap
        (Finsupp.single i r) = r ⊗ₜ[k] Finsupp.single i (1 : k) :=
      (congrFun (LinearEquiv.coe_toLinearMap
        (Finsupp.scalarExtensionCoordinates k E σ).symm) (Finsupp.single i r)).trans
          (Finsupp.scalarExtensionCoordinates_symm_single k E σ i r)
    rw [LinearMap.comp_apply, hs,
      AdjacentBar.generatorDifferenceFunctional_tmul, polynomialGeneratorLinear_single,
      KoszulComplex.finsuppFunctional, Finsupp.linearCombination_single]
    rfl

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. The diagonal Koszul complex on the functional eᵢ ↦ δᵢ is isomorphic to the Koszul
complex on E ⊗[k] V with its generator-difference functional. In degree n the map is the nth
exterior power of the inverse free scalar-coordinate isomorphism, so it preserves the Koszul
differential. -/
def polynomialDiagonalScalarExtensionIso : KoszulComplex.polynomialDiagonalComplex k σ ≅
    KoszulComplex.complex E (E ⊗[k] V)
      (AdjacentBar.generatorDifferenceFunctional k A V (polynomialGeneratorLinear k σ)) := by
  let e : VE ≃ₗ[E] (E ⊗[k] V) := (Finsupp.scalarExtensionCoordinates k E σ).symm
  exact KoszulComplex.mapIso E VE (N := E ⊗[k] V) (KoszulComplex.finsuppFunctional E δ)
    (AdjacentBar.generatorDifferenceFunctional k A V (polynomialGeneratorLinear k σ))
    e
    (polynomialGeneratorDifference_comp_scalarCoordinates k σ)

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. Antisymmetrization gives an E-linear chain map from the Koszul complex on E ⊗[k] V to
the enveloping bar resolution. A wedge of n variable generators maps to the sum of their n!
permutation words, weighted by permutation signs, with outer entries equal to 1. -/
def polynomialScalarKoszulToBar :
    KoszulComplex.complex E (E ⊗[k] V)
      (AdjacentBar.generatorDifferenceFunctional k A V (polynomialGeneratorLinear k σ)) ⟶
        AdjacentBar.envelopingBar k A :=
  ChainComplex.ofHom (fun n => by
    letI := TensorPower.outerModule k A n
    exact (ModuleCat.ofHom
      (AdjacentBar.koszulAntisymmetrizationLevel k A V (polynomialGeneratorLinear k σ) n) :
      (KoszulComplex.complex E (E ⊗[k] V)
        (AdjacentBar.generatorDifferenceFunctional k A V (polynomialGeneratorLinear k σ))).X n ⟶
      (AdjacentBar.envelopingBar k A).X n)) (by
      intro n
      rw [KoszulComplex.complex_d_succ]
      apply ModuleCat.hom_ext
      exact AdjacentBar.koszulAntisymmetrizationLevel_boundary
        k A V (polynomialGeneratorLinear k σ) n)

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. Composing the scalar-coordinate isomorphism with Koszul antisymmetrization gives an
E-linear chain map from the polynomial diagonal Koszul resolution to the enveloping bar
resolution, in every degree n : ℕ. -/
def polynomialAntisymmetricBarMap :
    KoszulComplex.polynomialDiagonalComplex k σ ⟶ AdjacentBar.envelopingBar k A :=
  (polynomialDiagonalScalarExtensionIso k σ).hom ≫ polynomialScalarKoszulToBar k σ

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. For n : ℕ and f : Fin n → σ, the comparison sends e_{f(0)}∧…∧e_{f(n−1)} to ∑π
sign(π)·(1 ⊗ X_{f(π(0))} ⊗ … ⊗ X_{f(π(n−1))} ⊗ 1), where π ranges over permutations of Fin n. -/
theorem polynomialAntisymmetricBarMap_basis (n : ℕ) (f : Fin n → σ) :
    ((polynomialAntisymmetricBarMap k σ).f n).hom
      (exteriorPower.ιMulti E n (fun j => Finsupp.single (f j) (1 : E))) =
      AdjacentBar.antisymmetricBarWord k A n (fun j => MvPolynomial.X (f j)) := by
  let z : ⋀[E]^n VE := exteriorPower.ιMulti E n (fun j => Finsupp.single (f j) (1 : E))
  let K := AdjacentBar.koszulAntisymmetrizationLevel k A V (polynomialGeneratorLinear k σ) n
  have hc : (polynomialDiagonalScalarExtensionIso k σ).hom.f n =
      ModuleCat.ofHom (exteriorPower.map n
        (Finsupp.scalarExtensionCoordinates k E σ).symm.toLinearMap) := by
    dsimp only [polynomialDiagonalScalarExtensionIso]
    exact KoszulComplex.mapIso_hom_f E VE (N := E ⊗[k] V) (KoszulComplex.finsuppFunctional E δ)
      (AdjacentBar.generatorDifferenceFunctional k A V (polynomialGeneratorLinear k σ))
      (Finsupp.scalarExtensionCoordinates k E σ).symm
      (polynomialGeneratorDifference_comp_scalarCoordinates k σ) n
  have hstart : ((polynomialAntisymmetricBarMap k σ).f n).hom z =
      K (exteriorPower.map n (Finsupp.scalarExtensionCoordinates k E σ).symm.toLinearMap z) :=
    (ModuleCat.comp_apply ((polynomialDiagonalScalarExtensionIso k σ).hom.f n)
      ((polynomialScalarKoszulToBar k σ).f n) z).trans
        (congrArg ((polynomialScalarKoszulToBar k σ).f n).hom
          (ConcreteCategory.congr_hom hc z))
  have hw : exteriorPower.map n (Finsupp.scalarExtensionCoordinates k E σ).symm.toLinearMap z =
      exteriorPower.ιMulti E n (fun j => (1 : E) ⊗ₜ[k] Finsupp.single (f j) (1 : k)) := by
    rw [exteriorPower.map_apply_ιMulti]
    apply congrArg (exteriorPower.ιMulti E n)
    funext j
    exact (congrFun (LinearEquiv.coe_toLinearMap
      (Finsupp.scalarExtensionCoordinates k E σ).symm) (Finsupp.single (f j) (1 : E))).trans
        (Finsupp.scalarExtensionCoordinates_symm_single k E σ (f j) (1 : E))
  refine hstart.trans ((congrArg K hw).trans ?_)
  have hg : (polynomialGeneratorLinear k σ) ∘ (fun j => Finsupp.single (f j) (1 : k)) =
      (fun j => MvPolynomial.X (f j)) := funext fun j => polynomialGeneratorLinear_single k σ (f j)
  exact (AdjacentBar.koszulAntisymmetrizationLevel_ιMulti k A V (polynomialGeneratorLinear k σ) n
    (fun j => Finsupp.single (f j) (1 : k))).trans
      (congrArg (AdjacentBar.antisymmetricBarWord k A n) hg)

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. For e ∈ E and an exterior word indexed by f : Fin n → σ, the bar comparison sends e
times that wedge to e times its signed permutation bar word. The scalar acts through the
E-module structure on the bar resolution. -/
theorem polynomialAntisymmetricBarMap_smul_basis
    (n : ℕ) (e : E) (f : Fin n → σ) :
    ((polynomialAntisymmetricBarMap k σ).f n).hom
      (e • exteriorPower.ιMulti E n (fun j => Finsupp.single (f j) (1 : E))) =
      e • AdjacentBar.antisymmetricBarWord k A n (fun j => MvPolynomial.X (f j)) := by
  let F : (⋀[E]^n VE) →ₗ[E] AdjacentBar.envelopingBarDegree k A n :=
    ((polynomialAntisymmetricBarMap k σ).f n).hom
  exact (F.map_smul e (exteriorPower.ιMulti E n
    (fun j => Finsupp.single (f j) (1 : E)))).trans
      (congrArg (fun z : AdjacentBar.envelopingBarDegree k A n => e • z)
        (polynomialAntisymmetricBarMap_basis k σ n f))

private theorem regularEnvelopingAction_multiplication (e : E) (a : A) :
    AdjacentBar.regularEnvelopingAction k A e a =
      MvPolynomial.diagonalMultiplication k σ e * a := by
  induction e using TensorProduct.inductionOn with
  | tmul l r =>
    have h := MvPolynomial.diagonalMultiplication_tmul k σ l r.unop
    rw [op_unop] at h
    rw [AdjacentBar.regularEnvelopingAction, AlgHom.mulLeftRight_apply, h]
    ac_rfl
  | add e e' he he' =>
    simp only [map_add, LinearMap.add_apply, add_mul, he, he']

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. For z in the degree-zero exterior power over E, applying the degree-zero
antisymmetric bar map and then the bar augmentation equals the polynomial diagonal augmentation
of z. Both augmentations use multiplication E → A. -/
theorem polynomialAntisymmetricBarMap_augmentation_apply (z : ⋀[E]^0 VE) :
    ((AdjacentBar.envelopingBarAugmentationMap k A).f 0).hom
      (((polynomialAntisymmetricBarMap k σ).f 0).hom z) =
      ((KoszulComplex.polynomialDiagonalAugmentation k σ).f 0).hom z := by
  rw [AdjacentBar.envelopingBarAugmentationMap_f_zero]
  let r := exteriorPower.zeroEquiv E VE z
  let f0 : Fin 0 → σ := fun j => Fin.elim0 j
  have hz : z = r • exteriorPower.ιMulti E 0
      (fun j => Finsupp.single (f0 j) (1 : E)) := by
    apply (exteriorPower.zeroEquiv E VE).injective
    rw [map_smul, exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]
  let F : (⋀[E]^0 VE) →ₗ[E] AdjacentBar.envelopingBarDegree k A 0 :=
    ((polynomialAntisymmetricBarMap k σ).f 0).hom
  let g : AdjacentBar.envelopingBarDegree k A 0 →ₗ[E]
      AdjacentBar.regularEnvelopingTarget k A := (AdjacentBar.envelopingBarAugmentation k A).hom
  let d : (⋀[E]^0 VE) →ₗ[E] AdjacentBar.regularEnvelopingTarget k A :=
    ((KoszulComplex.polynomialDiagonalAugmentation k σ).f 0).hom
  let x : AdjacentBar.envelopingBarDegree k A 0 :=
    AdjacentBar.antisymmetricBarWord k A 0 (fun j => MvPolynomial.X (f0 j))
  let a1 : AdjacentBar.regularEnvelopingTarget k A := ULift.up (1 : A)
  let ar : AdjacentBar.regularEnvelopingTarget k A :=
    ULift.up (MvPolynomial.diagonalMultiplication k σ r)
  have hF : F z = r • x :=
    (congrArg F hz).trans (polynomialAntisymmetricBarMap_smul_basis k σ 0 r f0)
  have hw : AdjacentBar.antisymmetricBarWord k A 0
      (fun j : Fin 0 => MvPolynomial.X (Fin.elim0 j)) =
      AdjacentBar.unitOuterWord k A 0 (fun j : Fin 0 => Fin.elim0 j) := by
    simp only [AdjacentBar.antisymmetricBarWord, Finset.univ_unique, Finset.sum_singleton]
    let a : Fin 0 → A := (fun j => MvPolynomial.X (Fin.elim0 j)) ∘ ⇑(default : Equiv.Perm (Fin 0))
    have hs : ((default : Equiv.Perm (Fin 0)).sign : ℤ) = 1 := by
      have hp : (default : Equiv.Perm (Fin 0)) = 1 := Subsingleton.elim _ _
      simp only [hp, Equiv.Perm.sign_one, Units.val_one]
    exact (congrArg (fun s : ℤ => s • AdjacentBar.unitOuterWord k A 0 a) hs).trans
      ((one_smul ℤ (AdjacentBar.unitOuterWord k A 0 a)).trans
        (congrArg (AdjacentBar.unitOuterWord k A 0) (funext fun j => Fin.elim0 j)))
  have hu : AdjacentBar.underlyingBarAugmentationLinear k A
      (AdjacentBar.unitOuterWord k A 0 (fun j : Fin 0 => Fin.elim0 j)) = (1 : A) := by
    have hl : Fin.snoc (α := fun _ : Fin 1 => A)
        (fun j : Fin 0 => Fin.elim0 j) (1 : A) (0 : Fin 1) = 1 := by
      simpa only [Fin.last_zero] using
        (Fin.snoc_last (α := fun _ : Fin 1 => A) (1 : A) (fun j : Fin 0 => Fin.elim0 j))
    exact (AdjacentBar.underlyingBarAugmentationLinear_tprod k A (1 : A)
      (Fin.snoc (fun j : Fin 0 => Fin.elim0 j) 1)).trans
        ((congrArg (fun a : A => (1 : A) * a) hl).trans (one_mul _))
  have hword : g x = a1 :=
    (congrArg g hw).trans
      ((AdjacentBar.envelopingBarAugmentation_apply k A
        (AdjacentBar.unitOuterWord k A 0 (fun j : Fin 0 => Fin.elim0 j))).trans
          (congrArg ULift.up hu))
  have hleft : g (F z) = r • a1 :=
    (congrArg g hF).trans ((g.map_smul r x).trans
      (congrArg (fun a : AdjacentBar.regularEnvelopingTarget k A => r • a) hword))
  have ha : r • a1 = ar := by
    apply ULift.ext
    change AdjacentBar.regularEnvelopingAction k A r 1 = MvPolynomial.diagonalMultiplication k σ r
    exact (regularEnvelopingAction_multiplication k σ r 1).trans (mul_one _)
  have hd : d z = ar :=
    KoszulComplex.polynomialDiagonalAugmentation_apply k σ z
  exact hleft.trans (ha.trans hd.symm)

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. If F is polynomialAntisymmetricBarMap, εbar the enveloping bar augmentation and εdiag
the polynomial diagonal augmentation, then F ≫ εbar = εdiag as maps to the complex concentrated
in degree zero at the regular E-module A. -/
@[reassoc]
theorem polynomialAntisymmetricBarMap_augmentation :
    polynomialAntisymmetricBarMap k σ ≫ AdjacentBar.envelopingBarAugmentationMap k A =
      KoszulComplex.polynomialDiagonalAugmentation k σ := by
  apply (ChainComplex.toSingle₀Equiv (KoszulComplex.polynomialDiagonalComplex k σ)
    (AdjacentBar.regularEnvelopingTarget k A)).injective
  apply Subtype.ext
  change (polynomialAntisymmetricBarMap k σ).f 0 ≫
    (AdjacentBar.envelopingBarAugmentationMap k A).f 0 =
      (KoszulComplex.polynomialDiagonalAugmentation k σ).f 0
  apply ModuleCat.hom_ext
  ext z
  exact polynomialAntisymmetricBarMap_augmentation_apply k σ z

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. The diagonal-to-bar antisymmetrization is chain homotopic to the inverse map of
barComparison k σ. These are two augmentation-preserving maps between projective resolutions of
the regular E-module A. -/
def polynomialAntisymmetricBarMapHomotopy :
    Homotopy (polynomialAntisymmetricBarMap k σ) (barComparison k σ).inv := by
  let p := P
  let Q := AdjacentBar.envelopingBarProjectiveResolution k A
  let S := ChainComplex.single₀ (ModuleCat E)
  have hid : p.π ≫ S.map (𝟙 (AdjacentBar.regularEnvelopingTarget k A)) = p.π :=
    (congrArg (fun a : S.obj (AdjacentBar.regularEnvelopingTarget k A) ⟶
        S.obj (AdjacentBar.regularEnvelopingTarget k A) => p.π ≫ a)
      (S.map_id (AdjacentBar.regularEnvelopingTarget k A))).trans (Category.comp_id p.π)
  have hf : polynomialAntisymmetricBarMap k σ ≫ Q.π = p.π :=
    (congrArg (fun a : AdjacentBar.envelopingBar k A ⟶
        S.obj (AdjacentBar.regularEnvelopingTarget k A) => polynomialAntisymmetricBarMap k σ ≫ a)
      (AdjacentBar.envelopingBarProjectiveResolution_π k A)).trans
        ((polynomialAntisymmetricBarMap_augmentation k σ).trans
          (KoszulComplex.polynomialDiagonalProjectiveResolution_π k σ).symm)
  have hg : (barComparison k σ).inv ≫ Q.π = p.π :=
    (congrArg (fun a : AdjacentBar.envelopingBar k A ⟶
        S.obj (AdjacentBar.regularEnvelopingTarget k A) => (barComparison k σ).inv ≫ a)
      (AdjacentBar.envelopingBarProjectiveResolution_π k A)).trans
        ((barComparison_inv_augmentation k σ).trans
          (KoszulComplex.polynomialDiagonalProjectiveResolution_π k σ).symm)
  exact ProjectiveResolution.liftHomotopy (𝟙 (AdjacentBar.regularEnvelopingTarget k A))
    («P» := p) (Q := Q) (polynomialAntisymmetricBarMap k σ) (barComparison k σ).inv
    (hf.trans hid.symm) (hg.trans hid.symm)

section Coefficients

variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module (MvPolynomial σ k) M] [Module (MvPolynomial σ k)ᵐᵒᵖ M]
  [SMulCommClass (MvPolynomial σ k) (MvPolynomial σ k)ᵐᵒᵖ M]
  [SMulCommClass k (MvPolynomial σ k) M] [SMulCommClass k (MvPolynomial σ k)ᵐᵒᵖ M]
  [IsScalarTower k (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k)ᵐᵒᵖ M]

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. Let M be an A-bimodule whose two A-actions commute and are compatible with its
k-module structure. Tensoring the E-linear diagonal-to-bar antisymmetrization with M over E and
then cancelling the bar endpoints gives a k-linear chain map from coefficientComplex k σ M to
the Hochschild chain complex Cₙ(A,M) = M ⊗[k] A^{⊗n}. -/
def polynomialAntisymmetricCoefficientMap :
    coefficientComplex k σ M ⟶ ModuleCat.Algebra.Hochschild.chainComplex k A M :=
  ((AdjacentBar.coefficientTensorFunctor k A M).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (polynomialAntisymmetricBarMap k σ) ≫ (AdjacentBar.coefficientTensorChainIso k A M).hom

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. Let M be an A-bimodule whose two A-actions commute and are compatible with its
k-module structure. The antisymmetric coefficient chain map is homotopic to the inverse of
coefficientComparison k σ M. This homotopy is obtained by tensoring the augmentation-preserving
resolution homotopy with M, and imposes no flatness or projectivity condition on M. -/
def polynomialAntisymmetricCoefficientMapHomotopy :
    Homotopy (polynomialAntisymmetricCoefficientMap k σ M) (coefficientComparison k σ M).inv :=
  ((AdjacentBar.coefficientTensorFunctor k A M).mapHomotopy
    (polynomialAntisymmetricBarMapHomotopy k σ)).compRight
      (AdjacentBar.coefficientTensorChainIso k A M).hom

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. Let M be an A-bimodule whose two A-actions commute and are compatible with its
k-module structure. The coefficient diagonal complex and the Hochschild chain complex are
homotopy equivalent, with polynomialAntisymmetricCoefficientMap as the forward map. The
equivalence is obtained from the comparison of projective resolutions. -/
def polynomialAntisymmetricCoefficientComparison :
    HomotopyEquiv (coefficientComplex k σ M) (ModuleCat.Algebra.Hochschild.chainComplex k A M) :=
  (coefficientComparison k σ M).symm.copy
    (polynomialAntisymmetricCoefficientMapHomotopy k σ M).symm

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. Let M be an A-bimodule whose two A-actions commute and are compatible with its
k-module structure. The forward map of polynomialAntisymmetricCoefficientComparison k σ M is
polynomialAntisymmetricCoefficientMap k σ M. -/
theorem polynomialAntisymmetricCoefficientComparison_hom :
    (polynomialAntisymmetricCoefficientComparison k σ M).hom =
      polynomialAntisymmetricCoefficientMap k σ M := rfl

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. Let M be an A-bimodule whose two A-actions commute and are compatible with its
k-module structure. In every degree n : ℕ, the homology map of
polynomialAntisymmetricCoefficientMap equals the homology map of (coefficientComparison k σ
M).inv. -/
theorem polynomialAntisymmetricCoefficientMap_homology (n : ℕ) :
    HomologicalComplex.homologyMap (polynomialAntisymmetricCoefficientMap k σ M) n =
      HomologicalComplex.homologyMap (coefficientComparison k σ M).inv n :=
  (polynomialAntisymmetricCoefficientMapHomotopy k σ M).homologyMap_eq n

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. Let M be an A-bimodule whose two A-actions commute and are compatible with its
k-module structure. For each n : ℕ, antisymmetrization induces an isomorphism from the nth
homology of the coefficient diagonal complex to HHₙ(A,M). -/
def polynomialAntisymmetricCoefficientHomologyIso (n : ℕ) :
    (coefficientComplex k σ M).homology n ≅
      (ModuleCat.Algebra.Hochschild.chainComplex k A M).homology n :=
  (polynomialAntisymmetricCoefficientComparison k σ M).toHomologyIso n

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. Let M be an A-bimodule whose two A-actions commute and are compatible with its
k-module structure. For m ∈ M and f : Fin n → σ, the comparison sends the balanced tensor m ⊗_E
(e_{f(0)}∧…∧e_{f(n−1)}) to ∑π sign(π)·(m ⊗ X_{f(π(0))} ⊗ … ⊗ X_{f(π(n−1))}), with π ranging over
permutations of Fin n. -/
theorem polynomialAntisymmetricCoefficientMap_mk_basis
    (n : ℕ) (m : M) (f : Fin n → σ) :
    letI := EnvelopingCoefficient.rightEnvelopingModule k A M
    letI : Module k (⋀[E]^n VE) := Module.compHom _ (algebraMap k E)
    ((polynomialAntisymmetricCoefficientMap k σ M).f n).hom
      (TensorProduct.Balanced.mk k E M (⋀[E]^n VE) m
        (exteriorPower.ιMulti E n (fun j => Finsupp.single (f j) (1 : E)))) =
      ∑ π : Equiv.Perm (Fin n), (π.sign : ℤ) •
        (m ⊗ₜ[k] PiTensorProduct.tprod k (fun j => MvPolynomial.X (f (π j)))) := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI : Module k (⋀[E]^n VE) := Module.compHom _ (algebraMap k E)
  letI : Module k (AdjacentBar.envelopingBarDegree k A n) := Module.compHom _ (algebraMap k E)
  let z : (coefficientComplex k σ M).X n :=
    TensorProduct.Balanced.mk k E M (⋀[E]^n VE) m
      (exteriorPower.ιMulti E n (fun j => Finsupp.single (f j) (1 : E)))
  let T : (coefficientComplex k σ M).X n ⟶ (AdjacentBar.coefficientTensorComplex k A M).X n :=
    (AdjacentBar.coefficientTensorFunctor k A M).map ((polynomialAntisymmetricBarMap k σ).f n)
  let q : AdjacentBar.envelopingBarDegree k A n →ₗ[k]
      (AdjacentBar.coefficientTensorComplex k A M).X n :=
    TensorProduct.Balanced.mk k E M (AdjacentBar.envelopingBarDegree k A n).carrier m
  let c : (AdjacentBar.coefficientTensorComplex k A M).X n ≃ₗ[k] M ⊗[k] TensorPower k n A :=
    AdjacentBar.coefficientTensorLevelEquiv k A M n
  let J : (AdjacentBar.coefficientTensorComplex k A M).X n →ₗ[k] M ⊗[k] TensorPower k n A :=
    ((AdjacentBar.coefficientTensorChainIso k A M).hom.f n).hom
  let L := c.toLinearMap.comp q
  let y := q (AdjacentBar.antisymmetricBarWord k A n (fun j => MvPolynomial.X (f j)))
  have hT : T.hom z = y :=
    (ModuleCat.BalancedTensor.map_mk k E M ((polynomialAntisymmetricBarMap k σ).f n) m
      (exteriorPower.ιMulti E n (fun j => Finsupp.single (f j) (1 : E)))).trans
        (congrArg q (polynomialAntisymmetricBarMap_basis k σ n f))
  have hstart : ((polynomialAntisymmetricCoefficientMap k σ M).f n).hom z = J y :=
    (ModuleCat.comp_apply T ((AdjacentBar.coefficientTensorChainIso k A M).hom.f n) z).trans
      (congrArg J hT)
  have hJ : J y = c y :=
    (LinearMap.congr_fun (AdjacentBar.coefficientTensorChainIso_hom_f k A M n) y).trans
      (congrFun (LinearEquiv.coe_toLinearMap c) y)
  have hL (a : AdjacentBar.envelopingBarDegree k A n) : c (q a) = L a :=
    (congrFun (LinearEquiv.coe_toLinearMap c) (q a)).symm.trans
      (LinearMap.comp_apply c.toLinearMap q a).symm
  have hformula : L (AdjacentBar.antisymmetricBarWord k A n (fun j => MvPolynomial.X (f j))) =
      ∑ π : Equiv.Perm (Fin n), (π.sign : ℤ) •
        (m ⊗ₜ[k] PiTensorProduct.tprod k (fun j => MvPolynomial.X (f (π j)))) := by
    rw [AdjacentBar.antisymmetricBarWord, map_sum]
    simp only [map_zsmul]
    apply Finset.sum_congr rfl
    intro π _
    apply congrArg (fun a : M ⊗[k] TensorPower k n A => (π.sign : ℤ) • a)
    have hc := AdjacentBar.coefficientTensorLevelEquiv_mk_tprod k A M n m (1 : A)
      (Fin.snoc (fun j => MvPolynomial.X (f (π j))) 1)
    simp only [Fin.snoc_last, Fin.init_snoc, op_one, one_smul] at hc
    exact (hL _).symm.trans hc
  exact hstart.trans (hJ.trans ((hL _).trans hformula))

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. Let M be an A-bimodule whose two A-actions commute and are compatible with its
k-module structure. Identify the degree-n coefficient diagonal term with M ⊗[k] ∧ⁿₖV using
coefficientFreeExteriorEquiv. The inverse-coordinate image of m ⊗ (e_{f(0)}∧…∧e_{f(n−1)}) maps
to ∑π sign(π)·(m ⊗ X_{f(π(0))} ⊗ … ⊗ X_{f(π(n−1))}). -/
theorem polynomialAntisymmetricCoefficientMap_free_basis
    (n : ℕ) (m : M) (f : Fin n → σ) :
    ((polynomialAntisymmetricCoefficientMap k σ M).f n).hom
      ((coefficientFreeExteriorEquiv k σ M n).symm
        (m ⊗ₜ[k] exteriorPower.ιMulti k n (fun j => Finsupp.single (f j) (1 : k)))) =
      ∑ π : Equiv.Perm (Fin n), (π.sign : ℤ) •
        (m ⊗ₜ[k] PiTensorProduct.tprod k (fun j => MvPolynomial.X (f (π j)))) := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI : Module k (⋀[E]^n VE) := Module.compHom _ (algebraMap k E)
  rw [coefficientFreeExteriorEquiv_symm_tmul_basis,
    polynomialAntisymmetricCoefficientMap_mk_basis]

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. Let M be an A-bimodule whose two A-actions commute and are compatible with its
k-module structure. Precomposing the degree-n antisymmetric coefficient map with
coefficientFreeExteriorEquiv⁻¹ gives id_M ⊗ exteriorAntisymmetrizationAlong(X), a k-linear map
from M ⊗[k] ∧ⁿₖV to M ⊗[k] A^{⊗n}. -/
theorem polynomialAntisymmetricCoefficientMap_free_coordinates (n : ℕ) :
    ((polynomialAntisymmetricCoefficientMap k σ M).f n).hom.comp
        (coefficientFreeExteriorEquiv k σ M n).symm.toLinearMap =
      TensorProduct.map LinearMap.id
        (AdjacentBar.exteriorAntisymmetrizationAlong k A V (polynomialGeneratorLinear k σ) n) := by
  let F : (M ⊗[k] (⋀[k]^n V)) →ₗ[k] (ModuleCat.Algebra.Hochschild.chainComplex k A M).X n :=
    ((polynomialAntisymmetricCoefficientMap k σ M).f n).hom.comp
      (coefficientFreeExteriorEquiv k σ M n).symm.toLinearMap
  let T : (M ⊗[k] (⋀[k]^n V)) →ₗ[k] (ModuleCat.Algebra.Hochschild.chainComplex k A M).X n :=
    TensorProduct.map LinearMap.id
      (AdjacentBar.exteriorAntisymmetrizationAlong k A V (polynomialGeneratorLinear k σ) n)
  change F = T
  apply TensorProduct.curry_injective
  apply LinearMap.ext
  intro m
  apply exteriorPower.linearMap_ext
  apply (Finsupp.basisSingleOne (R := k) (ι := σ)).ext_alternating
  intro f _
  simp only [Finsupp.coe_basisSingleOne]
  let z := m ⊗ₜ[k] exteriorPower.ιMulti k n (fun j => Finsupp.single (f j) (1 : k))
  have hFval : ((TensorProduct.curry F m).compAlternatingMap (exteriorPower.ιMulti k n))
      (fun j => Finsupp.single (f j) (1 : k)) = F z :=
    (LinearMap.compAlternatingMap_apply (TensorProduct.curry F m) (exteriorPower.ιMulti k n)
      (fun j => Finsupp.single (f j) (1 : k))).trans
        (TensorProduct.curry_apply F m (exteriorPower.ιMulti k n (fun j => Finsupp.single (f j) (1 : k))))
  have hTval : ((TensorProduct.curry T m).compAlternatingMap (exteriorPower.ιMulti k n))
      (fun j => Finsupp.single (f j) (1 : k)) = T z :=
    (LinearMap.compAlternatingMap_apply (TensorProduct.curry T m) (exteriorPower.ιMulti k n)
      (fun j => Finsupp.single (f j) (1 : k))).trans
        (TensorProduct.curry_apply T m (exteriorPower.ιMulti k n (fun j => Finsupp.single (f j) (1 : k))))
  have hF : F z = ∑ π : Equiv.Perm (Fin n), (π.sign : ℤ) •
      (m ⊗ₜ[k] PiTensorProduct.tprod k (fun j => MvPolynomial.X (f (π j)))) :=
    (LinearMap.comp_apply ((polynomialAntisymmetricCoefficientMap k σ M).f n).hom
      (coefficientFreeExteriorEquiv k σ M n).symm.toLinearMap z).trans
        ((congrArg ((polynomialAntisymmetricCoefficientMap k σ M).f n).hom
          (congrFun (LinearEquiv.coe_toLinearMap (coefficientFreeExteriorEquiv k σ M n).symm) z)).trans
            (polynomialAntisymmetricCoefficientMap_free_basis k σ M n m f))
  have hT : T z = ∑ π : Equiv.Perm (Fin n), (π.sign : ℤ) •
      (m ⊗ₜ[k] PiTensorProduct.tprod k (fun j => MvPolynomial.X (f (π j)))) := by
    have hs : TensorProduct.map (LinearMap.id : M →ₗ[k] M)
        (AdjacentBar.exteriorAntisymmetrizationAlong k A V (polynomialGeneratorLinear k σ) n) z =
        ∑ π : Equiv.Perm (Fin n), (π.sign : ℤ) •
          (m ⊗ₜ[k] PiTensorProduct.tprod k (fun j => MvPolynomial.X (f (π j)))) := by
      rw [TensorProduct.map_tmul, LinearMap.id_apply,
        AdjacentBar.exteriorAntisymmetrizationAlong_ιMulti]
      simp only [Function.comp_def, polynomialGeneratorLinear_single, TensorProduct.tmul_sum]
      apply Finset.sum_congr rfl
      intro π _
      exact map_zsmul (TensorProduct.mk k M (TensorPower k n A) m) _ _
    exact hs
  exact hFval.trans ((hF.trans hT.symm).trans hTval.symm)

end Coefficients

section Symmetric

variable (M : Type w) [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [SMulCommClass k (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k) M]

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. Let M be an A-module with compatible k-action, regarded as a symmetric A-bimodule.
The coefficient diagonal differential is zero. Taking its cycle classes and applying the
antisymmetric coefficient map defines a k-linear map M ⊗[k] ∧ⁿₖV → HHₙ(A,M) for every n : ℕ. -/
def polynomialAntisymmetricExteriorClass (n : ℕ) :
    M ⊗[k] (⋀[k]^n V) →ₗ[k] (Symmetric.chainComplex k A M).homology n := by
  letI := Symmetric.opModule A M
  letI := Symmetric.actionsComm A M
  letI := Symmetric.kOpComm k A M
  letI := Symmetric.kOpTower k A M
  exact (HomologicalComplex.zeroDifferentialClassMap (symmetricCoefficientComplex k σ M) n
      (symmetricCoefficientComplex_d_eq_zero k σ M) ≫
    HomologicalComplex.homologyMap (polynomialAntisymmetricCoefficientMap k σ M) n).hom.comp
      (symmetricFreeExteriorEquiv k σ M n).symm.toLinearMap

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. Let M be an A-module with compatible k-action, regarded as a symmetric A-bimodule. In
degree n : ℕ, polynomialAntisymmetricExteriorClass equals symmetricHochschildFreeExteriorClass.
Thus the signed chain construction and the diagonal resolution comparison define the same
Hochschild classes. -/
theorem polynomialAntisymmetricExteriorClass_eq_diagonal (n : ℕ) :
    polynomialAntisymmetricExteriorClass k σ M n = symmetricHochschildFreeExteriorClass k σ M n := by
  letI := Symmetric.opModule A M
  letI := Symmetric.actionsComm A M
  letI := Symmetric.kOpComm k A M
  letI := Symmetric.kOpTower k A M
  unfold polynomialAntisymmetricExteriorClass symmetricHochschildFreeExteriorClass
  rw [polynomialAntisymmetricCoefficientMap_homology]
  rfl

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. Let M be an A-module with compatible k-action, regarded as a symmetric A-bimodule.
For n : ℕ and x ∈ M ⊗[k] ∧ⁿₖV, the free exterior coordinate map sends
polynomialAntisymmetricExteriorClass k σ M n x back to x. -/
theorem polynomialAntisymmetricExteriorClass_coordinates
    (n : ℕ) (x : M ⊗[k] (⋀[k]^n V)) :
    symmetricHochschildFreeExteriorEquiv k σ M n
      (polynomialAntisymmetricExteriorClass k σ M n x) = x := by
  rw [polynomialAntisymmetricExteriorClass_eq_diagonal,
    symmetricHochschildFreeExteriorClass_coordinates]

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. Let M be an A-module with compatible k-action, regarded as a symmetric A-bimodule.
The polynomial differential-coordinate isomorphism M ⊗[k] ∧ⁿₖV ≅ M ⊗[A] ∧ⁿ_AΩ¹_{A/k}, followed
in reverse by the signed exterior class map, defines polynomialAntisymmetrizationHomology from
coefficient n-forms to HHₙ(A,M). -/
def polynomialAntisymmetrizationHomology (n : ℕ) :
    M ⊗[A] (⋀[A]^n (KaehlerDifferential k A)) →ₗ[k]
      (Symmetric.chainComplex k A M).homology n :=
  (polynomialAntisymmetricExteriorClass k σ M n).comp
    ((KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv k σ M n).symm.restrictScalars k).toLinearMap

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. Let M be an A-module with compatible k-action, regarded as a symmetric A-bimodule.
For m ∈ M and f : Fin n → σ, antisymmetrization sends m ⊗ (dX_{f(0)}∧…∧dX_{f(n−1)}) to the
signed exterior Hochschild class of m ⊗ (e_{f(0)}∧…∧e_{f(n−1)}). -/
theorem polynomialAntisymmetrizationHomology_basis
    (n : ℕ) (m : M) (f : Fin n → σ) :
    polynomialAntisymmetrizationHomology k σ M n
      (m ⊗ₜ[A] exteriorPower.ιMulti A n
        (fun j => KaehlerDifferential.D k A (MvPolynomial.X (f j)))) =
      polynomialAntisymmetricExteriorClass k σ M n
        (m ⊗ₜ[k] exteriorPower.ιMulti k n (fun j => Finsupp.single (f j) (1 : k))) := by
  let z := m ⊗ₜ[A] exteriorPower.ιMulti A n
    (fun j => KaehlerDifferential.D k A (MvPolynomial.X (f j)))
  let e := (KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv k σ M n).symm
  have hc : (e.restrictScalars k).toLinearMap z = e z :=
    (congrFun (LinearEquiv.coe_toLinearMap (e.restrictScalars k)) z).trans
      (LinearEquiv.restrictScalars_apply k e z)
  exact congrArg (polynomialAntisymmetricExteriorClass k σ M n)
    (hc.trans (KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv_symm_tmul_basis k σ M n m f))

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. Let M be an A-module with compatible k-action, regarded as a symmetric A-bimodule.
For every coefficient n-form ω, applying polynomialAntisymmetrizationHomology and then
symmetricHochschildDifferentialFormEquiv returns ω. -/
theorem polynomialAntisymmetrizationHomology_coordinates
    (n : ℕ) (ω : M ⊗[A] (⋀[A]^n (KaehlerDifferential k A))) :
    symmetricHochschildDifferentialFormEquiv k σ M n
      (polynomialAntisymmetrizationHomology k σ M n ω) = ω := by
  change KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv k σ M n
    (symmetricHochschildFreeExteriorEquiv k σ M n
      (polynomialAntisymmetricExteriorClass k σ M n
        ((KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv k σ M n).symm ω))) = ω
  rw [polynomialAntisymmetricExteriorClass_coordinates, LinearEquiv.apply_symm_apply]

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. Let M be an A-module with compatible k-action, regarded as a symmetric A-bimodule.
For every n : ℕ there is a k-linear equivalence M ⊗[A] ∧ⁿ_AΩ¹_{A/k} ≅ HHₙ(A,M), inverse to the
differential-form coordinates obtained from the diagonal projective resolution. Its forward map
is the signed antisymmetrization. -/
def polynomialAntisymmetrizationHomologyEquiv (n : ℕ) :
    M ⊗[A] (⋀[A]^n (KaehlerDifferential k A)) ≃ₗ[k]
      (Symmetric.chainComplex k A M).homology n :=
  (symmetricHochschildDifferentialFormEquiv k σ M n).symm

/-- Let k be a commutative ring and σ any set of variables. Put A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and V =
⊕ᵢ∈σ k·eᵢ. Let M be an A-module with compatible k-action, regarded as a symmetric A-bimodule.
The underlying k-linear map of polynomialAntisymmetrizationHomologyEquiv k σ M n equals
polynomialAntisymmetrizationHomology k σ M n in every degree n : ℕ. -/
theorem polynomialAntisymmetrizationHomologyEquiv_toLinearMap (n : ℕ) :
    (polynomialAntisymmetrizationHomologyEquiv k σ M n).toLinearMap =
      polynomialAntisymmetrizationHomology k σ M n := by
  ext ω
  apply (symmetricHochschildDifferentialFormEquiv k σ M n).injective
  rw [polynomialAntisymmetrizationHomology_coordinates]
  exact LinearEquiv.apply_symm_apply _ _

end Symmetric

end ModuleCat.Algebra.Hochschild.PolynomialDiagonal
