/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.PolynomialCoefficientAlgebraComparison
public import MathlibExt.Algebra.Homology.Hochschild.PolynomialDiagonalFormCoordinates

/-!
# Algebra naturality of polynomial coefficient-form homology

Let k be a commutative ring, A = k[σ], B = k[τ], and let M and N be compatible symmetric
coefficient modules. A k-algebra map g : A → B and a k-linear map f : M → N satisfying f(a·m) =
g(a)·f(m) induce both a Hochschild word map and a coefficient-form map.

The diagonal Koszul map acts in cotangent coordinates by dXᵢ ↦ d(gXᵢ), the Jacobian action on
polynomial differentials. Its balanced coefficient map commutes with the diagonal-to-form chain
isomorphisms. The homotopy naturality of antisymmetrization then gives the forward and inverse
naturality squares for the polynomial differential-form homology isomorphisms in every degree n
: ℕ.
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
local notation "VS" => σ →₀ k
local notation "DS" => symmetricCoefficientComplex k σ M
local notation "DT" => symmetricCoefficientComplex k τ N
local notation "FS" => Symmetric.coefficientDifferentialFormComplex k AS M
local notation "FT" => Symmetric.coefficientDifferentialFormComplex k AT N

/-- Let k be a commutative ring, A = k[σ] and B = k[τ]. Let M be an A-module and N a B-module, with
their compatible k-actions. M becomes a symmetric A-bimodule by letting aᵐᵒᵖ act on m as a·m.
This defines its module structure over Aᵐᵒᵖ. -/
local instance polynomialFormNaturalitySourceOpModule :
    Module ASᵐᵒᵖ M :=
  Symmetric.opModule AS M
/-- Let k be a commutative ring, A = k[σ] and B = k[τ]. Let M be an A-module and N a B-module, with
their compatible k-actions. With the symmetric right action aᵐᵒᵖ·m = a·m, the A- and
Aᵐᵒᵖ-actions on M commute: a·(bᵐᵒᵖ·m) = bᵐᵒᵖ·(a·m). -/
local instance polynomialFormNaturalitySourceActionsComm :
    SMulCommClass AS ASᵐᵒᵖ M :=
  Symmetric.actionsComm AS M
/-- Let k be a commutative ring, A = k[σ] and B = k[τ]. Let M be an A-module and N a B-module, with
their compatible k-actions. The k-action on M commutes with its symmetric Aᵐᵒᵖ-action:
r·(aᵐᵒᵖ·m) = aᵐᵒᵖ·(r·m). -/
local instance polynomialFormNaturalitySourceGroundOpComm :
    SMulCommClass k ASᵐᵒᵖ M :=
  Symmetric.kOpComm k AS M
/-- Let k be a commutative ring, A = k[σ] and B = k[τ]. Let M be an A-module and N a B-module, with
their compatible k-actions. The symmetric Aᵐᵒᵖ-action on M is compatible with k → Aᵐᵒᵖ:
(r·aᵐᵒᵖ)·m = r·(aᵐᵒᵖ·m). -/
local instance polynomialFormNaturalitySourceGroundOpTower :
    IsScalarTower k ASᵐᵒᵖ M :=
  Symmetric.kOpTower k AS M
/-- Let k be a commutative ring, A = k[σ] and B = k[τ]. Let M be an A-module and N a B-module, with
their compatible k-actions. N becomes a symmetric B-bimodule by letting bᵐᵒᵖ act on n as b·n.
This defines its module structure over Bᵐᵒᵖ. -/
local instance polynomialFormNaturalityTargetOpModule :
    Module ATᵐᵒᵖ N :=
  Symmetric.opModule AT N
/-- Let k be a commutative ring, A = k[σ] and B = k[τ]. Let M be an A-module and N a B-module, with
their compatible k-actions. The B- and symmetric Bᵐᵒᵖ-actions on N commute: b·(cᵐᵒᵖ·n) =
cᵐᵒᵖ·(b·n). -/
local instance polynomialFormNaturalityTargetActionsComm :
    SMulCommClass AT ATᵐᵒᵖ N :=
  Symmetric.actionsComm AT N
/-- Let k be a commutative ring, A = k[σ] and B = k[τ]. Let M be an A-module and N a B-module, with
their compatible k-actions. The k-action on N commutes with its symmetric Bᵐᵒᵖ-action:
r·(bᵐᵒᵖ·n) = bᵐᵒᵖ·(r·n). -/
local instance polynomialFormNaturalityTargetGroundOpComm :
    SMulCommClass k ATᵐᵒᵖ N :=
  Symmetric.kOpComm k AT N
/-- Let k be a commutative ring, A = k[σ] and B = k[τ]. Let M be an A-module and N a B-module, with
their compatible k-actions. The symmetric Bᵐᵒᵖ-action on N is compatible with k → Bᵐᵒᵖ:
(r·bᵐᵒᵖ)·n = r·(bᵐᵒᵖ·n). -/
local instance polynomialFormNaturalityTargetGroundOpTower :
    IsScalarTower k ATᵐᵒᵖ N :=
  Symmetric.kOpTower k AT N
/-- Let k be a commutative ring, A = k[σ] and B = k[τ]. Let M be an A-module and N a B-module, with
their compatible k-actions. M has the right module structure over E_A = A ⊗[k] Aᵐᵒᵖ defined by
m·(a ⊗ bᵐᵒᵖ) = b·(a·m). Symmetry identifies this action with multiplication by ab on M. -/
local instance polynomialFormNaturalitySourceEnvelopingModule :
    Module ESᵐᵒᵖ M :=
  EnvelopingCoefficient.rightEnvelopingModule k AS M
/-- Let k be a commutative ring, A = k[σ] and B = k[τ]. Let M be an A-module and N a B-module, with
their compatible k-actions. N has the right module structure over E_B = B ⊗[k] Bᵐᵒᵖ defined by
n·(b ⊗ cᵐᵒᵖ) = c·(b·n). Symmetry identifies this action with multiplication by bc on N. -/
local instance polynomialFormNaturalityTargetEnvelopingModule :
    Module ETᵐᵒᵖ N :=
  EnvelopingCoefficient.rightEnvelopingModule k AT N

/-- Let k be a commutative ring, A = k[σ] and B = k[τ]. Let M and N be compatible A- and B-modules
with symmetric right actions. Let g : A →ₐ[k] B and f : M →ₗ[k] N satisfy f(a·m) = g(a)·f(m).
Let D_{g,f} be the coefficient diagonal chain map, S_A and S_B the diagonal-to-form chain
isomorphisms and F_{g,f} the coefficient-form map. Then D_{g,f} ≫ S_B.hom = S_A.hom ≫ F_{g,f}.
On form words, F_{g,f} sends m ⊗ (da₁∧…∧daₙ) to f(m) ⊗ (d(g a₁)∧…∧d(g aₙ)). -/
@[reassoc]
theorem polynomialCoefficientDiagonalAlgebraMap_forms :
    polynomialCoefficientDiagonalAlgebraMap k g f hf ≫
        (symmetricCoefficientFormChainIso k τ N).hom =
      (symmetricCoefficientFormChainIso k σ M).hom ≫
        Symmetric.coefficientFormAlgebraComplexMap k g f hf := by
  let d := polynomialCoefficientDiagonalAlgebraMap k g f hf
  let eS := symmetricCoefficientFormChainIso k σ M
  let eT := symmetricCoefficientFormChainIso k τ N
  let F := Symmetric.coefficientFormAlgebraComplexMap k g f hf
  apply HomologicalComplex.hom_ext
  intro n
  let U := ModuleCat.of k (M ⊗[k] (⋀[k]^n VS))
  let E : U ≅ (DS).X n := (symmetricFreeExteriorEquiv k σ M n).symm.toModuleIso
  let d0 : (DS).X n ⟶ (DT).X n := d.f n
  let s0 : (DS).X n ⟶ (FS).X n := eS.hom.f n
  let t0 : (DT).X n ⟶ (FT).X n := eT.hom.f n
  let f0 : (FS).X n ⟶ (FT).X n := F.f n
  let L : (M ⊗[k] (⋀[k]^n VS)) →ₗ[k] (FT).X n :=
    (t0.hom.comp d0.hom).comp E.hom.hom
  let Rf : (M ⊗[k] (⋀[k]^n VS)) →ₗ[k] (FT).X n :=
    (f0.hom.comp s0.hom).comp E.hom.hom
  have hLR : L = Rf := by
    apply TensorProduct.curry_injective
    apply LinearMap.ext
    intro m
    apply exteriorPower.linearMap_ext
    apply (Finsupp.basisSingleOne (R := k) (ι := σ)).ext_alternating
    intro a _
    simp only [Finsupp.coe_basisSingleOne, LinearMap.compAlternatingMap_apply,
      TensorProduct.curry_apply]
    letI : Module k (⋀[ES]^n (σ →₀ ES)) := Module.compHom _ (algebraMap k ES)
    letI : Module k (⋀[ET]^n (τ →₀ ET)) := Module.compHom _ (algebraMap k ET)
    let vS : Fin n → (σ →₀ ES) := fun j => Finsupp.single (a j) (1 : ES)
    let vT : Fin n → (τ →₀ ET) := fun j => MvPolynomial.polynomialDiagonalGeneratorLift k τ g (a j)
    let zS : ⋀[ES]^n (σ →₀ ES) := exteriorPower.ιMulti ES n vS
    let zT : ⋀[ET]^n (τ →₀ ET) := exteriorPower.ιMulti ET n vT
    let qS := TensorProduct.Balanced.mk k ES M (⋀[ES]^n (σ →₀ ES)) m zS
    let qT := TensorProduct.Balanced.mk k ET N (⋀[ET]^n (τ →₀ ET)) (f m) zT
    let w := m ⊗ₜ[k] exteriorPower.ιMulti k n (fun j => Finsupp.single (a j) (1 : k))
    let ωS : (FS).X n := ULift.up (m ⊗ₜ[AS] exteriorPower.ιMulti AS n
      (fun j => KaehlerDifferential.D k AS (MvPolynomial.X (a j))))
    let ωT : (FT).X n := ULift.up (f m ⊗ₜ[AT] exteriorPower.ιMulti AT n
      (fun j => KaehlerDifferential.D k AT (g (MvPolynomial.X (a j)))))
    have hE : E.hom.hom w = qS :=
      coefficientFreeExteriorEquiv_symm_tmul_basis k σ M n m a
    have hD : d0.hom qS = qT := by
      have h := polynomialCoefficientDiagonalAlgebraMap_mk k g f hf n m zS
      have hz : exteriorPower.mapSemilinear (MvPolynomial.polynomialEnvelopingMap k τ g).toRingHom
          (MvPolynomial.polynomialDiagonalGeneratorMap k τ g) n zS = zT := by
        rw [exteriorPower.mapSemilinear_ιMulti]
        apply congrArg (exteriorPower.ιMulti ET n)
        funext j
        simp only [vS, vT, MvPolynomial.polynomialDiagonalGeneratorMap_single, map_one, one_smul]
      exact h.trans (congrArg
        (fun z : ⋀[ET]^n (τ →₀ ET) => TensorProduct.Balanced.mk k ET N
          (⋀[ET]^n (τ →₀ ET)) (f m) z) hz)
    have hsVec : (fun j => diagonalCotangentSemilinearMap k σ (vS j)) =
        (fun j => KaehlerDifferential.D k AS (MvPolynomial.X (a j))) := by
      funext j
      exact diagonalCotangentSemilinearMap_single k σ (a j)
    have htVec : (fun j => diagonalCotangentSemilinearMap k τ (vT j)) =
        (fun j => KaehlerDifferential.D k AT (g (MvPolynomial.X (a j)))) := by
      funext j
      exact (diagonalCotangentSemilinearMap_coordinates k τ (vT j)).trans
        (MvPolynomial.polynomialDiagonalGeneratorLift_coordinates k τ g (a j))
    have hS : s0.hom qS = ωS :=
      (symmetricCoefficientFormChainIso_hom_f k σ M n qS).trans
        ((congrArg (fun z : M ⊗[AS] (⋀[AS]^n (KaehlerDifferential k AS)) =>
            (ULift.up z : (FS).X n))
          (symmetricCoefficientFormDegreeEquiv_mk_ιMulti k σ M n m vS)).trans
            (congrArg (fun v : Fin n → KaehlerDifferential k AS =>
              (ULift.up (m ⊗ₜ[AS] exteriorPower.ιMulti AS n v) : (FS).X n)) hsVec))
    have hT : t0.hom qT = ωT :=
      (symmetricCoefficientFormChainIso_hom_f k τ N n qT).trans
        ((congrArg (fun z : N ⊗[AT] (⋀[AT]^n (KaehlerDifferential k AT)) =>
            (ULift.up z : (FT).X n))
          (symmetricCoefficientFormDegreeEquiv_mk_ιMulti k τ N n (f m) vT)).trans
            (congrArg (fun v : Fin n → KaehlerDifferential k AT =>
              (ULift.up (f m ⊗ₜ[AT] exteriorPower.ιMulti AT n v) : (FT).X n)) htVec))
    have hF : f0.hom ωS = ωT :=
      Symmetric.coefficientFormAlgebraComplexMap_word k g f hf n m
        (fun j => MvPolynomial.X (a j))
    have hL : L w = ωT :=
      (congrArg (fun x => t0.hom (d0.hom x)) hE).trans ((congrArg t0.hom hD).trans hT)
    have hR : Rf w = ωT :=
      (congrArg (fun x => f0.hom (s0.hom x)) hE).trans ((congrArg f0.hom hS).trans hF)
    exact hL.trans hR.symm
  apply (cancel_epi E.hom).1
  exact ModuleCat.hom_ext hLR

/-- Let k be a commutative ring, A = k[σ] and B = k[τ]. Let M and N be compatible A- and B-modules
with symmetric right actions. Let g : A →ₐ[k] B and f : M →ₗ[k] N satisfy f(a·m) = g(a)·f(m).
With D_{g,f} the coefficient diagonal map, S_A and S_B the diagonal-to-form isomorphisms and
F_{g,f} the coefficient-form map, the inverse-coordinate square is S_A.inv ≫ D_{g,f} = F_{g,f} ≫
S_B.inv. -/
@[reassoc]
theorem polynomialCoefficientDiagonalAlgebraMap_forms_inv :
    (symmetricCoefficientFormChainIso k σ M).inv ≫ polynomialCoefficientDiagonalAlgebraMap k g f hf =
      Symmetric.coefficientFormAlgebraComplexMap k g f hf ≫
        (symmetricCoefficientFormChainIso k τ N).inv := by
  let eS := symmetricCoefficientFormChainIso k σ M
  let eT := symmetricCoefficientFormChainIso k τ N
  let d := polynomialCoefficientDiagonalAlgebraMap k g f hf
  let F := Symmetric.coefficientFormAlgebraComplexMap k g f hf
  have h : d ≫ eT.hom = eS.hom ≫ F := polynomialCoefficientDiagonalAlgebraMap_forms k g f hf
  apply (cancel_mono eT.hom).1
  have hLeft : (eS.inv ≫ d) ≫ eT.hom = F :=
    (Category.assoc eS.inv d eT.hom).trans
      ((congrArg (fun t : DS ⟶ FT => eS.inv ≫ t) h).trans
        ((Category.assoc eS.inv eS.hom F).symm.trans
          ((congrArg (fun t : FS ⟶ FS => t ≫ F) eS.inv_hom_id).trans (Category.id_comp F))))
  have hRight : (F ≫ eT.inv) ≫ eT.hom = F :=
    (Category.assoc F eT.inv eT.hom).trans
      ((congrArg (fun t : FT ⟶ FT => F ≫ t) eT.inv_hom_id).trans (Category.comp_id F))
  exact hLeft.trans hRight.symm

/-- Let k be a commutative ring, A = k[σ] and B = k[τ]. Let M and N be compatible A- and B-modules
with symmetric right actions. Let g : A →ₐ[k] B and f : M →ₗ[k] N satisfy f(a·m) = g(a)·f(m).
For n : ℕ, let H_A,H_B be the polynomial Hochschild-to-form homology isomorphisms, C_{g,f} the
Hochschild word map and F_{g,f,n} the coefficient-form map in degree n. Then F_{g,f,n} ≫ H_B.inv
= H_A.inv ≫ Hₙ(C_{g,f}). -/
@[reassoc]
theorem polynomialDifferentialFormHomologyIso_inv_algebra (n : ℕ) :
    (Symmetric.coefficientFormAlgebraComplexMap k g f hf).f n ≫
        (polynomialDifferentialFormHomologyIso k τ N n).inv =
      (polynomialDifferentialFormHomologyIso k σ M n).inv ≫
        HomologicalComplex.homologyMap (Symmetric.originalAlgebraCoefficientChainMap k g f hf) n := by
  let eS := symmetricCoefficientFormChainIso k σ M
  let eT := symmetricCoefficientFormChainIso k τ N
  let d := polynomialCoefficientDiagonalAlgebraMap k g f hf
  let F := Symmetric.coefficientFormAlgebraComplexMap k g f hf
  let aS := polynomialAntisymmetricCoefficientMap k σ M
  let aT := polynomialAntisymmetricCoefficientMap k τ N
  let h := Symmetric.originalAlgebraCoefficientChainMap k g f hf
  let pS := HomologicalComplex.zeroDifferentialClassMap DS n
    (symmetricCoefficientComplex_d_eq_zero k σ M)
  let pT := HomologicalComplex.zeroDifferentialClassMap DT n
    (symmetricCoefficientComplex_d_eq_zero k τ N)
  have he : eS.inv.f n ≫ d.f n = F.f n ≫ eT.inv.f n := by
    have H := congrArg (fun t => t.f n) (polynomialCoefficientDiagonalAlgebraMap_forms_inv k g f hf)
    exact H
  have hp : pS ≫ HomologicalComplex.homologyMap d n = d.f n ≫ pT :=
    HomologicalComplex.zeroDifferentialClassMap_naturality d n
      (symmetricCoefficientComplex_d_eq_zero k σ M)
      (symmetricCoefficientComplex_d_eq_zero k τ N)
  have ha : HomologicalComplex.homologyMap aS n ≫ HomologicalComplex.homologyMap h n =
      HomologicalComplex.homologyMap d n ≫ HomologicalComplex.homologyMap aT n := by
    have H := (polynomialAntisymmetricCoefficientMap_algebraHomotopy k g f hf).homologyMap_eq n
    exact (HomologicalComplex.homologyMap_comp aS h n).symm.trans
      (H.trans (HomologicalComplex.homologyMap_comp d aT n))
  let hs := HomologicalComplex.homologyMap aS n
  let ht := HomologicalComplex.homologyMap aT n
  let hh := HomologicalComplex.homologyMap h n
  let hd := HomologicalComplex.homologyMap d n
  let s0 := eS.inv.f n
  let t0 := eT.inv.f n
  let f0 := F.f n
  let d0 := d.f n
  have factorS : (polynomialDifferentialFormHomologyIso k σ M n).inv = s0 ≫ pS ≫ hs :=
    polynomialDifferentialFormHomologyIso_inv_factor k σ M n
  have factorT : (polynomialDifferentialFormHomologyIso k τ N n).inv = t0 ≫ pT ≫ ht :=
    polynomialDifferentialFormHomologyIso_inv_factor k τ N n
  have h1 : f0 ≫ (polynomialDifferentialFormHomologyIso k τ N n).inv =
      f0 ≫ (t0 ≫ (pT ≫ ht)) :=
    congrArg (fun t : (FT).X n ⟶ (Symmetric.chainComplex k AT N).homology n => f0 ≫ t) factorT
  have h2 : f0 ≫ (t0 ≫ (pT ≫ ht)) = (s0 ≫ d0) ≫ (pT ≫ ht) :=
    (Category.assoc f0 t0 (pT ≫ ht)).symm.trans
      (congrArg (fun t : (FS).X n ⟶ (DT).X n => t ≫ (pT ≫ ht)) he.symm)
  have h3 : (s0 ≫ d0) ≫ (pT ≫ ht) = s0 ≫ ((pS ≫ hd) ≫ ht) :=
    (Category.assoc s0 d0 (pT ≫ ht)).trans
      ((congrArg (fun t : (DS).X n ⟶ (Symmetric.chainComplex k AT N).homology n => s0 ≫ t)
        (Category.assoc d0 pT ht).symm).trans
          (congrArg (fun t : (DS).X n ⟶ (DT).homology n => s0 ≫ (t ≫ ht)) hp.symm))
  have h4 : s0 ≫ ((pS ≫ hd) ≫ ht) = (s0 ≫ pS) ≫ (hs ≫ hh) :=
    (congrArg (fun t : (DS).X n ⟶ (Symmetric.chainComplex k AT N).homology n => s0 ≫ t)
      (Category.assoc pS hd ht)).trans
        ((Category.assoc s0 pS (hd ≫ ht)).symm.trans
          (congrArg (fun t : (DS).homology n ⟶ (Symmetric.chainComplex k AT N).homology n =>
            (s0 ≫ pS) ≫ t) ha.symm))
  have h5 : (s0 ≫ pS) ≫ (hs ≫ hh) =
      (polynomialDifferentialFormHomologyIso k σ M n).inv ≫ hh :=
    (Category.assoc s0 pS (hs ≫ hh)).trans
      ((congrArg (fun t : (DS).X n ⟶ (Symmetric.chainComplex k AT N).homology n => s0 ≫ t)
        (Category.assoc pS hs hh).symm).trans
          ((Category.assoc s0 (pS ≫ hs) hh).symm.trans
            (congrArg (fun t : (FS).X n ⟶ (Symmetric.chainComplex k AS M).homology n => t ≫ hh)
              factorS.symm)))
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

/-- Let k be a commutative ring, A = k[σ] and B = k[τ]. Let M and N be compatible A- and B-modules
with symmetric right actions. Let g : A →ₐ[k] B and f : M →ₗ[k] N satisfy f(a·m) = g(a)·f(m).
For n : ℕ, let H_A,H_B be the polynomial differential-form homology isomorphisms, C_{g,f} the
Hochschild word map and F_{g,f,n} the degree-n coefficient-form map. Then Hₙ(C_{g,f}) ≫ H_B.hom
= H_A.hom ≫ F_{g,f,n}. -/
@[reassoc]
theorem polynomialDifferentialFormHomologyIso_algebra (n : ℕ) :
    HomologicalComplex.homologyMap (Symmetric.originalAlgebraCoefficientChainMap k g f hf) n ≫
        (polynomialDifferentialFormHomologyIso k τ N n).hom =
      (polynomialDifferentialFormHomologyIso k σ M n).hom ≫
        (Symmetric.coefficientFormAlgebraComplexMap k g f hf).f n := by
  let eS := polynomialDifferentialFormHomologyIso k σ M n
  let eT := polynomialDifferentialFormHomologyIso k τ N n
  let h := HomologicalComplex.homologyMap (Symmetric.originalAlgebraCoefficientChainMap k g f hf) n
  let F := (Symmetric.coefficientFormAlgebraComplexMap k g f hf).f n
  have hi : F ≫ eT.inv = eS.inv ≫ h := polynomialDifferentialFormHomologyIso_inv_algebra k g f hf n
  apply (cancel_epi eS.inv).1
  have hLeft : eS.inv ≫ (h ≫ eT.hom) = F :=
    (Category.assoc eS.inv h eT.hom).symm.trans
      ((congrArg (fun t : (FS).X n ⟶ (Symmetric.chainComplex k AT N).homology n => t ≫ eT.hom)
        hi.symm).trans
          ((Category.assoc F eT.inv eT.hom).trans
            ((congrArg (fun t : (FT).X n ⟶ (FT).X n => F ≫ t) eT.inv_hom_id).trans
              (Category.comp_id F))))
  have hRight : eS.inv ≫ (eS.hom ≫ F) = F :=
    (Category.assoc eS.inv eS.hom F).symm.trans
      ((congrArg (fun t : (FS).X n ⟶ (FS).X n => t ≫ F) eS.inv_hom_id).trans (Category.id_comp F))
  exact hLeft.trans hRight.symm

end ModuleCat.Algebra.Hochschild.PolynomialDiagonal
