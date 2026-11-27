/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.PolynomialDiagonalAlgebraMaps
public import MathlibExt.Algebra.Homology.Hochschild.AdjacentBarAlgebraMaps
public import MathlibExt.Algebra.Homology.Hochschild.PolynomialAntisymmetrization
public import MathlibExt.Algebra.Homology.ChainComplex.ProjectiveAugmentationHomotopy

/-!
# Polynomial algebra-change homotopy for the diagonal-to-bar comparison

For a commutative ring k and a polynomial algebra map g : k[σ] → k[τ], let φ be its map on
enveloping algebras. The semilinear diagonal Koszul map commutes with the multiplication
augmentations. The two paths from the source diagonal resolution to the scalar-restricted target
bar resolution therefore have the same composite with the target augmentation.

The source Koszul terms are projective, and the restricted target augmentation is a
quasi-isomorphism. These facts give a chain homotopy between antisymmetrization followed by the
bar algebra map and the diagonal algebra map followed by the restricted target
antisymmetrization. Their induced homology maps agree in every natural-number degree.
Projectivity of the target terms after restriction of scalars is not required.
-/

@[expose] public section
noncomputable section

open CategoryTheory

universe u v

namespace ModuleCat.Algebra.Hochschild.PolynomialDiagonal

variable (k : Type u) [CommRing k] {σ τ : Type v}
  (g : MvPolynomial σ k →ₐ[k] MvPolynomial τ k)

local notation "AS" => MvPolynomial σ k
local notation "AT" => MvPolynomial τ k
local notation "ES" => MvPolynomial.PolynomialEnveloping k σ
local notation "ET" => MvPolynomial.PolynomialEnveloping k τ
local notation "VS" => σ →₀ ES
local notation "VT" => τ →₀ ET
local notation "φ" => MvPolynomial.polynomialEnvelopingMap k τ g
/-- Let k be a commutative ring, A = k[σ], B = k[τ] and g : A →ₐ[k] B. Write E_A and E_B for their
enveloping algebras and φ : E_A → E_B for the map induced by g on both factors. Restriction of
scalars along φ defines a functor from ℕ-indexed chain complexes of left E_B-modules to
ℕ-indexed chain complexes of left E_A-modules. It retains the component groups and differentials
and changes the scalar action through φ. -/
abbrev restrictedComplexFunctor :
    ChainComplex (ModuleCat.{max u v} ET) ℕ ⥤
      ChainComplex (ModuleCat.{max u v} ES) ℕ :=
  Functor.mapHomologicalComplex
    (ModuleCat.restrictScalars.{max u v} (AlgHom.toRingHom (φ))) (.down ℕ)

/-- Let k be a commutative ring, A = k[σ], B = k[τ] and g : A →ₐ[k] B. Write E_A and E_B for their
enveloping algebras and φ : E_A → E_B for the map induced by g on both factors. For z ∈
∧⁰_{E_A}(⊕ᵢ∈σ E_Aeᵢ), let r be its scalar under the degree-zero exterior isomorphism. Applying
the degree-zero diagonal map and then the target augmentation yields g(μ_A(r)), in the regular
target module B, where μ_A : E_A → A is multiplication. -/
theorem polynomialDiagonalRestrictedMap_augmentation_apply (z : ⋀[ES]^0 VS) :
    ((KoszulComplex.polynomialDiagonalAugmentation k τ).f 0).hom
      (((polynomialDiagonalRestrictedMap k g).f 0).hom z) =
      ULift.up (g (MvPolynomial.diagonalMultiplication k σ
        (exteriorPower.zeroEquiv ES VS z))) := by
  let f : (⋀[ES]^0 VS) →ₗ[ES]
      (ModuleCat.restrictScalars.{max u v} ((φ).toRingHom)).obj
        (ModuleCat.of ET (⋀[ET]^0 VT)) :=
    ((polynomialDiagonalRestrictedMap k g).f 0).hom
  let zT : ⋀[ET]^0 VT := f z
  have hScalar : exteriorPower.zeroEquiv ET VT zT =
      φ (exteriorPower.zeroEquiv ES VS z) :=
    polynomialDiagonalRestrictedMap_zero_scalar k g z
  have hMultiplication :
      MvPolynomial.diagonalMultiplication k τ (exteriorPower.zeroEquiv ET VT zT) =
        g (MvPolynomial.diagonalMultiplication k σ (exteriorPower.zeroEquiv ES VS z)) :=
    (congrArg (MvPolynomial.diagonalMultiplication k τ) hScalar).trans
      (MvPolynomial.polynomialEnvelopingMap_multiplication k τ g
        (exteriorPower.zeroEquiv ES VS z))
  exact (KoszulComplex.polynomialDiagonalAugmentation_apply k τ zT).trans
    (congrArg (fun a : AT => (ULift.up a : KoszulComplex.polynomialDiagonalTarget k τ))
      hMultiplication)

/-- Let k be a commutative ring, A = k[σ], B = k[τ] and g : A →ₐ[k] B. Write E_A and E_B for their
enveloping algebras and φ : E_A → E_B for the map induced by g on both factors. Let D_g be
polynomialDiagonalRestrictedMap, ε_A and ε_B the diagonal augmentations, U_φ restriction of
scalars and g[0] the induced map of regular targets concentrated in degree zero. Then D_g ≫
U_φ(ε_B) = ε_A ≫ g[0]. -/
@[reassoc]
theorem polynomialDiagonalRestrictedMap_augmentation :
    polynomialDiagonalRestrictedMap k g ≫
      (restrictedComplexFunctor k g).map (KoszulComplex.polynomialDiagonalAugmentation k τ) =
      KoszulComplex.polynomialDiagonalAugmentation k σ ≫
        AdjacentBar.envelopingBarAlgebraSingleTargetMap k g := by
  let U : ModuleCat.{max u v} ET ⥤ ModuleCat.{max u v} ES :=
    ModuleCat.restrictScalars.{max u v} (AlgHom.toRingHom (φ))
  let F : ChainComplex (ModuleCat.{max u v} ET) ℕ ⥤
      ChainComplex (ModuleCat.{max u v} ES) ℕ :=
    U.mapHomologicalComplex (.down ℕ)
  let singleS : ModuleCat.{max u v} ES ⥤ ChainComplex (ModuleCat.{max u v} ES) ℕ :=
    ChainComplex.single₀ (ModuleCat.{max u v} ES)
  let singleT : ModuleCat.{max u v} ET ⥤ ChainComplex (ModuleCat.{max u v} ET) ℕ :=
    ChainComplex.single₀ (ModuleCat.{max u v} ET)
  let P : ChainComplex (ModuleCat.{max u v} ES) ℕ := KoszulComplex.polynomialDiagonalComplex k σ
  let Q : ChainComplex (ModuleCat.{max u v} ET) ℕ := KoszulComplex.polynomialDiagonalComplex k τ
  let ZS : ModuleCat.{max u v} ES := AdjacentBar.regularEnvelopingTarget k AS
  let ZT : ModuleCat.{max u v} ET := AdjacentBar.regularEnvelopingTarget k AT
  let d : P ⟶ F.obj Q := polynomialDiagonalRestrictedMap k g
  let aS : P ⟶ singleS.obj ZS := KoszulComplex.polynomialDiagonalAugmentation k σ
  let aT : Q ⟶ singleT.obj ZT := KoszulComplex.polynomialDiagonalAugmentation k τ
  let t : singleS.obj ZS ⟶ F.obj (singleT.obj ZT) :=
    AdjacentBar.envelopingBarAlgebraSingleTargetMap k g
  let r : ZS ⟶ U.obj ZT := AdjacentBar.regularEnvelopingTargetAlgebraMap k g
  let e : F.obj (singleT.obj ZT) ≅ singleS.obj (U.obj ZT) :=
    (HomologicalComplex.singleMapHomologicalComplex U (.down ℕ) 0).app ZT
  let j : singleS.obj ZS ⟶ singleS.obj (U.obj ZT) := singleS.map r
  have ht : t ≫ e.hom = j := by
    have hdefinition : t = j ≫ e.inv := rfl
    have hinverse : (j ≫ e.inv) ≫ e.hom = j :=
      (Category.assoc j e.inv e.hom).trans
        ((congrArg (fun h : singleS.obj (U.obj ZT) ⟶ singleS.obj (U.obj ZT) => j ≫ h)
          e.inv_hom_id).trans (Category.comp_id j))
    exact (congrArg (fun h : singleS.obj ZS ⟶ F.obj (singleT.obj ZT) => h ≫ e.hom)
      hdefinition).trans hinverse
  have hright : (aS ≫ t) ≫ e.hom = aS ≫ j :=
    (Category.assoc aS t e.hom).trans
      (congrArg (fun h : singleS.obj ZS ⟶ singleS.obj (U.obj ZT) => aS ≫ h) ht)
  have hleft : (d ≫ F.map aT) ≫ e.hom = aS ≫ j := by
    apply HomologicalComplex.to_single_hom_ext (j := 0)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    let zS : ⋀[ES]^0 VS := z
    let f0 : (⋀[ES]^0 VS) →ₗ[ES] U.obj (ModuleCat.of ET (⋀[ET]^0 VT)) :=
      (d.f 0).hom
    let dS0 : (⋀[ES]^0 VS) →ₗ[ES] ZS := (aS.f 0).hom
    let dT0 : (⋀[ET]^0 VT) →ₗ[ET] ZT := (aT.f 0).hom
    change dT0 (f0 zS) = (ULift.up (g (dS0 zS).down) : ZT)
    have hvalue : dT0 (f0 zS) =
        (ULift.up (g (MvPolynomial.diagonalMultiplication k σ
          (exteriorPower.zeroEquiv ES VS zS))) : ZT) :=
      polynomialDiagonalRestrictedMap_augmentation_apply k g zS
    have hsource : dS0 zS =
        (ULift.up (MvPolynomial.diagonalMultiplication k σ
          (exteriorPower.zeroEquiv ES VS zS)) : ZS) :=
      KoszulComplex.polynomialDiagonalAugmentation_apply k σ zS
    have htargetValue : (ULift.up (g (dS0 zS).down) : ZT) =
        (ULift.up (g (MvPolynomial.diagonalMultiplication k σ
          (exteriorPower.zeroEquiv ES VS zS))) : ZT) :=
      congrArg (fun a : ZS => (ULift.up (g a.down) : ZT)) hsource
    exact hvalue.trans htargetValue.symm
  have hsquare : d ≫ F.map aT = aS ≫ t :=
    (cancel_mono e.hom).1 (hleft.trans hright.symm)
  exact hsquare

/-- Let k be a commutative ring, A = k[σ], B = k[τ] and g : A →ₐ[k] B. Write E_A and E_B for their
enveloping algebras and φ : E_A → E_B for the map induced by g on both factors. Let F_A and F_B
be the antisymmetric diagonal-to-bar comparisons and bar_g the enveloping bar map. There is a
chain homotopy F_A ≫ bar_g ∼ D_g ≫ U_φ(F_B), where D_g is the diagonal map and the common target
is the scalar-restricted bar resolution of B. Projectivity of the source Koszul terms and the
quasi-isomorphic restricted target augmentation construct this homotopy. -/
def polynomialAntisymmetricBarMap_algebraHomotopy :
    Homotopy
      (polynomialAntisymmetricBarMap k σ ≫ AdjacentBar.envelopingBarAlgebraMap k g)
      (polynomialDiagonalRestrictedMap k g ≫
        (restrictedComplexFunctor k g).map (polynomialAntisymmetricBarMap k τ)) := by
  letI (n : ℕ) : Projective ((KoszulComplex.polynomialDiagonalComplex k σ).X n) :=
    KoszulComplex.polynomialDiagonalComplex_projective k σ n
  let U : ModuleCat.{max u v} ET ⥤ ModuleCat.{max u v} ES :=
    ModuleCat.restrictScalars.{max u v} (AlgHom.toRingHom (φ))
  let F : ChainComplex (ModuleCat.{max u v} ET) ℕ ⥤
      ChainComplex (ModuleCat.{max u v} ES) ℕ :=
    U.mapHomologicalComplex (.down ℕ)
  let P : ChainComplex (ModuleCat.{max u v} ES) ℕ := KoszulComplex.polynomialDiagonalComplex k σ
  let B : ChainComplex (ModuleCat.{max u v} ES) ℕ := AdjacentBar.envelopingBar k AS
  let PT : ChainComplex (ModuleCat.{max u v} ET) ℕ := KoszulComplex.polynomialDiagonalComplex k τ
  let BT : ChainComplex (ModuleCat.{max u v} ET) ℕ := AdjacentBar.envelopingBar k AT
  let singleS : ModuleCat.{max u v} ES ⥤ ChainComplex (ModuleCat.{max u v} ES) ℕ :=
    ChainComplex.single₀ (ModuleCat.{max u v} ES)
  let singleT : ModuleCat.{max u v} ET ⥤ ChainComplex (ModuleCat.{max u v} ET) ℕ :=
    ChainComplex.single₀ (ModuleCat.{max u v} ET)
  let TS : ChainComplex (ModuleCat.{max u v} ES) ℕ :=
    singleS.obj (AdjacentBar.regularEnvelopingTarget k AS)
  let TT : ChainComplex (ModuleCat.{max u v} ET) ℕ :=
    singleT.obj (AdjacentBar.regularEnvelopingTarget k AT)
  let cS : P ⟶ B := polynomialAntisymmetricBarMap k σ
  let cT : PT ⟶ BT := polynomialAntisymmetricBarMap k τ
  let d : P ⟶ F.obj PT := polynomialDiagonalRestrictedMap k g
  let b : B ⟶ F.obj BT := AdjacentBar.envelopingBarAlgebraMap k g
  let t : TS ⟶ F.obj TT := AdjacentBar.envelopingBarAlgebraSingleTargetMap k g
  let aS : P ⟶ TS := KoszulComplex.polynomialDiagonalAugmentation k σ
  let aB : B ⟶ TS := AdjacentBar.envelopingBarAugmentationMap k AS
  let aT : PT ⟶ TT := KoszulComplex.polynomialDiagonalAugmentation k τ
  let aBT : BT ⟶ TT := AdjacentBar.envelopingBarAugmentationMap k AT
  let f : P ⟶ F.obj BT := cS ≫ b
  let f' : P ⟶ F.obj BT := d ≫ F.map cT
  let q : F.obj BT ⟶ F.obj TT := F.map aBT
  letI : U.PreservesHomology := inferInstance
  have hq : QuasiIso q := by
    unfold q
    infer_instance
  have hbar : b ≫ q = aB ≫ t :=
    AdjacentBar.envelopingBarAlgebraMap_augmentation k g
  have hsource : cS ≫ aB = aS := polynomialAntisymmetricBarMap_augmentation k σ
  have htarget : cT ≫ aBT = aT := polynomialAntisymmetricBarMap_augmentation k τ
  have hdiagonal : d ≫ F.map aT = aS ≫ t :=
    polynomialDiagonalRestrictedMap_augmentation k g
  have hf : f ≫ q = aS ≫ t :=
    (Category.assoc cS b q).trans
      ((congrArg (fun h : B ⟶ F.obj TT => cS ≫ h) hbar).trans
        ((Category.assoc cS aB t).symm.trans
          (congrArg (fun h : P ⟶ TS => h ≫ t) hsource)))
  have hg : f' ≫ q = aS ≫ t :=
    (Category.assoc d (F.map cT) (F.map aBT)).trans
      ((congrArg (fun h : F.obj PT ⟶ F.obj TT => d ≫ h) (F.map_comp cT aBT).symm).trans
        ((congrArg (fun h : PT ⟶ TT => d ≫ F.map h) htarget).trans hdiagonal))
  exact ChainComplex.projectiveHomotopyOfCompQuasiIso q hq f f' (hf.trans hg.symm)

/-- Let k be a commutative ring, A = k[σ], B = k[τ] and g : A →ₐ[k] B. Write E_A and E_B for their
enveloping algebras and φ : E_A → E_B for the map induced by g on both factors. For every n : ℕ,
the homology maps induced by F_A ≫ bar_g and D_g ≫ U_φ(F_B) are equal, where F_A,F_B are the
antisymmetric diagonal-to-bar comparisons, D_g is the diagonal map and U_φ is restriction of
scalars. -/
theorem polynomialAntisymmetricBarMap_algebra_homology (n : ℕ) :
    HomologicalComplex.homologyMap
        (polynomialAntisymmetricBarMap k σ ≫ AdjacentBar.envelopingBarAlgebraMap k g) n =
      HomologicalComplex.homologyMap
        (polynomialDiagonalRestrictedMap k g ≫
          (restrictedComplexFunctor k g).map (polynomialAntisymmetricBarMap k τ)) n :=
  (polynomialAntisymmetricBarMap_algebraHomotopy k g).homologyMap_eq n

end ModuleCat.Algebra.Hochschild.PolynomialDiagonal
