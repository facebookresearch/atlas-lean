/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.RingTheory.MvPolynomial.EnvelopingDiagonalCotangentLifts
public import MathlibExt.Algebra.Homology.KoszulComplex.Semilinear

/-!
# polynomial algebra maps on diagonal Koszul complexes

An arbitrary polynomial algebra homomorphism maps both original enveloping
factors. The diagonal generator lifts induce a literal Koszul chain
map after scalar restriction. Its every-degree components are the exterior
powers of the semilinear generator map.

The source and target polynomial variable types share an ambient universe;
that ambient universe is independent of the ground-ring universe. The
semilinear generator and exterior APIs retain independent carrier universes.
-/

@[expose] public section
noncomputable section

open CategoryTheory

universe u v

namespace ModuleCat.Algebra.Hochschild.PolynomialDiagonal

variable (k : Type u) [CommRing k] {σ τ : Type v}
  (g : MvPolynomial σ k →ₐ[k] MvPolynomial τ k)

local notation "ES" => MvPolynomial.PolynomialEnveloping k σ
local notation "ET" => MvPolynomial.PolynomialEnveloping k τ
local notation "VS" => σ →₀ ES
local notation "VT" => τ →₀ ET
local notation "xS" => KoszulComplex.finsuppFunctional ES (MvPolynomial.diagonalDifference k σ)
local notation "xT" => KoszulComplex.finsuppFunctional ET (MvPolynomial.diagonalDifference k τ)
local notation "φ" => MvPolynomial.polynomialEnvelopingMap k τ g
local notation "J" => MvPolynomial.polynomialDiagonalGeneratorMap k τ g

/-- The polynomial diagonal map on the original ground-restricted
Koszul complexes, in every degree. -/
def polynomialDiagonalGroundMap :
    ((ModuleCat.restrictScalars (algebraMap k ES)).mapHomologicalComplex (.down ℕ)).obj
        (KoszulComplex.polynomialDiagonalComplex k σ) ⟶
      ((ModuleCat.restrictScalars (algebraMap k ET)).mapHomologicalComplex (.down ℕ)).obj
        (KoszulComplex.polynomialDiagonalComplex k τ) :=
  KoszulComplex.semilinearMap (R := ES) (S := ET) (M := VS) (N := VT) k (φ) xS xT (J)
    (MvPolynomial.polynomialDiagonalGeneratorMap_functional k τ g)

/-- Every original wedge is mapped by the lifted diagonal generators. -/
theorem polynomialDiagonalGroundMap_basis (n : ℕ) (a : Fin n → σ) :
    ((polynomialDiagonalGroundMap k g).f n).hom
      (exteriorPower.ιMulti ES n (fun j => Finsupp.single (a j) (1 : ES))) =
        exteriorPower.ιMulti ET n
          (fun j => MvPolynomial.polynomialDiagonalGeneratorLift k τ g (a j)) := by
  have h := KoszulComplex.semilinearMap_f_ιMulti (R := ES) (S := ET) (M := VS) (N := VT)
    k (φ) xS xT (J) (MvPolynomial.polynomialDiagonalGeneratorMap_functional k τ g) n
      (fun j => Finsupp.single (a j) (1 : ES))
  have hWord : (fun j => J (Finsupp.single (a j) (1 : ES))) =
      (fun j => MvPolynomial.polynomialDiagonalGeneratorLift k τ g (a j)) := by
    funext j
    rw [MvPolynomial.polynomialDiagonalGeneratorMap_single, map_one, one_smul]
  exact h.trans (congrArg (exteriorPower.ιMulti ET n) hWord)

/-- Regard the same original enveloping homomorphism as an algebra map
over its own source ring. This earns the restricted target action. -/
def polynomialEnvelopingSourceAlgebraMap :
    letI : Algebra ES ET := (φ).toRingHom.toAlgebra
    ES →ₐ[ES] ET := by
  letI : Algebra ES ET := (φ).toRingHom.toAlgebra
  exact
    { (φ).toRingHom with
      commutes' := fun _ => rfl }

/-- Native restriction along the identity is canonically the original
complex functor, with the native identity-action dictionary retained. -/
def polynomialDiagonalSourceRestrictionIso (ρ : Type v) :
    ((ModuleCat.restrictScalars (RingHom.id (MvPolynomial.PolynomialEnveloping k ρ))).mapHomologicalComplex
      (.down ℕ)).obj (KoszulComplex.polynomialDiagonalComplex k ρ) ≅
        KoszulComplex.polynomialDiagonalComplex k ρ :=
  (NatIso.mapHomologicalComplex
    (ModuleCat.restrictScalarsId (MvPolynomial.PolynomialEnveloping k ρ)) (.down ℕ) ≪≫
      Functor.mapHomologicalComplexIdIso
        (ModuleCat (MvPolynomial.PolynomialEnveloping k ρ)) (.down ℕ)).app _

/-- The polynomial Koszul map as a morphism over the original
source enveloping ring, into the native scalar-restricted target resolution. -/
def polynomialDiagonalRestrictedMap :
    KoszulComplex.polynomialDiagonalComplex k σ ⟶
      ((ModuleCat.restrictScalars (φ).toRingHom).mapHomologicalComplex (.down ℕ)).obj
        (KoszulComplex.polynomialDiagonalComplex k τ) := by
  letI : Algebra ES ET := (φ).toRingHom.toAlgebra
  exact (polynomialDiagonalSourceRestrictionIso k σ).inv ≫
    KoszulComplex.semilinearMap (R := ES) (S := ET) (M := VS) (N := VT)
      ES (polynomialEnvelopingSourceAlgebraMap k g) xS xT (J)
      (MvPolynomial.polynomialDiagonalGeneratorMap_functional k τ g)

/-- The source-restricted map has the same semilinear exterior value. -/
theorem polynomialDiagonalRestrictedMap_f_apply (n : ℕ) (z : ⋀[ES]^n VS) :
    ((polynomialDiagonalRestrictedMap k g).f n).hom z =
      exteriorPower.mapSemilinear (φ).toRingHom J n z := by
  let L : (⋀[ES]^n VS) →ₛₗ[(φ).toRingHom] (⋀[ET]^n VT) :=
    exteriorPower.mapSemilinear (R := ES) (S := ET) (M := VS) (N := VT) (φ).toRingHom (J) n
  have hValue : ((polynomialDiagonalRestrictedMap k g).f n).hom z =
      L (((polynomialDiagonalSourceRestrictionIso k σ).inv.f n).hom z) := rfl
  have hid : ((polynomialDiagonalSourceRestrictionIso k σ).inv.f n).hom z = z := by
    change (ModuleCat.restrictScalarsId'App (RingHom.id ES) rfl
      (ModuleCat.of ES (⋀[ES]^n VS))).inv.hom z = z
    exact ModuleCat.restrictScalarsId'App_inv_apply (RingHom.id ES) rfl
      (ModuleCat.of ES (⋀[ES]^n VS)) z
  exact hValue.trans (congrArg (fun t : ⋀[ES]^n VS => L t) hid)

/-- The zero-degree exterior map preserves the scalar represented
by the original empty wedge. -/
theorem polynomialDiagonalRestrictedMap_zero_scalar (z : ⋀[ES]^0 VS) :
    exteriorPower.zeroEquiv ET VT (((polynomialDiagonalRestrictedMap k g).f 0).hom z) =
      φ (exteriorPower.zeroEquiv ES VS z) := by
  let r := exteriorPower.zeroEquiv ES VS z
  let a : Fin 0 → VS := fun j => Fin.elim0 j
  have hz : z = r • exteriorPower.ιMulti ES 0 a := by
    apply (exteriorPower.zeroEquiv ES VS).injective
    rw [map_smul, exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]
  have hValue : exteriorPower.mapSemilinear (R := ES) (S := ET) (M := VS) (N := VT)
      (φ).toRingHom (J) 0 z =
      φ r • exteriorPower.ιMulti ET 0 (fun j => J (a j)) := by
    have h := congrArg (exteriorPower.mapSemilinear (R := ES) (S := ET) (M := VS) (N := VT)
      (φ).toRingHom (J) 0) hz
    rw [map_smulₛₗ, exteriorPower.mapSemilinear_ιMulti] at h
    exact h
  rw [polynomialDiagonalRestrictedMap_f_apply]
  exact (congrArg (exteriorPower.zeroEquiv ET VT) hValue).trans (by
    rw [map_smul, exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one])

end ModuleCat.Algebra.Hochschild.PolynomialDiagonal
