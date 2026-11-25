/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PrismaticPeriodFrames
public import MathlibExt.AlgebraicGeometry.PrismaticDividedFrobenius
public import Mathlib.LinearAlgebra.Dual.BaseChange

/-!
# Actual period-frame coordinates for completed syntomic operators

Coordinate frames use the computed conormal vector, the real inverse
phi_A coefficient map and the actual finite line comparisons. Tensor
and dual frames are native linear equivalences. Their coefficient
coordinate is the actual ideal generator in the initial delta algebra.

A realization of these coordinates is constrained by every finite
quotient projection and the actual filtration inclusion. Thus the later
divided-Frobenius map cannot be an unrelated named endomorphism.

References: BMS18 arXiv:1602.03148v3, Example 4.24;
BMS arXiv:1802.03261v2, Section 7.4 and Theorem 10.1.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PrismaticSyntomicCoordinates

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AbsolutePrismaticBasis PrismaticFilteredTwists PrismaticPeriodFrames
open MathlibExt.RingTheory MathlibExt.RingTheory.BoundedPrisms
open PrismaticBreuilKisinSeeds PrismaticDividedFrobenius
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

/-- The actual scalar-extension tensor-unit comparison. -/
def scalarUnitIso {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    (ModuleCat.extendScalars f).obj (ModuleCat.of R R) ≅ ModuleCat.of S S := by
  letI : Algebra R S := f.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso

/-- Native evaluation at one identifies the dual of the scalar line. -/
def dualScalarEquiv (R : Type) [CommRing R] : Module.Dual R R ≃ₗ[R] R where
  toFun f := f 1
  invFun a := LinearMap.toSpanSingleton R R a
  left_inv f := by
    apply LinearMap.ext
    intro r
    simpa using (f.map_smul r (1 : R)).symm
  right_inv a := by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {C : Type 1} [Category.{0} C] (O : Cᵒᵖ ⥤ CommRingCat.{0})

/-- Tensor powers of the actual module frame, with their real scalar-unit convention. -/
def wordFrame (M : PresheafOfModulesOfCommRing.{0} O) (B : Cᵒᵖ)
    (e : M.obj B ≃ₗ[O.obj B] O.obj B) :
    (n : ℕ) → (word O M n).obj B ≃ₗ[O.obj B] O.obj B
  | 0 => LinearEquiv.refl _ _
  | n + 1 => (TensorProduct.congr e (wordFrame M B e n)).trans
      (TensorProduct.lid (O.obj B) (O.obj B))

variable (p : ℕ) [Fact p.Prime] (A : QuasiSyntomicPrismSites.Ring p)
  (D : ∀ B : Basis p A, InitialLift p (ring p B))
  (Z : ZeroReduction p A D) (T : TwistTower p A D Z)

/-- Actual root-period coordinates at a basis object. All scalars and generators are fixed. -/
structure Context (B : ((Basis p A)ᵒᵖ)ᵒᵖ) where
  base : Prism.{0} p
  perfect : Function.Bijective (DeltaRing.frobenius p base.ring)
  initial : IsInitial ({ prism := base, residue := RingHom.id base.Residue } : Lift p base.Residue)
  residueMap : base.Residue →+* ring p B.unop.unop
  seed : ClassicalSeed p base
  frame : Frame p base perfect seed
  ideal :
    (D B.unop.unop).lift.prism.ideal =
      Ideal.span {(perfectoidBaseMap p A D B base initial residueMap).hom frame.generator.value}
  regular : Function.Injective
    (fun x : (D B.unop.unop).lift.prism.ring ↦
      (perfectoidBaseMap p A D B base initial residueMap).hom frame.generator.value * x)

namespace Context

variable {p A D Z} (T : TwistTower p A D Z)
  {B : ((Basis p A)ᵒᵖ)ᵒᵖ} (F : Context p A D B)

/-- The actual initial-ring divisor, not an independent syntomic parameter. -/
abbrev divisor : (D B.unop.unop).lift.prism.ring :=
  (perfectoidBaseMap p A D B F.base F.initial F.residueMap).hom F.frame.generator.value

/-- The finite positive line frame follows the specified inverse-Frobenius scalar extension. -/
def lineFrame (n : ℕ) :
    (T.data.line n).obj B ≅ ModuleCat.of ((quotientPresheaf p A D n).obj B)
      ((quotientPresheaf p A D n).obj B) :=
  (T.classical B F.base F.perfect F.initial F.residueMap F.seed).comparison n ≪≫
    (ModuleCat.extendScalars
      (adjustedScalars p A D B F.base F.perfect F.initial F.residueMap n)).mapIso
        F.frame.iso.symm ≪≫
      scalarUnitIso (adjustedScalars p A D B F.base F.perfect F.initial F.residueMap n)

/-- The negative frame is actual dual transport followed by evaluation at one. -/
def dualFrame (n : ℕ) :
    (T.data.dual n).obj B ≃ₗ[(quotientPresheaf p A D n).obj B]
      (quotientPresheaf p A D n).obj B :=
  (T.data.dualPoint n B).toLinearEquiv.trans
    ((Module.Dual.congr (F.lineFrame T n).toLinearEquiv).trans
      (dualScalarEquiv ((quotientPresheaf p A D n).obj B)))

/-- Every signed finite point frame is computed from tensor or dual powers. -/
def pointFrame (n : ℕ) (i : ℤ) :
    (T.finite n i).obj B ≃ₗ[(quotientPresheaf p A D n).obj B]
      (quotientPresheaf p A D n).obj B :=
  match i with
  | Int.ofNat k => wordFrame (quotientPresheaf p A D n) (T.data.line n) B
      (F.lineFrame T n).toLinearEquiv k
  | Int.negSucc k => wordFrame (quotientPresheaf p A D n) (T.data.dual n) B
      (F.dualFrame T n) (k + 1)

end Context

/-- Evaluation is the actual sheaf-to-presheaf evaluation functor. -/
def evaluate (B : ((Basis p A)ᵒᵖ)ᵒᵖ) :
    PrismaticNygaardCohomology.Sheaves p A ⥤ ModuleCat.{1} ℤ :=
  sheafToPresheaf (topology p A) _ ⋙
    (evaluation (((Basis p A)ᵒᵖ)ᵒᵖ) (ModuleCat.{1} ℤ)).obj B

instance evaluate_additive (B : ((Basis p A)ᵒᵖ)ᵒᵖ) : (evaluate p A B).Additive where
  map_add := by intros; rfl

/-- The actual coefficient complex at a basis point. -/
def pointComplex (B : ((Basis p A)ᵒᵖ)ᵒᵖ)
    (K : CochainComplex (PrismaticNygaardCohomology.Sheaves p A) ℤ) :
    CochainComplex (ModuleCat.{1} ℤ) ℤ :=
  ((evaluate p A B).mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- Actual source-coordinate maps, fixed by every finite projection and the real inclusion. The
coordinates are the uncompleted initial prism ring and its Nygaard step, whereas the evaluated
complexes are Nygaard-completed; the maps are therefore not quasi-isomorphisms in general (the
initial prism of `𝔽_p[x^{1/p^∞}]/(x)` is not Nygaard-complete). -/
structure Realization (B : ((Basis p A)ᵒᵖ)ᵒᵖ) (F : Context p A D B) (i : ℤ) where
  source : sourceComplex p (D B.unop.unop).lift.prism.ring F.divisor i.toNat ⟶
    pointComplex p A B (T.nygaard i)
  target : targetComplex (D B.unop.unop).lift.prism.ring ⟶
    pointComplex p A B (T.complex i)
  inclusion :
    source ≫ ((evaluate p A B).mapHomologicalComplex (ComplexShape.up ℤ)).map (T.can i) =
      canSigned p (D B.unop.unop).lift.prism.ring F.divisor i ≫ target
  projection : ∀ (n : ℕ) (x : (D B.unop.unop).lift.prism.ring),
    F.pointFrame T n i
      (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        ((evaluate p A B).obj (T.finiteSheaf n i))).hom
          ((((evaluate p A B).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (T.projection i n)).f 0
              (target.f 0 (targetGenerator (D B.unop.unop).lift.prism.ring x)))).down) =
        Ideal.Quotient.mk _ x

end MathlibExt.AlgebraicGeometry.PrismaticSyntomicCoordinates
