/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicCohomologyProducts

/-!
# The actual affine finite-cycle quotient K_n,A

K_n,A is the zero-pointed constant simplicial sheaf formed from the
literal cokernel Z_tr(A^n)/Z_tr(A^n minus zero), the native ordinary
Nisnevich sheafification, and the specified pure-tensor coefficient
sheaf. Cycle sections and coefficient maps use the same quotient unit.
External multiplication is fixed on every pair of actual finite cycles
by product, source diagonal and the normalized affine coordinate map.

This definition is independent of the reduced-torus Tate complex. Their
comparison and its motivic weak-equivalence/multiplicativity conclusions
are genuine separate construction requests.

Source: Voevodsky arXiv:math/0107109v1, Section 2, pp. 3--4, equation 2.2
and Theorem 2.1. Finite cycle multiplicities retain the native source
normalizations of the imported correspondence/product models.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicAffineQuotientModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open FiniteTransferCycleModels FiniteTransferProductModels
open NisnevichTransferModels MotivicStandardSchemes
open EffectiveMotivicComplexModels PointedMotivicModels
open MotivicCycleProducts PointedMotivicQuotients
open scoped Simplicial

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]

/-- A constant simplicial module sheaf with the actual zero basepoint. -/
def pointedConstantModule (Q : PointedSimplicialModuleFunctor k)
    (F : NisModules (k := k)) : PointedSpaces (k := k) :=
  Q.functor.obj ((Functor.const SimplexCategoryᵒᵖ).obj F)

/-- The sheaf Yoneda section is fixed on every actual scheme map and
every simplex; the basepoint equation follows from pointedness and Q's zero. -/
structure ModuleSectionSystem (Q : PointedSimplicialModuleFunctor k) where
  sectionMap : ∀ (F : NisModules (k := k)) (U : SmoothScheme k)
    (_x : F.obj.obj (op U)), representedPointed U ⟶ pointedConstantModule Q F
  value : ∀ (F : NisModules (k := k)) (U : SmoothScheme k)
    (x : F.obj.obj (op U)) (W : SmoothScheme k) (g : W ⟶ U)
    (n : SimplexCategoryᵒᵖ),
    ((((Q.underlyingIso.app ((Functor.const SimplexCategoryᵒᵖ).obj F)).hom.app
      (op W)).app n)
      (((sectionMap F U x).right.app (op W)).app n (some (ULift.up g)))) =
      F.obj.map g.op x

variable {D : CompositionSystem k} {G : GraphSystem k}
  [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
  {P : SmoothProductSystem k} {A : StandardSchemes P}
  {R : RepresentableSystem D G}

/-- The native ordinary sheafification of the literal finite-cycle cokernel. -/
def affineQuotientSheaf (q : ℕ) : NisModules (k := k) :=
  (presheafToSheaf (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)).obj
    (graphRestriction D G
      (affineQuotientPresheaf (D := D) (G := G) (P := P) (A := A) (R := R) q))

/-- A literal finite cycle passes through the native cokernel projection
and the native ordinary Nisnevich sheafification unit. -/
def affineCycleClass (q : ℕ) (U : SmoothScheme k) (z : Cycles U (A.affine q)) :
    (affineQuotientSheaf (D := D) (G := G) (P := P) (A := A) (R := R) q).obj.obj (op U) :=
  (((sheafificationAdjunction (nisnevichTopology (k := k))
    (ModuleCat.{1} ℤ)).unit.app
      (graphRestriction D G
        (affineQuotientPresheaf (D := D) (G := G) (P := P) (A := A) (R := R) q))).app
      (op U))
    ((cokernel.π (R.functor.map (show (⟨A.complement q⟩ : CorrespondenceObject D G) ⟶
      ⟨A.affine q⟩ from graphCycle G (A.complementInclusion q))).hom).app (op ⟨U⟩)
      (((eqToHom (R.object_eq ⟨A.affine q⟩)).hom.app (op ⟨U⟩))
        (((R.model ⟨A.affine q⟩).valueIso ⟨U⟩).inv (ULift.up z))))

variable (N : NisTensorSystem k) (Q : PointedSimplicialModuleFunctor k)

/-- Coefficients tensor this same actual affine quotient sheaf. -/
def affineCoefficient (q : ℕ) (V : ModuleCat.{1} ℤ) : NisModules (k := k) :=
  (N.functor.obj (affineQuotientSheaf (D := D) (G := G) (P := P) (A := A) (R := R) q)).obj
    (constantCoefficient V)

/-- The literal source K_n,A, rather than a Tate-complex synonym. -/
def affineK (q : ℕ) (V : ModuleCat.{1} ℤ) : PointedSpaces (k := k) :=
  pointedConstantModule Q (affineCoefficient (D := D) (G := G) (P := P)
    (A := A) (R := R) N q V)

/-- All coefficient maps pass through native constant sheaf and quotient tensor. -/
def affineKFunctor (q : ℕ) : ModuleCat.{1} ℤ ⥤ PointedSpaces (k := k) :=
  constantSheaf (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ) ⋙
    N.functor.obj (affineQuotientSheaf (D := D) (G := G) (P := P) (A := A) (R := R) q) ⋙
    Functor.const SimplexCategoryᵒᵖ ⋙ Q.functor

/-- The affine coefficient functor has exactly the stated actual objects. -/
theorem affineKFunctor_obj (q : ℕ) (V : ModuleCat.{1} ℤ) :
    (affineKFunctor (D := D) (G := G) (P := P) (A := A) (R := R) N Q q).obj V =
      affineK (D := D) (G := G) (P := P) (A := A) (R := R) N Q q V := rfl

/-- The actual finite-cycle/coefficient element in that sheaf. -/
def affineCoefficientClass (q : ℕ) (V : ModuleCat.{1} ℤ)
    (U : SmoothScheme k) (z : Cycles U (A.affine q)) (v : V) :
    (affineCoefficient (D := D) (G := G) (P := P) (A := A) (R := R) N q V).obj.obj (op U) :=
  tensorElement N _ _ (op U)
    (affineCycleClass (D := D) (G := G) (P := P) (A := A) (R := R) q U z)
      (constantElement V (op U) v)

/-- The pointed section on every actual cycle and coefficient. -/
def affineCycleSection (M : ModuleSectionSystem Q) (q : ℕ) (V : ModuleCat.{1} ℤ)
    (U : SmoothScheme k) (z : Cycles U (A.affine q)) (v : V) :
    representedPointed U ⟶ affineK (D := D) (G := G) (P := P) (A := A) (R := R) N Q q V :=
  M.sectionMap _ U (affineCoefficientClass (D := D) (G := G) (P := P)
    (A := A) (R := R) N q V U z v)

/-- The actual affine external-cycle product followed by both fixed coordinate maps. -/
def diagonalAffineProduct (E : ExternalSystem P) (q r : ℕ) (U : SmoothScheme k)
    (z : Cycles U (A.affine q)) (w : Cycles U (A.affine r)) : Cycles U (A.affine (q + r)) :=
  composeCycles D (graphCycle G (smoothDiagonal P U))
    (composeCycles D (externalCycles E z w) (graphCycle G (A.affineProduct q r).hom))

/-- Affine quotient multiplication, fixed on all literal finite cycles
and coefficient tensors, not by an arbitrary cohomology pairing. -/
structure AffineCycleProduct (E : ExternalSystem P) (M : ModuleSectionSystem Q) where
  map : ∀ (q r : ℕ) (V W Z : ModuleCat.{1} ℤ)
    (_μ : TensorProduct ℤ V W →ₗ[ℤ] Z),
    smash (affineK (D := D) (G := G) (P := P) (A := A) (R := R) N Q q V)
      (affineK (D := D) (G := G) (P := P) (A := A) (R := R) N Q r W) ⟶
      affineK (D := D) (G := G) (P := P) (A := A) (R := R) N Q (q + r) Z
  cycle_product : ∀ (q r : ℕ) (V W Z : ModuleCat.{1} ℤ)
    (μ : TensorProduct ℤ V W →ₗ[ℤ] Z) (U : SmoothScheme k)
    (z : Cycles U (A.affine q)) (w : Cycles U (A.affine r)) (v : V) (t : W),
    smashDiagonal (representedPointed U) ≫
      smashMap (affineCycleSection N Q M q V U z v)
        (affineCycleSection N Q M r W U w t) ≫ map q r V W Z μ =
      affineCycleSection N Q M (q + r) Z U
        (diagonalAffineProduct (D := D) (G := G) E q r U z w)
        (μ (TensorProduct.tmul ℤ v t))

end MathlibExt.AlgebraicGeometry.MotivicAffineQuotientModels
