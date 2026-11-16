/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicTorusClassModels
public import MathlibExt.AlgebraicGeometry.PointedMotivicQuotientMaps
public import MathlibExt.AlgebraicGeometry.MotivicCofiberComparisons
public import MathlibExt.AlgebraicGeometry.MotivicBundleModels

/-!
# The source-normalized rank-one Tate/Thom orientation

G_m -> A^1 is fixed by the polynomial coordinate sent to the Laurent
monomial. The point one is fixed by the unit insertion. The relative
cofiber G_m/1 -> A^1/1 is compared to the literal A^1/(A^1 minus zero)
by its actual quotient map. Its reduced-chain boundary sends the graph
torus class to the rank-one Thom class, with the native triangle fixing
the sign. No arbitrary cohomology isomorphism is part of this recipe.

Sources: Mazza--Voevodsky--Weibel, Definitions 2.12/3.1 and Lecture 14;
Voevodsky arXiv:math/0107109v1, Sections 2/4 and Lemma 4.2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicTateThomModels

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open FiniteTransferCycleModels FiniteTransferProductModels
open NisnevichTransferModels MotivicStandardSchemes
open EffectiveMotivicComplexModels PointedMotivicModels
open ReducedMotivicCohomologyModels MotivicRealizationComparisons
open MotivicCycleProducts MotivicTensorOperations MotivicCohomologyProducts
open PointedMotivicQuotients PointedMotivicQuotientMaps
open MotivicTorusClassModels MotivicCofiberComparisons MotivicBundleModels
open scoped Simplicial

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  {P : SmoothProductSystem k} {A : StandardSchemes P}

/-- The actual invertible Laurent coordinate of G_m. -/
def torusCoordinate : torusRing k 1 :=
  AddMonoidAlgebra.single (fun _ : Fin 1 => (1 : ℤ)) (1 : k)

/-- The polynomial coordinate map of the standard open immersion. -/
def torusAffineRing : affineRing k 1 →ₐ[k] torusRing k 1 :=
  MvPolynomial.aeval (fun _ : Fin 1 => torusCoordinate (k := k))

/-- The standard torus/open-affine comparison, fixed as a whole Spec map. -/
structure TorusOpenAffine where
  map : A.torus 1 ⟶ A.affine 1
  openIso : A.torus 1 ≅ A.complement 1
  open_eq : map = openIso.hom ≫ A.complementInclusion 1
  coordinate_eq : (A.torusIso 1).inv ≫ map.left ≫ (A.affineIso 1).hom =
    Spec.map (CommRingCat.ofHom (torusAffineRing (k := k)).toRingHom)

/-- A^1 pointed at one, through the same actual standard coordinate map. -/
def pointedAffineOne (G : TorusOpenAffine (P := P) (A := A)) : PointedSpaces (k := k) :=
  cofiber (representedMap (torusPoint (P := P) (A := A) ≫ G.map))

/-- The native relative pointed open map G_m/1 -> A^1/1. -/
def relativeTorusMap (G : TorusOpenAffine (P := P) (A := A)) :
    pointedTorus (P := P) (A := A) ⟶ pointedAffineOne G :=
  cofiberMap (representedMap (torusPoint (P := P) (A := A)))
    (representedMap (torusPoint (P := P) (A := A) ≫ G.map)) (𝟙 _)
    (representedMap G.map) (by
      rw [Category.id_comp, representedMap_comp])

/-- Its cofiber is identified by the actual A^1 quotient map.
Objectwise monicity is a geometric source condition for the native
reduced-chain cone comparison; it is not a motivic-equivalence conclusion. -/
structure RelativeA1CofiberSource (G : TorusOpenAffine (P := P) (A := A)) where
  iso : cofiber (relativeTorusMap G) ≅ affineThomSphere A 1
  quotient_eq : cofiberQuotient
      (representedMap (torusPoint (P := P) (A := A) ≫ G.map)) ≫
    cofiberQuotient (relativeTorusMap G) ≫ iso.hom =
      cofiberQuotient (representedMap (A.complementInclusion 1))
  mono : ∀ U, Mono ((relativeTorusMap G).right.app U)

variable {D : CompositionSystem k} {G₀ : GraphSystem k}
  [CorrespondenceLaws D G₀] [CorrespondenceAdditivity D G₀]
  {E : ExternalSystem P} {C : CorrespondenceProductModel D G₀ P E}
  {R : RepresentableSystem D G₀} {S : TransferSheafificationModel D G₀}
  (T : CycleComplexSystem (D := D) (G := G₀) (P := P) (E := E)
    (C := C) (A := A) (R := R)) (F : ReducedFreeNisSystem k)
  (N : NisTensorSystem k) [N.functor.Additive] [∀ H, (N.functor.obj H).Additive]
  (B : CoefficientComplexSystem (D := D) (G := G₀) (P := P) (E := E)
    (C := C) (A := A) (R := R) (S := S) T N)

/-- The actual rank-one Thom orientation is the native cofiber boundary
applied to the actual torus graph class, transported by the quotient comparison. -/
def rankOneThomClass (G : TorusOpenAffine (P := P) (A := A))
    (V : RelativeA1CofiberSource G) (Q : CofiberChainSource F (relativeTorusMap G))
    (L : TorusCycleLinearization (S := S) T F)
    (U : IntegerCoefficientInclusions (T := T) (N := N) (B := B)) :
    ReducedCohomology B F (affineThomSphere A 1) 2 1 integerCoefficients :=
  ReducedMotivicCohomologyModels.pullback B F V.iso.inv 2 1 integerCoefficients
    (connecting F B Q 1 1 integerCoefficients
      (torusClass (T := T) (F := F) (N := N) (B := B) L U))

end MathlibExt.AlgebraicGeometry.MotivicTateThomModels
