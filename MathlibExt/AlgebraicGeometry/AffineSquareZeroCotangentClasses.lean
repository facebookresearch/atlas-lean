/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeometricCotangentComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Actual square-zero extension classes of the computed affine cotangent

The extension is an actual surjective algebra map with square-zero
kernel. Its coefficient module is compared to that literal kernel, and
its A-action is fixed by multiplication by every lift in the extension.
The cochain class is normalized on every pure differential in degree -1
by the difference of the two actual lifted faces of P1 to P0.

Its derived arrow is the literal Q-image of that cochain map into the
single kernel module in degree -1, the native model of I[1]. It is not
an independently supplied arrow named an extension class.
Generic affine extension/cotangent classification and resolution independence
are completed Stacks Project/AxiomMath source integration, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b, Apache2.0, especially
Deformation/RingThickening/{CotangentLift,CotangentExtComparison,
CotangentObstructionCocycle,CotangentObstructionClasses}.lean (0GPU,08RB,08SP).
The comparison requests supply the native carrier bridge.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.AffineSquareZeroCotangentClasses

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicTopology _root_.Simplicial
open GeometricCotangentComplex
open scoped Simplicial
attribute [local instance] HasDerivedCategory.standard

variable (k A : Type) [CommRing k] [CommRing A] [Algebra k A]

structure Extension where
  ring : Type
  [commRing : CommRing ring]
  [algebra : Algebra k ring]
  projection : ring →ₐ[k] A
  surjective : Function.Surjective projection
  squareZero : (RingHom.ker projection.toRingHom) ^ 2 = ⊥
  coefficient : ModuleCat.{0} A
  kernel : RingHom.ker projection.toRingHom ≃+ coefficient
  action : ∀ (e : ring) (x : RingHom.ker projection.toRingHom),
    kernel ⟨e * x.val, by
      have hx := x.property
      change projection.toRingHom x.val = 0 at hx
      change projection.toRingHom (e * x.val) = 0
      rw [map_mul, hx, mul_zero]⟩ = projection e • kernel x

attribute [instance] Extension.commRing Extension.algebra

variable {k A} (R : PolynomialResolution k A) (E : Extension k A)

structure PolynomialLift where
  lift : R.algebra.obj (.op ⦋0⦌) →ₐ[k] E.ring
  reduction : ∀ x, E.projection (lift x) = R.augmentation.app (.op ⦋0⦌) x
  faces : ∀ x : R.algebra.obj (.op ⦋1⦌),
    E.projection (lift (R.algebra.δ (0 : Fin 2) x)) =
      E.projection (lift (R.algebra.δ (1 : Fin 2) x))

def faceDifference (L : PolynomialLift R E) (x : R.algebra.obj (.op ⦋1⦌)) : E.coefficient :=
  E.kernel ⟨L.lift (R.algebra.δ (0 : Fin 2) x) - L.lift (R.algebra.δ (1 : Fin 2) x), by
    change E.projection.toRingHom (_ - _) = 0
    rw [map_sub]
    change E.projection (L.lift (R.algebra.δ (0 : Fin 2) x)) -
      E.projection (L.lift (R.algebra.δ (1 : Fin 2) x)) = 0
    rw [L.faces, sub_self]⟩

def coefficientComplex : CochainComplex (ModuleCat.{0} A) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat.{0} A) (-1)).obj E.coefficient

structure NormalizedCochain (L : PolynomialLift R E) where
  map : affineComplex R ⟶ coefficientComplex E
  pure : ∀ x : R.algebra.obj (.op ⦋1⦌),
    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-1) E.coefficient).hom
      ((map.f (-1)) ((affineDegreeIso R 1).inv
        (CommAlgCat.resolutionCotangentTermDifferential k (CommAlgCat.of k A)
          R.algebra R.augmentation (.op ⦋1⦌) x))) = faceDifference R E L x

def extensionClass {L : PolynomialLift R E} (N : NormalizedCochain R E L) :
    affineDerived R ⟶ DerivedCategory.Q.obj (coefficientComplex E) := DerivedCategory.Q.map N.map

/-- The condition that the extension class of $E$ is independent of the choices: for any two
$k$-algebra maps from $P_0$ to the extension ring lifting the augmentation $P_0 \to A$ (where
$P_\bullet$ is the resolution), and any normalized cochain maps for them (sending $dx$, for
$x \in P_1$, to the difference of the lifts of the two faces of $x$), the two resulting morphisms
in the derived category of $A$-modules, from the cotangent complex
$\Omega_{P_\bullet/k} \otimes_{P_\bullet} A$ to the coefficient module placed in degree $-1$, are
equal. -/
def Independent : Prop := ∀ (L M : PolynomialLift R E)
    (N : NormalizedCochain R E L) (N' : NormalizedCochain R E M),
  extensionClass R E N = extensionClass R E N'

structure ExtensionMap (F : Extension k A) where
  map : E.ring →ₐ[k] F.ring
  projection : ∀ x, F.projection (map x) = E.projection x
  coefficient : E.coefficient ⟶ F.coefficient
  normalized : ∀ x : RingHom.ker E.projection.toRingHom,
    coefficient (E.kernel x) = F.kernel ⟨map x.val, by
      have hx := x.property
      change E.projection.toRingHom x.val = 0 at hx
      change F.projection (map x.val) = 0
      rw [projection]
      exact hx⟩

def coefficientMap {F : Extension k A} (u : ExtensionMap E F) :
    coefficientComplex E ⟶ coefficientComplex F :=
  (CochainComplex.singleFunctor (ModuleCat.{0} A) (-1)).map u.coefficient

def Natural {F : Extension k A} (u : ExtensionMap E F) : Prop :=
  ∀ (L : PolynomialLift R E) (M : PolynomialLift R F)
    (N : NormalizedCochain R E L) (N' : NormalizedCochain R F M),
      extensionClass R E N ≫ DerivedCategory.Q.map (coefficientMap E u) = extensionClass R F N'

end MathlibExt.AlgebraicGeometry.AffineSquareZeroCotangentClasses
