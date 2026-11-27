/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicCofiberComparisons
public import MathlibExt.AlgebraicGeometry.MotivicTorusClassModels
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Data.ZMod.Basic

/-!
# The two original coefficient Bocksteins

The integral sequence is Z --ell--> Z --> Z/ell. The mod-ell sequence
is Z/ell --times ell--> Z/ell^2 --> Z/ell. Its injection is an additive
integer-linear map, defined by the native universal lift from Z/ell;
it is not a unital ring map. All coefficients use the same lifted
integer-module universe as the existing motivic Tate complexes.

The coefficient boundary is the actual native mapping-cone triangle of
the original first coefficient map. Its comparison to the original last
coefficient complex is computed from the second map and zero homotopy.
Only quasi-isomorphism of that comparison is a construction output.

Source: Voevodsky, arXiv:math/0107109v1, Sections 6, 8 and 9; the two
sequences separately normalize the integral lift of c and the mod-ell beta.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicBocksteinModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open CochainComplex.HomComplex
open FiniteTransferCycleModels FiniteTransferProductModels NisnevichTransferModels
open MotivicStandardSchemes EffectiveMotivicComplexModels
open PointedMotivicModels ReducedMotivicCohomologyModels MotivicTorusClassModels
open scoped ZeroObject

/-- Native mod-ell coefficients in the existing integer-module universe. -/
abbrev ModCoefficients (ell : ℕ) : ModuleCat.{1} ℤ :=
  ModuleCat.of ℤ (ULift.{1} (ZMod ell))

/-- Lift the original integer-linear map without changing its coefficients. -/
def liftCoefficientMap {V W : Type} [AddCommGroup V]
    [AddCommGroup W] (f : V →+ W) :
    ModuleCat.of ℤ (ULift.{1} V) ⟶ ModuleCat.of ℤ (ULift.{1} W) :=
  ModuleCat.ofHom ({
    toFun := fun v => ULift.up (f v.down)
    map_zero' := congrArg ULift.up f.map_zero
    map_add' := fun v w => congrArg ULift.up (f.map_add v.down w.down)
  } : ULift.{1} V →+ ULift.{1} W).toIntLinearMap

/-- The first integral arrow is literal multiplication by ell. -/
def integralMultiplication (ell : ℕ) : integerCoefficients ⟶ integerCoefficients :=
  liftCoefficientMap ((ell : ℤ) • AddMonoidHom.id ℤ)

/-- The original quotient coefficient map. -/
def integralReduction (ell : ℕ) : integerCoefficients ⟶ ModCoefficients ell :=
  liftCoefficientMap (Int.castAddHom (ZMod ell))

/-- The map `ZMod ell → ZMod (ell^2)`, `n ↦ ell * n`: injective for `0 < ell`, zero for
`ell = 0`. -/
def modInjectionAdd (ell : ℕ) : ZMod ell →+ ZMod (ell * ell) :=
  ZMod.lift ell ⟨(ell : ℤ) • Int.castAddHom (ZMod (ell * ell)), by
    change (ell : ℤ) • ((ell : ℤ) : ZMod (ell * ell)) = 0
    simp only [zsmul_eq_mul, Int.cast_natCast]
    rw [← Nat.cast_mul, ZMod.natCast_self]⟩

/-- The same map `n ↦ ell * n` on the lifted coefficient modules. -/
def modInjection (ell : ℕ) : ModCoefficients ell ⟶ ModCoefficients (ell * ell) :=
  liftCoefficientMap (modInjectionAdd ell)

/-- Reduction from modulo ell^2 to modulo ell is the native quotient ring map. -/
def modReduction (ell : ℕ) : ModCoefficients (ell * ell) ⟶ ModCoefficients ell :=
  liftCoefficientMap (ZMod.castHom (dvd_mul_right ell ell) (ZMod ell)).toAddMonoidHom

/-- The original integral coefficient sequence, with its literal zero composite. -/
def integralSequence (ell : ℕ) : ShortComplex (ModuleCat.{1} ℤ) :=
  ShortComplex.mk (integralMultiplication ell) (integralReduction ell) (by
    ext z
    change (((ell : ℤ) * z.down : ℤ) : ZMod ell) = 0
    simp)

/-- The original mod-ell sequence, with its literal zero composite. -/
def modSequence (ell : ℕ) : ShortComplex (ModuleCat.{1} ℤ) :=
  ShortComplex.mk (modInjection ell) (modReduction ell) (by
    ext z
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective z.down
    change (ZMod.castHom (dvd_mul_right ell ell) (ZMod ell)) (modInjectionAdd ell z.down) = 0
    rw [← ha, modInjectionAdd, ZMod.lift_coe]
    simp)

variable {k : Type} [Field k]
  [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
  {D : CompositionSystem k} {G : GraphSystem k}
  [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
  {P : SmoothProductSystem k} {E : ExternalSystem P}
  {C : CorrespondenceProductModel D G P E} {A : StandardSchemes P}
  {R : RepresentableSystem D G} {S : TransferSheafificationModel D G}
  {T : CycleComplexSystem (D := D) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R)} {N : NisTensorSystem k}
  (B : CoefficientComplexSystem (D := D) (G := G) (P := P) (E := E)
    (C := C) (A := A) (R := R) (S := S) T N)

/-- The original first coefficient map on the actual Tate complex. -/
def firstMap (s : ShortComplex (ModuleCat.{1} ℤ)) (q : ℤ) :=
  (B.weightFunctor q).map s.f

/-- The original second coefficient map on that same Tate complex. -/
def secondMap (s : ShortComplex (ModuleCat.{1} ℤ)) (q : ℤ) :=
  (B.weightFunctor q).map s.g

/-- The cone comparison uses the actual second map and the zero homotopy. -/
def coefficientConeComparison (s : ShortComplex (ModuleCat.{1} ℤ)) (q : ℤ)
    (h : firstMap B s q ≫ secondMap B s q = 0) :
    CochainComplex.mappingCone (firstMap B s q) ⟶ (B.weightFunctor q).obj s.X₃ :=
  CochainComplex.mappingCone.desc (firstMap B s q) 0 (secondMap B s q) (by
    simp only [δ_zero, h, Cochain.ofHom_zero])

/-- Source exactness is a proof about this computed comparison, not a chosen boundary. -/
structure CoefficientConeSource (s : ShortComplex (ModuleCat.{1} ℤ)) (q : ℤ) where
  zero : firstMap B s q ≫ secondMap B s q = 0
  quasi : QuasiIso (coefficientConeComparison B s q zero)

attribute [local instance] HasDerivedCategory.standard

/-- The derived boundary is the original native coefficient-cone triangle. -/
def coefficientBoundary {s : ShortComplex (ModuleCat.{1} ℤ)} {q : ℤ}
    (M : CoefficientConeSource B s q) :
    DerivedCategory.Q.obj ((B.weightFunctor q).obj s.X₃) ⟶
      (DerivedCategory.Q.obj ((B.weightFunctor q).obj s.X₁))⟦(1 : ℤ)⟧ := by
  haveI : QuasiIso (coefficientConeComparison B s q M.zero) := M.quasi
  exact (asIso (DerivedCategory.Q.map (coefficientConeComparison B s q M.zero))).inv ≫
    DerivedCategory.Q.map (CochainComplex.mappingCone.triangle (firstMap B s q)).mor₃ ≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app ((B.weightFunctor q).obj s.X₁)

/-- Postcomposition with that boundary gives the actual coefficient connecting map. -/
def coefficientConnecting (F : ReducedFreeNisSystem k) (X : PointedSpaces (k := k))
    {s : ShortComplex (ModuleCat.{1} ℤ)} (p q : ℤ)
    (M : CoefficientConeSource B s q) (u : ReducedCohomology B F X p q s.X₃) :
    ReducedCohomology B F X (p + 1) q s.X₁ :=
  u ≫ (coefficientBoundary B M)⟦p⟧' ≫
    ((shiftFunctorAdd' _ (1 : ℤ) p (p + 1) (by omega)).app
      (DerivedCategory.Q.obj ((B.weightFunctor q).obj s.X₁))).inv

/-- Integral delta is fixed by Z --ell--> Z --> Z/ell. -/
def integralBockstein (ell : ℕ) (F : ReducedFreeNisSystem k)
    (X : PointedSpaces (k := k)) (p q : ℤ)
    (M : CoefficientConeSource B (integralSequence ell) q)
    (u : ReducedCohomology B F X p q (ModCoefficients ell)) :
    ReducedCohomology B F X (p + 1) q integerCoefficients :=
  coefficientConnecting B F X p q M u

/-- Mod-ell beta is fixed independently by Z/ell --timesell--> Z/ell^2 --> Z/ell. -/
def bockstein (ell : ℕ) (F : ReducedFreeNisSystem k)
    (X : PointedSpaces (k := k)) (p q : ℤ)
    (M : CoefficientConeSource B (modSequence ell) q)
    (u : ReducedCohomology B F X p q (ModCoefficients ell)) :
    ReducedCohomology B F X (p + 1) q (ModCoefficients ell) :=
  coefficientConnecting B F X p q M u

end MathlibExt.AlgebraicGeometry.MotivicBocksteinModels
