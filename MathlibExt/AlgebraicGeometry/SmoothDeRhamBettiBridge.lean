/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HyperkahlerComplexStructures
public import MathlibExt.AlgebraicGeometry.IntegralBetti
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# A normalized real smooth de Rham and integral Betti bridge

The smooth-form sheaves are native sheafifications of actual real tangent
forms on every open. Their differential is the actual chart exterior
derivative. A de Rham resolution is pinned in every degree to those sheaves
and differentials. Its constant inclusion and closed-form cocycles are
normalized to the literal constant/function-times-form sheaf maps. The
derived class formula is then fixed; an arbitrary H² isomorphism is not a
substitute for these normalization conditions.

The integer-to-real map is induced by native sectionwise scalar extension,
sheafification and derived localization. The coefficient-unit comparison
is the native sheafification of c↦c⊗1. It is defined before its isomorphism
proof is requested. The actual integral constant-sheaf H² is never replaced
by a freely selected lattice carrier.

Sources: de Rham/Poincaré comparison and Kashiwara–Schapira,
*Sheaves on Manifolds*, section 2.6; Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679, Apache 2.0,
DerivedCategory/ExactFunctor (Joël Riou), ModuleCat/ChangeOfRings
(Jujian Zhang). Imported real-form sources retain their original credits.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SmoothDeRhamBettiBridge

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite TopologicalSpace
open ManifoldDifferentialForms HyperkahlerComplexStructures
open scoped Manifold ContDiff TensorProduct ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

variable (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Ambient n) M]
  [IsManifold 𝓘(ℝ, Ambient n) ∞ M]

abbrev LocalForms (U : Opens M) (p : ℕ) := smoothForms ℝ (Ambient n) M U p

def restrictRough {U V : Opens M} (h : V ≤ U) {p : ℕ}
    (alpha : RoughForm ℝ (Ambient n) M U p) : RoughForm ℝ (Ambient n) M V p :=
  fun x ↦ alpha ⟨x.val, h x.property⟩

def restriction {U V : Opens M} (h : V ≤ U) (p : ℕ) :
    LocalForms n M U p →ₗ[ℝ] LocalForms n M V p where
  toFun alpha := ⟨restrictRough n M h alpha.val, by
    intro a
    have hd : chartDomain ℝ (Ambient n) M V a ⊆ chartDomain ℝ (Ambient n) M U a :=
      fun z hz ↦ ⟨hz.1, h hz.2⟩
    apply ((alpha.property a).mono hd).congr
    intro z hz
    simp only [chartForm, hz, hd hz, dite_true, restrictRough]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def formPresheaf (p : ℕ) : (Opens M)ᵒᵖ ⥤ ModuleCat.{0} ℝ where
  obj U := ModuleCat.of ℝ (LocalForms n M U.unop p)
  map f := ModuleCat.ofHom (restriction n M f.unop.le p)
  map_id U := by ext alpha x v; rfl
  map_comp f g := by ext alpha x v; rfl

def formSheaf (p : ℕ) : TopCat.Sheaf (ModuleCat.{0} ℝ) (TopCat.of M) :=
  (presheafToSheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℝ)).obj (formPresheaf n M p)

/-- The condition that the exterior derivative satisfies its laws on smooth real forms over every
open set: for a smooth manifold $M$ modelled on $\mathbb{C}^{2n}$ (as a real vector space), the
exterior derivative `exteriorDerivative` (computed in charts) of a smooth form is smooth, it is
$\mathbb{R}$-linear, $d(d\alpha) = 0$, and it commutes with restriction to smaller open sets. -/
class LocalExteriorTheory : Prop where
  smooth : ∀ (U : Opens M) p (alpha : LocalForms n M U p),
    IsSmooth ℝ (Ambient n) M (exteriorDerivative ℝ (Ambient n) M alpha.val)
  add : ∀ (U : Opens M) p (alpha beta : LocalForms n M U p),
    exteriorDerivative ℝ (Ambient n) M (alpha.val + beta.val) =
      exteriorDerivative ℝ (Ambient n) M alpha.val + exteriorDerivative ℝ (Ambient n) M beta.val
  smul : ∀ (U : Opens M) p (c : ℝ) (alpha : LocalForms n M U p),
    exteriorDerivative ℝ (Ambient n) M (c • alpha.val) =
      c • exteriorDerivative ℝ (Ambient n) M alpha.val
  square : ∀ (U : Opens M) p (alpha : LocalForms n M U p),
    exteriorDerivative ℝ (Ambient n) M (exteriorDerivative ℝ (Ambient n) M alpha.val) = 0
  natural : ∀ (U V : Opens M) (h : V ≤ U) p (alpha : LocalForms n M U p),
    restrictRough n M h (exteriorDerivative ℝ (Ambient n) M alpha.val) =
      exteriorDerivative ℝ (Ambient n) M (restrictRough n M h alpha.val)

variable [LocalExteriorTheory n M]

def localD (U : Opens M) (p : ℕ) : LocalForms n M U p →ₗ[ℝ] LocalForms n M U (p + 1) where
  toFun alpha := ⟨exteriorDerivative ℝ (Ambient n) M alpha.val,
    LocalExteriorTheory.smooth U p alpha⟩
  map_add' alpha beta := Subtype.ext (LocalExteriorTheory.add U p alpha beta)
  map_smul' c alpha := Subtype.ext (LocalExteriorTheory.smul U p c alpha)

def formDifferential (p : ℕ) : formPresheaf n M p ⟶ formPresheaf n M (p + 1) where
  app U := ModuleCat.ofHom (localD n M U.unop p)
  naturality {U V} f := by
    ext alpha
    exact Subtype.ext (LocalExteriorTheory.natural U.unop V.unop f.unop.le p alpha).symm

def sheafDifferential (p : ℕ) : formSheaf n M p ⟶ formSheaf n M (p + 1) :=
  (presheafToSheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℝ)).map (formDifferential n M p)

variable [ExteriorTheory ℝ (Ambient n) M]

def constantFormPresheafMap {p : ℕ} (alpha : RealForms n M p) :
    (Functor.const (Opens M)ᵒᵖ).obj (ModuleCat.of ℝ ℝ) ⟶ formPresheaf n M p where
  app U := ModuleCat.ofHom (LinearMap.toSpanSingleton ℝ (LocalForms n M U.unop p)
    (restriction n M (by simp) p alpha))
  naturality {U V} f := by
    ext
    rfl

abbrev RealSheaf := TopCat.Sheaf (ModuleCat.{0} ℝ) (TopCat.of M)
abbrev RealDerived := DerivedCategory (RealSheaf M)
abbrev realConstantSheaf : RealSheaf M :=
  (constantSheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℝ)).obj (ModuleCat.of ℝ ℝ)
abbrev realUnit : RealDerived M := (DerivedCategory.singleFunctor _ 0).obj (realConstantSheaf M)
abbrev RealBettiH2 := realUnit M ⟶ (realUnit M)⟦(2 : ℤ)⟧

instance realSheafLinear : Linear ℝ (RealSheaf M) := by
  change Linear ℝ (Sheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℝ))
  unfold Sheaf
  infer_instance

def constantFormSheafMap {p : ℕ} (alpha : RealForms n M p) :
    realConstantSheaf M ⟶ formSheaf n M p :=
  (presheafToSheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℝ)).map
    (constantFormPresheafMap n M alpha)

def constantZeroForm (c : ℝ) : RealForms n M 0 :=
  ⟨fun _ ↦ ContinuousAlternatingMap.constOfIsEmpty ℝ (Ambient n) (Fin 0) c, by
    intro a
    apply (contDiffOn_const : ContDiffOn ℝ ∞
      (fun _ : Ambient n ↦ ContinuousAlternatingMap.constOfIsEmpty ℝ (Ambient n) (Fin 0) c)
      (chartDomain ℝ (Ambient n) M ⊤ a)).congr
    intro z hz
    ext v
    simp only [chartForm, dite_eq_left hz]
    rfl⟩

abbrev ConstantComplex := (CochainComplex.singleFunctor (RealSheaf M) 0).obj (realConstantSheaf M)

structure DeRhamResolution where
  complex : CochainComplex (RealSheaf M) ℤ
  terms : ∀ p : ℕ, complex.X (p : ℤ) ≅ formSheaf n M p
  negatives : ∀ j : ℤ, j < 0 → IsZero (complex.X j)
  differential : ∀ p : ℕ, complex.d (p : ℤ) (p + 1 : ℕ) ≫ (terms (p + 1)).hom =
    (terms p).hom ≫ sheafDifferential n M p
  unit : ConstantComplex M ⟶ complex
  unit_value : unit.f 0 ≫ (terms 0).hom = constantFormSheafMap n M (constantZeroForm n M 1)
  [unit_quasiIso : QuasiIso unit]
  cocycle : closedForms ℝ (Ambient n) M 2 → (ConstantComplex M ⟶ complex⟦(2 : ℤ)⟧)
  cocycle_value : ∀ alpha, (cocycle alpha).f 0 ≫
      (complex.shiftFunctorObjXIso 2 0 2 (by omega)).hom ≫ (terms 2).hom =
    constantFormSheafMap n M alpha.val

attribute [instance] DeRhamResolution.unit_quasiIso

def derivedClosedClass (R : DeRhamResolution n M) (alpha : closedForms ℝ (Ambient n) M 2) :
    RealBettiH2 M :=
  DerivedCategory.Q.map (R.cocycle alpha) ≫
    (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app R.complex ≫
      (shiftFunctor (RealDerived M) (2 : ℤ)).map (inv (DerivedCategory.Q.map R.unit))

structure DeRhamClassProofs (R : DeRhamResolution n M) : Prop where
  add : ∀ alpha beta, derivedClosedClass n M R (alpha + beta) =
    derivedClosedClass n M R alpha + derivedClosedClass n M R beta
  smul : ∀ (c : ℝ) alpha,
    derivedClosedClass n M R (c • alpha) = c • derivedClosedClass n M R alpha
  exact : ∀ alpha : RealForms n M 1,
    derivedClosedClass n M R (dToClosed ℝ (Ambient n) M 1 alpha) = 0
  kernel : ∀ alpha, derivedClosedClass n M R alpha = 0 →
    alpha ∈ LinearMap.range (dToClosed ℝ (Ambient n) M 1)
  surjective : Function.Surjective (derivedClosedClass n M R)

def closedClassLinear (R : DeRhamResolution n M) (P : DeRhamClassProofs n M R) :
    closedForms ℝ (Ambient n) M 2 →ₗ[ℝ] RealBettiH2 M where
  toFun := derivedClosedClass n M R
  map_add' := P.add
  map_smul' := P.smul

def deRhamClass (R : DeRhamResolution n M) (P : DeRhamClassProofs n M R) :
    RealH2 n M →ₗ[ℝ] RealBettiH2 M :=
  (LinearMap.range (dToClosed ℝ (Ambient n) M 1)).liftQ (closedClassLinear n M R P) (by
    rintro _ ⟨alpha, rfl⟩
    exact P.exact alpha)

/-- The equivalence is fixed by the actual closed-form cocycle formula.
Finiteness is a source cohomology conclusion, not a BBF hypothesis. -/
structure RealDeRhamComparison (R : DeRhamResolution n M) where
  equiv : RealH2 n M ≃ₗ[ℝ] RealBettiH2 M
  normalization : ∀ alpha : closedForms ℝ (Ambient n) M 2,
    equiv (classOfClosedTwoForm ℝ (Ambient n) M alpha) = derivedClosedClass n M R alpha
  finite : FiniteDimensional ℝ (RealH2 n M)

abbrev integerPresheaf := (Functor.const (Opens M)ᵒᵖ).obj (ModuleCat.of ℤ ℤ)

def integerOne (U : (Opens M)ᵒᵖ) :
    (IntegralBetti.integerConstantSheaf (TopCat.of M)).obj.obj U :=
  ((toSheafify (Opens.grothendieckTopology M) (integerPresheaf M)).app U).hom (1 : ℤ)

theorem integerOne_natural {U V : (Opens M)ᵒᵖ} (f : U ⟶ V) :
    ((IntegralBetti.integerConstantSheaf (TopCat.of M)).obj.map f).hom (integerOne M U) =
      integerOne M V := by
  have h := (toSheafify (Opens.grothendieckTopology M) (integerPresheaf M)).naturality f
  change (((sheafify (Opens.grothendieckTopology M) (integerPresheaf M)).map f).hom)
    (((toSheafify (Opens.grothendieckTopology M) (integerPresheaf M)).app U).hom (1 : ℤ)) = _
  simpa [ModuleCat.hom_comp, LinearMap.comp_apply, integerOne, integerPresheaf] using
      (congrArg (fun g ↦ g.hom (1 : ℤ)) h).symm

def extendIntegerPresheaf :
    IntegralBetti.IntegerSheaf (TopCat.of M) ⥤ ((Opens M)ᵒᵖ ⥤ ModuleCat.{0} ℝ) :=
  sheafToPresheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℤ) ⋙
    (Functor.whiskeringRight (Opens M)ᵒᵖ (ModuleCat.{0} ℤ) (ModuleCat.{0} ℝ)).obj
      (ModuleCat.extendScalars (Int.castRingHom ℝ))

def extendIntegerSheaf : IntegralBetti.IntegerSheaf (TopCat.of M) ⥤ RealSheaf M :=
  extendIntegerPresheaf M ⋙ presheafToSheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℝ)

def constantTensorPresheafMap :
    (Functor.const (Opens M)ᵒᵖ).obj (ModuleCat.of ℝ ℝ) ⟶
      (extendIntegerPresheaf M).obj (IntegralBetti.integerConstantSheaf (TopCat.of M)) where
  app U := ModuleCat.ofHom (LinearMap.toSpanSingleton ℝ _
    ((1 : ℝ) ⊗ₜ[ℤ, Int.castRingHom ℝ] integerOne M U))
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    let cR : ℝ := c
    change cR • ((1 : ℝ) ⊗ₜ[ℤ, Int.castRingHom ℝ] integerOne M V) =
      (ModuleCat.extendScalars (Int.castRingHom ℝ)).map
        ((IntegralBetti.integerConstantSheaf (TopCat.of M)).obj.map f)
          (cR • ((1 : ℝ) ⊗ₜ[ℤ, Int.castRingHom ℝ] integerOne M U))
    rw [map_smul, ModuleCat.ExtendScalars.map_tmul, integerOne_natural]

/-- Canonical c↦c⊗1 coefficient-unit comparison, including sheafification. -/
def constantTensorUnit : realConstantSheaf M ⟶
    (extendIntegerSheaf M).obj (IntegralBetti.integerConstantSheaf (TopCat.of M)) :=
  (presheafToSheaf (Opens.grothendieckTopology M) (ModuleCat.{0} ℝ)).map
    (constantTensorPresheafMap M)

class IntegerCoefficientTheory : Prop where
  [additive : (extendIntegerSheaf M).Additive]
  [limits : PreservesFiniteLimits (extendIntegerSheaf M)]
  [colimits : PreservesFiniteColimits (extendIntegerSheaf M)]
  [unitIso : IsIso (constantTensorUnit M)]

attribute [instance] IntegerCoefficientTheory.additive IntegerCoefficientTheory.limits
  IntegerCoefficientTheory.colimits IntegerCoefficientTheory.unitIso

variable [IntegerCoefficientTheory M]

def derivedIntegerExtension : IntegralBetti.IntegerDerived (TopCat.of M) ⥤ RealDerived M :=
  (extendIntegerSheaf M).mapDerivedCategory

instance derivedIntegerCommShift : (derivedIntegerExtension M).CommShift ℤ := by
  dsimp [derivedIntegerExtension]
  infer_instance

def coefficientUnitIso :
    (derivedIntegerExtension M).obj (IntegralBetti.integerUnit (TopCat.of M)) ≅ realUnit M :=
  ((extendIntegerSheaf M).mapDerivedCategorySingleFunctor 0).app
      (IntegralBetti.integerConstantSheaf (TopCat.of M)) ≪≫
    (DerivedCategory.singleFunctor (RealSheaf M) 0).mapIso (asIso (constantTensorUnit M)).symm

def integralCoefficientMap (x : IntegralBetti.Cohomology (TopCat.of M) 2) : RealBettiH2 M :=
  (coefficientUnitIso M).inv ≫ (derivedIntegerExtension M).map x ≫
    ((derivedIntegerExtension M).commShiftIso (2 : ℤ)).hom.app
      (IntegralBetti.integerUnit (TopCat.of M)) ≫
        (shiftFunctor (RealDerived M) (2 : ℤ)).map (coefficientUnitIso M).hom

def integralSmoothClass (R : DeRhamResolution n M) (B : RealDeRhamComparison n M R)
    (x : IntegralBetti.Cohomology (TopCat.of M) 2) : RealH2 n M :=
  B.equiv.symm (integralCoefficientMap M x)

/-- Actual scalar extension of the integral cohomology lattice, fixed on
every integral class by the preceding native coefficient map. -/
structure IntegralRealComparison (R : DeRhamResolution n M) (B : RealDeRhamComparison n M R) where
  equiv : ℝ ⊗[ℤ] IntegralBetti.Cohomology (TopCat.of M) 2 ≃ₗ[ℝ] RealH2 n M
  normalization : ∀ x : IntegralBetti.Cohomology (TopCat.of M) 2,
    equiv (TensorProduct.tmul ℤ (1 : ℝ) x) = integralSmoothClass n M R B x

end MathlibExt.AlgebraicGeometry.SmoothDeRhamBettiBridge
