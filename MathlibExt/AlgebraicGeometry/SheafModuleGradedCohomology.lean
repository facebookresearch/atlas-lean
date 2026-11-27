/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import MathlibExt.AlgebraicGeometry.ContinuousAdicRingModules

/-!
# Cohomology of the structure sheaf of a ringed site and its cup product

For a sheaf of rings `R` on a site, `Cohomology R n` is `Ext^n(R, R)` in sheaves of `R`-modules,
which is the cohomology `H^n` of the structure sheaf, since `R` represents global sections. The cup
product is the Yoneda product (`Abelian.Ext.comp`), with unit the identity in degree zero; it is
biadditive and associative, and corresponds to composition of shifted morphisms in the derived
category (`cup_toDerived`). Graded commutativity is not claimed (the site's ring need not be
commutative), nor any comparison with another model of derived global sections.

For the ring sheaf of continuous functions `C(-, E)` on a pro-étale site
(`ContinuousAdicRingModules`), constants give degree-zero classes (`Adic.constantClass`), injective
on nonempty schemes.

Sources: Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679,
Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean and
Mathlib/CategoryTheory/Shift/ShiftedHom.lean (Joël Riou, Apache 2.0).
Continuous coefficients: Bhatt--Scholze, Definition 6.8.1 and Lemma 4.2.12,
https://arxiv.org/abs/1309.1198.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SheafModuleGradedCohomology

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite

universe u v w e d

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Sheaves of modules over the sheaf of rings `R`. -/
abbrev Modules (R : Sheaf J RingCat.{w}) := SheafOfModules.{w} R

/-- `R` as a module over itself. -/
abbrev ringUnit (R : Sheaf J RingCat.{w}) : Modules R := SheafOfModules.unit R

variable (R : Sheaf J RingCat.{w}) [Abelian (Modules R)] [HasExt.{e} (Modules R)]

/-- `H^n` of the structure sheaf: `Ext^n(R, R)`. -/
abbrev Cohomology (n : ℕ) : Type e := Abelian.Ext (ringUnit R) (ringUnit R) n

/-- `Cohomology R n` as an object of `AddCommGrpCat`. -/
def cohomologyObject (n : ℕ) : AddCommGrpCat.{e} := AddCommGrpCat.of (Cohomology R n)

/-- The unit: the class of the identity in degree zero. -/
def one : Cohomology R 0 := Abelian.Ext.mk₀ (𝟙 (ringUnit R))

/-- The cup product (Yoneda product), landing in degree `c = a + b`. -/
def cup {a b c : ℕ} (x : Cohomology R a) (y : Cohomology R b) (h : a + b = c) :
    Cohomology R c := x.comp y h

/-- The cup product as a biadditive map. -/
def cupMap (a b c : ℕ) (h : a + b = c) :
    Cohomology R a →+ Cohomology R b →+ Cohomology R c :=
  Abelian.Ext.bilinearComp (ringUnit R) (ringUnit R) (ringUnit R) a b c h

@[simp] theorem one_cup {n : ℕ} (x : Cohomology R n) :
    cup R (one R) x (zero_add n) = x := Abelian.Ext.mk₀_id_comp x

@[simp] theorem cup_one {n : ℕ} (x : Cohomology R n) :
    cup R x (one R) (add_zero n) = x := Abelian.Ext.comp_mk₀_id x

/-- The cup product is associative. -/
theorem cup_assoc {a b c ab bc total : ℕ}
    (x : Cohomology R a) (y : Cohomology R b) (z : Cohomology R c)
    (hab : a + b = ab) (hbc : b + c = bc) (ht : a + b + c = total) :
    cup R (cup R x y hab) z (show ab + c = total by omega) =
      cup R x (cup R y z hbc) (show a + bc = total by omega) :=
  Abelian.Ext.comp_assoc x y z hab hbc ht

/-- The degree-zero class of a global section of `R` (multiplication by it). -/
def coefficientClass (s : (ringUnit R).sections) : Cohomology R 0 :=
  Abelian.Ext.mk₀ ((ringUnit R).unitHomEquiv.symm s)

theorem coefficientClass_injective : Function.Injective (coefficientClass R) :=
  (Abelian.Ext.mk₀_bijective (ringUnit R) (ringUnit R)).1.comp
    (ringUnit R).unitHomEquiv.symm.injective

@[simp] theorem coefficientClass_of_morphism (f : ringUnit R ⟶ ringUnit R) :
    coefficientClass R ((ringUnit R).unitHomEquiv f) = Abelian.Ext.mk₀ f := by
  simp [coefficientClass]

section DerivedRepresentation

variable [HasDerivedCategory.{d} (Modules R)]

/-- `R` in degree zero, in the derived category. -/
abbrev derivedUnit := (DerivedCategory.singleFunctor (Modules R) 0).obj (ringUnit R)

/-- `Ext^n(R, R)` as shifted morphisms in the derived category. -/
def homEquiv (n : ℕ) :
    Cohomology R n ≃+ (derivedUnit R ⟶ (derivedUnit R)⟦(n : ℤ)⟧) :=
  Abelian.Ext.homAddEquiv

/-- A class as a shifted morphism in the derived category. -/
abbrev toDerived {n : ℕ} (x : Cohomology R n) := (homEquiv R n) x

/-- The cup product is the composition of shifted morphisms. -/
theorem cup_toDerived {a b c : ℕ} (x : Cohomology R a) (y : Cohomology R b)
    (h : a + b = c) :
    toDerived R (cup R x y h) =
      ShiftedHom.comp (toDerived R x) (toDerived R y) (by omega) :=
  Abelian.Ext.comp_hom x y h

end DerivedRepresentation

namespace Adic

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open MathlibExt.AlgebraicGeometry.ContinuousAdicCoefficients
open MathlibExt.AlgebraicGeometry.ContinuousAdicRingModules

variable (E : Type) [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  (X : Scheme.{0})

/-- Cohomology of the ring sheaf `C(-, E)` on the small pro-étale site of `X`. -/
abbrev Cohomology [HasExt.{e} (CoefficientModules E X)] (n : ℕ) :=
  SheafModuleGradedCohomology.Cohomology (coefficientRing E X) n

/-- A constant as a global section of `C(-, E)`. -/
def constantSection (a : E) : (ringUnit (coefficientRing E X)).sections where
  val U := ContinuousMap.const ((ProEt.forget X).obj U.unop).left (ULift.up a)
  property _f := rfl

theorem constantSection_injective [Nonempty X] : Function.Injective (constantSection E X) := by
  intro a b h
  obtain ⟨x⟩ := ‹Nonempty X›
  let U : X.ProEt := ProEt.mk (𝟙 X)
  have h' := congrArg
    (fun s : (ringUnit (coefficientRing E X)).sections => s.val (op U)) h
  change (ContinuousMap.const X (ULift.up a) : C(X, ULift.{1} E)) =
    ContinuousMap.const X (ULift.up b) at h'
  exact congrArg ULift.down (congrArg (fun f : C(X, ULift.{1} E) => f x) h')

variable [HasExt.{e} (CoefficientModules E X)]

/-- The degree-zero class of a constant. -/
def constantClass (a : E) : Cohomology E X 0 :=
  coefficientClass (coefficientRing E X) (constantSection E X a)

theorem constantClass_injective [Nonempty X] : Function.Injective (constantClass E X) :=
  (coefficientClass_injective (coefficientRing E X)).comp (constantSection_injective E X)

@[simp] theorem constantClass_one :
    constantClass E X 1 = SheafModuleGradedCohomology.one (coefficientRing E X) := by
  have h : constantSection E X 1 = (ringUnit (coefficientRing E X)).unitHomEquiv
      (𝟙 (ringUnit (coefficientRing E X))) := by
    ext U
    rfl
  rw [constantClass, h, coefficientClass_of_morphism]
  rfl

@[simp] theorem constantClass_zero : constantClass E X 0 = 0 := by
  have h : constantSection E X 0 = (ringUnit (coefficientRing E X)).unitHomEquiv
      (0 : ringUnit (coefficientRing E X) ⟶ ringUnit (coefficientRing E X)) := by
    ext U
    rfl
  rw [constantClass, h, coefficientClass_of_morphism]
  exact Abelian.Ext.mk₀_zero _ _

/-- `unitUnderlyingIso` as a degree-zero `Ext` class. -/
def underlyingUnitClass [HasExt.{e} (CoefficientSheaf X E)] :
    Abelian.Ext ((underlying E X).obj (ringUnit (coefficientRing E X)))
      (continuousModuleSheaf E (ULift.{1} E) X) 0 :=
  Abelian.Ext.mk₀ (unitUnderlyingIso E X).hom

/-- The map from the constant sheaf `E` to `C(-, E)` (`unitCoefficientMap`) as a degree-zero `Ext`
class. -/
def coefficientUnitClass [HasExt.{e} (CoefficientSheaf X E)] :
    Abelian.Ext (ProEtaleCohomologyFunctoriality.constantUnit E X)
      (continuousModuleSheaf E (ULift.{1} E) X) 0 :=
  Abelian.Ext.mk₀ (unitCoefficientMap E X)

end Adic

end MathlibExt.AlgebraicGeometry.SheafModuleGradedCohomology
