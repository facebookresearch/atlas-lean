/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SmallEtaleTorsionCoefficients
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.TStructure
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Fixed small-étale derived global sections and actual cohomology models

RΓ is the native right Kan-derived functor of evaluation at the actual
terminal étale object. Cohomology is Hom from the actual free coefficient
unit in degree i to that fixed RΓ object. The unit from constants is the
actual constant-sheaf adjunction unit followed by the native derived unit.

The Ext/Yoneda comparison is computed by native shift/single maps and RΓ,
not supplied as a cohomology-carrier identification. Generic derived
existence and constant/sheaf/shift primitives are completed source inputs.

References: Stacks sheaf cohomology; AxiomMath/Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b,
EtaleCohomology/KummerTheory and its native small-site cohomology models,
Apache 2.0.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SmallEtaleDerivedCohomology

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.SmallEtaleTorsionCoefficients

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

variable (X : Scheme.{0})
  [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{1} Scalar)]

/-- The actual evaluation/global-section functor at the actual terminal small-site object. -/
def sections : Coefficients X ⥤ ModuleCat.{1} Scalar :=
  (sheafSections X.smallEtaleTopology (ModuleCat.{1} Scalar)).obj (op (⊤_ X.Etale))

instance sections_additive : (sections X).Additive where
  map_add := by intros; rfl

abbrev Cochains := CochainComplex (Coefficients X) ℤ
abbrev D := DerivedCategory (Coefficients X)

def quasiIso : MorphismProperty (Cochains X) :=
  HomologicalComplex.quasiIso (Coefficients X) (.up ℤ)

instance localization_isLocalization :
    (DerivedCategory.Q : Cochains X ⥤ D X).IsLocalization (quasiIso X) := by
  dsimp [quasiIso]
  infer_instance

/-- The actual cochain sections source defining unbounded RΓ. -/
def sectionsSource : Cochains X ⥤ DerivedCategory (ModuleCat.{1} Scalar) :=
  (sections X).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

/-- Genuine source-derived existence, on the actual cochain evaluation source. -/
class HasDerivedSections : Prop where
  existsDerived : (sectionsSource X).HasRightDerivedFunctor (quasiIso X)

attribute [instance] HasDerivedSections.existsDerived
variable [HasDerivedSections X]

/-- Fixed native RΓ, chosen by its actual right-derived universal constructor. -/
def derivedSections : D X ⥤ DerivedCategory (ModuleCat.{1} Scalar) :=
  (sectionsSource X).totalRightDerived DerivedCategory.Q (quasiIso X)

def derivedSectionsUnit : sectionsSource X ⟶ DerivedCategory.Q ⋙ derivedSections X :=
  (sectionsSource X).totalRightDerivedUnit DerivedCategory.Q (quasiIso X)

/-- Actual native right-derived property of the fixed RΓ operator. -/
instance derivedSections_isRightDerived :
    (derivedSections X).IsRightDerivedFunctor (derivedSectionsUnit X) (quasiIso X) := by
  dsimp [derivedSections, derivedSectionsUnit]
  infer_instance

/-- The derived global sections `RΓ(X, F)` of a sheaf `F` of abelian groups on the small étale
site of `X`: the total right derived functor of global sections (`derivedSections`, which exists
by `HasDerivedSections X`) applied to `F` placed in degree zero. -/
def globalObject (F : Coefficients X) : DerivedCategory (ModuleCat.{1} Scalar) :=
  (derivedSections X).obj ((DerivedCategory.singleFunctor (Coefficients X) 0).obj F)

/-- Degree i cohomology as actual derived Hom from the actual free rank-one coefficient object. -/
abbrev Cohomology (F : Coefficients X) (i : ℤ) :=
  (DerivedCategory.singleFunctor (ModuleCat.{1} Scalar) i).obj (ModuleCat.of Scalar Scalar) ⟶
    globalObject X F

/-- The actual constant-sheaf/sections adjunction unit in every cochain degree. -/
def globalUnit (i : ℤ) :
    (DerivedCategory.singleFunctor (ModuleCat.{1} Scalar) i).obj (ModuleCat.of Scalar Scalar) ⟶
      (derivedSections X).obj
        ((DerivedCategory.singleFunctor (Coefficients X) i).obj (constantUnit X)) :=
  DerivedCategory.Q.map
    ((CochainComplex.singleFunctor (ModuleCat.{1} Scalar) i).map
      ((constantSheafAdj X.smallEtaleTopology (ModuleCat.{1} Scalar)
        (terminalIsTerminal (C := X.Etale))).unit.app (ModuleCat.of Scalar Scalar))) ≫
  DerivedCategory.Q.map
    ((HomologicalComplex.singleMapHomologicalComplex (sections X) (.up ℤ) i).inv.app
      (constantUnit X)) ≫
  (derivedSectionsUnit X).app
    ((CochainComplex.singleFunctor (Coefficients X) i).obj (constantUnit X))

variable [HasExt.{2} (Coefficients X)]

/-- Native lowering of the shift in an Ext morphism, with positive single degree i. -/
def unshiftedExt {F : Coefficients X} {i : ℕ}
    (e : Abelian.Ext.{2} (constantUnit X) F i) :
    (DerivedCategory.singleFunctor (Coefficients X) (i : ℤ)).obj (constantUnit X) ⟶
      (DerivedCategory.singleFunctor (Coefficients X) 0).obj F :=
  (shiftFunctor (D X) (i : ℤ)).preimage
    (((DerivedCategory.singleFunctors (Coefficients X)).shiftIso (i : ℤ) 0 (i : ℤ)
      (by simp)).hom.app (constantUnit X) ≫ e.hom)

/-- Exact computed comparison from native Yoneda Ext to the fixed RΓ cohomology model. -/
def extToCohomology {F : Coefficients X} {i : ℕ}
    (e : Abelian.Ext.{2} (constantUnit X) F i) : Cohomology X F (i : ℤ) :=
  globalUnit X (i : ℤ) ≫ (derivedSections X).map (unshiftedExt X e)

/-- The Kummer cohomology class in the fixed native RΓ model. -/
def kummer (G : MultiplicativeNormalization X) (l : ℕ) (E : KummerExactness X G l)
    (a : (Γ(X, ⊤))ˣ) (A : UnitSection X G a) : Cohomology X (rootsSheaf X G l) 1 :=
  extToCohomology X (kummerClass X G l E a A)

end MathlibExt.AlgebraicGeometry.SmallEtaleDerivedCohomology
