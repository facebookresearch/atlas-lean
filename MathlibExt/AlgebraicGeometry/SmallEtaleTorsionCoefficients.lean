/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/AlgebraicGeometry/EtaleCohomology/KummerTheory/MultiplicativeSheaf.lean`
(`multiplicativePresheaf`, `powMap`, `rootsOfUnitySheaf`) and
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/KummerTheory/Sequence.lean`
(`kummerSequence`)
(AxiomMath/Stacks, https://github.com/AxiomMath/Stacks, revision
c496df0d9beea9deaeabcea8492605f9a0a2313b):
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source files carry no per-file copyright notice or author list.
Modified: canonical integer modules on the abelian groups; the small-site sheaf and
exactness proofs are recorded as explicit inputs; tensor Tate coefficients and the
Yoneda Kummer class are built here.
-/
module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Data.ZMod.Basic

/-!
# Fixed small-étale torsion coefficients and Yoneda Kummer classes

G_m uses the actual units of regular functions on the native small étale
site. μ_l is its actual power-map kernel. Tate coefficients are literal
ordinary tensor powers, with degree zero the actual constant Z/l sheaf.
Cohomology is native Ext from the actual constant integer coefficient unit.

The generic small-site sheaf condition, Kummer short exactness and
sheafification/derived existence are completed source/native integration
inputs. No μ_l carrier, Kummer class or field cohomology group is supplied
freely. In particular, actual twists are retained without choosing roots
of unity in the base field.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SmallEtaleTorsionCoefficients

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

abbrev Scalar := ULift.{1} ℤ

/-- The canonical integer-module functor on actual abelian groups. -/
def integerModules : AddCommGrpCat.{1} ⥤ ModuleCat.{1} ℤ where
  obj A := ModuleCat.of ℤ A
  map f := ModuleCat.ofHom f.hom.toIntLinearMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The fixed regular-unit coefficient functor, with canonical integer scalar action. -/
def unitCoefficientFunctor : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} Scalar :=
  Scheme.Γ ⋙
    forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙
      commGroupAddCommGroupEquivalence.functor ⋙ AddCommGrpCat.uliftFunctor.{1,0} ⋙
        integerModules ⋙ ModuleCat.restrictScalars
          (ULift.ringEquiv : Scalar ≃+* ℤ).toRingHom

/-- The presheaf of units of regular functions on the small étale site of a scheme $X$: an étale
$X$-scheme $U$ goes to the unit group $\Gamma(U, \mathcal{O}_U)^\times$, written additively and
viewed as a module over `Scalar` (the integers, lifted to universe 1), and a morphism of étale
$X$-schemes to the induced map on units. -/
def multiplicativePresheaf (X : Scheme.{0}) : X.Etaleᵒᵖ ⥤ ModuleCat.{1} Scalar :=
  (Scheme.Etale.forget X ⋙ Over.forget X).op ⋙ unitCoefficientFunctor

/-- The presheaf of units of regular functions, $U \mapsto \Gamma(U, \mathcal{O}_U)^\times$ on the
small étale site of $X$ (as $\mathbb{Z}$-modules), is a sheaf for the small étale topology. -/
structure MultiplicativeNormalization (X : Scheme.{0}) : Prop where
  isSheaf : Presheaf.IsSheaf X.smallEtaleTopology (multiplicativePresheaf X)

abbrev Coefficients (X : Scheme.{0}) := Sheaf X.smallEtaleTopology (ModuleCat.{1} Scalar)

/-- Actual G_m sheaf, with its carrier fixed by the source units formula. -/
def multiplicativeSheaf (X : Scheme.{0}) (G : MultiplicativeNormalization X) : Coefficients X :=
  ⟨multiplicativePresheaf X, G.isSheaf⟩

variable (X : Scheme.{0}) (G : MultiplicativeNormalization X)
  [Abelian (Coefficients X)] [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{1} Scalar)]

attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- The actual power map on units, written additively as l times identity. -/
def powerMap (l : ℕ) : multiplicativeSheaf X G ⟶ multiplicativeSheaf X G :=
  l • 𝟙 (multiplicativeSheaf X G)

/-- Actual μ_l, the literal kernel of the actual power map. -/
def rootsSheaf (l : ℕ) : Coefficients X := kernel (C := Coefficients X) (powerMap X G l)

/-- Actual constant integer unit from which sheaf cohomology is Ext. -/
def constantUnit : Coefficients X :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{1} Scalar)).obj (ModuleCat.of Scalar Scalar)

/-- Literal tensor Tate coefficients; no trivialization of μ_l is assumed. -/
def tateTwist (l : ℕ) : ℕ → Coefficients X
  | 0 =>
      letI : Module Scalar (ULift.{1} (ZMod l)) :=
        Module.compHom _ (ULift.ringEquiv : Scalar ≃+* ℤ).toRingHom
      (constantSheaf X.smallEtaleTopology (ModuleCat.{1} Scalar)).obj
        (ModuleCat.of Scalar (ULift.{1} (ZMod l)))
  | 1 => rootsSheaf X G l
  | j+2 => (presheafToSheaf X.smallEtaleTopology (ModuleCat.{1} Scalar)).obj
      ((tateTwist l (j+1)).obj ⊗ (rootsSheaf X G l).obj)

/-- The Kummer short complex $\mu_l \to \mathbb{G}_m \to \mathbb{G}_m$ of sheaves on the small étale
site of $X$, for $l \in \mathbb{N}$: the inclusion of the kernel $\mu_l$ (`rootsSheaf`) of the
$l$-th power map of $\mathbb{G}_m$, followed by that power map (`powerMap`, written additively as
$l$ times the identity). Here $\mathbb{G}_m$ is the sheaf of units of regular functions
(`multiplicativeSheaf`, for the sheaf property $G$), in the category of sheaves of
`Scalar`-modules with its given abelian structure. -/
def kummerSequence (l : ℕ) : ShortComplex (Coefficients X) :=
  ShortComplex.mk (kernel.ι (powerMap X G l)) (powerMap X G l) (kernel.condition _)

/-- The condition that the Kummer sequence $0 \to \mu_l \to \mathbb{G}_m \to \mathbb{G}_m \to 0$
of sheaves on the small étale site of $X$, whose last map is the $l$-th power map
(`kummerSequence`), is short exact. -/
structure KummerExactness (l : ℕ) : Prop where
  shortExact : (kummerSequence X G l).ShortExact

variable [HasExt.{2} (Coefficients X)]

/-- Actual étale torsion cohomology, including all actual Tate coefficient twists. -/
abbrev Cohomology (l i j : ℕ) :=
  Abelian.Ext.{2} (constantUnit X) (tateTwist X G l j) i

/-- Source-normalized morphism represented by an actual global unit.
Its value on every integer section is the actual restricted unit's power. -/
structure UnitSection (a : (Γ(X, ⊤))ˣ) where
  map : constantUnit X ⟶ multiplicativeSheaf X G
  normalized : ∀ (U : X.Etale) (r : ℤ),
    map.hom.app (op U)
      (((sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{1} Scalar)).unit.app
        ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of Scalar Scalar))).app (op U)
          (ULift.up r)) =
    ULift.up (Additive.ofMul ((Units.map
      (U.hom.appTop.hom : Γ(X,⊤) →+* Γ(U.left,⊤)).toMonoidHom a)^r))

/-- The Kummer class is the actual Yoneda composition with the actual source extension class. -/
def kummerClass (l : ℕ) (E : KummerExactness X G l)
    (a : (Γ(X, ⊤))ˣ) (A : UnitSection X G a) : Cohomology X G l 1 1 := by
  change Abelian.Ext.{2} (constantUnit X) (rootsSheaf X G l) 1
  let eK : Abelian.Ext.{2} (multiplicativeSheaf X G) (rootsSheaf X G l) 1 :=
    ShortComplex.ShortExact.extClass.{2} (C := Coefficients X)
      (S := kummerSequence X G l) E.shortExact
  exact (Abelian.Ext.mk₀ A.map).comp eK (zero_add 1)

end MathlibExt.AlgebraicGeometry.SmallEtaleTorsionCoefficients
