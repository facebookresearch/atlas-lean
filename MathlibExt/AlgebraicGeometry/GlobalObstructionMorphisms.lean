/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Global locally perfect obstruction-morphism contracts

The source is a native complex of module sheaves on an arbitrary scheme.
Amplitude [-1,0] is local in the derived sense: every point has an actual
open neighborhood on which the restriction is isomorphic to a finite-free
two-term mapping-cone complex. The public morphism contract uses actual
H0-isomorphism and H−1-epimorphism conditions on the native derived map.

This supplies the global perfect-amplitude/morphism portion of a perfect
obstruction theory. The target parameter is a specified actual complex;
identifying it with L_X/S remains a required source-normalized cotangent
provider. A freely named target is not declared to be a cotangent complex.
The complete external global constructor is
AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/Cotangent/SchemeCotangentComplex.lean (Apache 2.0), and is
port/comparison work rather than a new Wanted theorem.

Reference: Behrend--Fantechi, *The intrinsic normal cone*, §4,
https://arxiv.org/abs/alg-geom/9601010.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GlobalObstructionMorphisms

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
attribute [local instance] HasDerivedCategory.standard

/-- Integer-indexed cochain complexes of sheaves of modules on `X`. -/
abbrev Complex (X : Scheme.{0}) := CochainComplex X.Modules ℤ
/-- The derived category of sheaves of modules on `X`. -/
abbrev D (X : Scheme.{0}) := DerivedCategory X.Modules

/-- The free sheaf of modules of rank `r`. -/
abbrev freeModule (X : Scheme.{0}) (r : ℕ) :=
  SheafOfModules.free (R := X.ringCatSheaf) (Fin r)

/-- The two-term complex of a map between free sheaves of modules, in degrees `-1` and `0`. -/
def twoTerm (X : Scheme.{0}) (rMinus rZero : ℕ)
    (d : freeModule X rMinus ⟶ freeModule X rZero) : Complex X :=
  CochainComplex.mappingCone ((CochainComplex.singleFunctor X.Modules 0).map d)

/-- The restriction of a complex to an open subscheme. -/
def restriction {X : Scheme.{0}} (U : X.Opens) (E : Complex X) : Complex U.toScheme :=
  ((Scheme.Modules.pullback U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj E

/-- Actual local finite-perfect amplitude, including nontrivial vector bundles
and complexes not globally representable by one finite-free matrix. -/
def LocallyPerfectAmplitude {X : Scheme.{0}} (E : Complex X) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ rMinus rZero : ℕ,
    ∃ d : freeModule U.toScheme rMinus ⟶ freeModule U.toScheme rZero,
      Nonempty (DerivedCategory.Q.obj (restriction U E) ≅
        DerivedCategory.Q.obj (twoTerm U.toScheme rMinus rZero d))

/-- A morphism $\varphi : E \to L$ in the derived category of $\mathcal{O}_X$-modules, from a
complex $E$ of locally perfect amplitude in $[-1, 0]$ (on an open neighbourhood of every point,
isomorphic in the derived category to a two-term complex of finite free modules in degrees $-1$
and $0$) to the given complex $L$ (`target`), such that $H^0(\varphi)$ is an isomorphism and
$H^{-1}(\varphi)$ is an epimorphism. When $L$ is the relative cotangent complex, such a morphism
is a perfect obstruction theory. -/
structure ObstructionMorphism {X : Scheme.{0}} (target : Complex X) where
  source : Complex X
  amplitude : LocallyPerfectAmplitude source
  map : DerivedCategory.Q.obj source ⟶ DerivedCategory.Q.obj target
  [h0 : IsIso ((DerivedCategory.homologyFunctor X.Modules 0).map map)]
  [hMinus : Epi ((DerivedCategory.homologyFunctor X.Modules (-1)).map map)]
attribute [instance] ObstructionMorphism.h0 ObstructionMorphism.hMinus

/-- The extension obstruction is the actual composition with the supplied
normalized cotangent-to-square-zero-extension class. -/
def obstruction {X : Scheme.{0}} {target : Complex X} (P : ObstructionMorphism target)
    (M : X.Modules)
    (extensionClass : DerivedCategory.Q.obj target ⟶
      (DerivedCategory.singleFunctor X.Modules (-1)).obj M) :=
  P.map ≫ extensionClass

end MathlibExt.AlgebraicGeometry.GlobalObstructionMorphisms
