/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StackFibreModels
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Cartesian modules on actual affine stack points

Objects are affine schemes with an object of the native fibre groupoid.
The ring presheaf is the actual global-section ring of that scheme.
Cartesian restriction is its universal scalar-extension property, checked
on the actual semilinear presheaf map. Constant rank is checked by genuine
localized finite bases, not by a freely assigned rank function.

The affine cartesian-module/QCoh dictionary is completed public mathematics
in AxiomMath/Stacks at c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/
QuasiCoherentCartesianEquivalence.lean (Apache License 2.0).
This module supplies a native dictionary without re-requesting that theorem.
-/

@[expose] public noncomputable section
namespace AlgebraicGeometry.StackAffineModules

open CategoryTheory CategoryTheory.Limits Opposite
open GeneralStackGeometry StackCycleGeometry StackFibreModels

variable {S : Scheme.{0}}

abbrev AffinePoint (X : Stack S) :=
  (show ObjectProperty (Total X) from fun t => IsAffine t.base.left).FullSubcategory

def pointScheme (X : Stack S) : AffinePoint X ⥤ Scheme.{0} :=
  (show ObjectProperty (Total X) from fun t => IsAffine t.base.left).ι ⋙
    Pseudofunctor.CoGrothendieck.forget X.toPseudofunctor ⋙ Over.forget S

def rings (X : Stack S) : (AffinePoint X)ᵒᵖ ⥤ CommRingCat.{0} :=
  (pointScheme X).op ⋙ Scheme.Γ

abbrev ModulePresheaf (X : Stack S) :=
  PresheafOfModules.{0} (rings X ⋙ forget₂ CommRingCat RingCat)

/-- The canonical scalar-extension universal property of the actual
restriction map; no independently assigned base-change equivalence. -/
def IsCartesian {X : Stack S} (M : ModulePresheaf X) : Prop :=
  ∀ {a b : (AffinePoint X)ᵒᵖ} (f : a ⟶ b) (N : ModuleCat.{0} ((rings X).obj b)),
    Function.Bijective (fun g : M.obj b →ₗ[((rings X).obj b)] N =>
      g.comp (M.restrictₛₗ f))

/-- Finitely presented cartesian modules are the affine dictionary for
coherent sheaves on finite-type Artin stacks over a field. -/
structure FPModule (X : Stack S) where
  presheaf : ModulePresheaf X
  cartesian : IsCartesian presheaf
  finitePresentation : ∀ a : (AffinePoint X)ᵒᵖ,
    Module.FinitePresentation ((rings X).obj a) (presheaf.obj a)

/-- The rank is witnessed on every principal affine neighborhood by an
actual finite basis of the localized module. -/
def HasConstantRank {X : Stack S} (M : FPModule X) (r : ℕ) : Prop :=
  ∀ (a : (AffinePoint X)ᵒᵖ) (q : PrimeSpectrum ((rings X).obj a)),
    ∃ f : (rings X).obj a, f ∉ q.asIdeal ∧
      Nonempty (Module.Basis (Fin r) (Localization.Away f)
        (LocalizedModule (Submonoid.powers f) (M.presheaf.obj a)))

abbrev VectorModule (X : Stack S) (r : ℕ) :=
  {M : FPModule X // HasConstantRank M r}

end AlgebraicGeometry.StackAffineModules
