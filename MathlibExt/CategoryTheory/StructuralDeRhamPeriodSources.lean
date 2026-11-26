/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GeneralPadicCoefficientFields
public import MathlibExt.CategoryTheory.UntiltingSheafSources
public import MathlibExt.CategoryTheory.SheafLocalGeneratorLocalization
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# The constructed absolute and naive structural de Rham period objects

The structural period sheaves here are the NAIVE ones: Scholze's original Definition 6.8
(arXiv:1205.3463v2), which item (3) of his erratum to that paper withdraws. There the theta-kernel completion is applied to the ordinary
pushout of `O` and the already `p`-inverted `B_inf`; the corrected `OB_dR⁺` sheafifies the colimit
over the stages `U_i` of the theta-adic completions of `(R_i⁺ ⊗̂_{W(κ)} A_inf(R, R⁺))[1/p]`, with
an integral, `p`-adically completed tensor product before inverting `p`. For the naive objects the
toric Taylor comparison (Proposition 6.10) fails, so no comparison theorem relying on it is
requested for them.

The original uncompleted `O` and positive ring `Rplus` are distinct.
`naiveStructuralInf` is the actual ring-sheaf pushout over the constant
`W(kappa)`. Naive structural positive periods are the native theta-kernel
completion of that pushout. Its full ring inverts images of LOCAL
GENERATORS OF THE ABSOLUTE theta line. The full structural theta ideal
is used for positive filtration powers, never as the denominator line.

All scalar arrows are the original pushout, completion, and
sheafified localization arrows. A Witt scalar source is an intermediate
source port; its analytic qualification is stated separately. There is
no higher cohomology object or comparison supplied here.

Reference: Scholze, arXiv:1205.3463v2, Definitions 6.1 and 6.8;
Bhatt--Morrow--Scholze, arXiv:1602.03148v3, Section 5.1.
Native Mathlib sheaf colimits and limits: Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.StructuralDeRhamPeriodSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MathlibExt.AlgebraicGeometry.GeneralPadicCoefficientFields
open SheafKernelCompletion SheafKernelCompletionMaps
open SheafScalarQuotients UntiltingSheafSources SheafLocalGeneratorLocalization

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J CommRingCat.{1}] (p : ℕ) [Fact p.Prime] (K : BaseField p)

/-- The actual constant Witt ring uses the original perfect residue field of K. -/
def constantWitt : Sheaf J CommRingCat.{1} :=
  constantRing (J := J) (WittVector p (BaseField.residueField p K))

variable (O Rplus : Sheaf J CommRingCat.{1}) (A : UntiltingData p Rplus)

/-- Original structural scalar sources before the pushout and completion. -/
structure WittScalarSource where
  toOriginal : constantWitt p K ⟶ O
  toInf : constantWitt p K ⟶ rationalInf p Rplus
  originalTheta : O ⟶ completedRegular p Rplus
  scalar_square : toOriginal ≫ originalTheta = toInf ≫ A.rationalTheta

namespace WittScalarSource

variable (W : WittScalarSource p K O Rplus A)

/-- The naive `O_B_inf`, formed from the ORIGINAL uncompleted O over constant W(kappa), with
`B_inf` already `p`-inverted (the withdrawn definition; see the module docstring). -/
def naiveStructuralInf : Sheaf J CommRingCat.{1} :=
  pushout W.toOriginal W.toInf

def originalToInf : O ⟶ W.naiveStructuralInf := pushout.inl _ _
def absoluteToInf : rationalInf p Rplus ⟶ W.naiveStructuralInf := pushout.inr _ _

/-- The theta map is the native pushout descent of the two original theta maps. -/
def structuralTheta : W.naiveStructuralInf ⟶ completedRegular p Rplus :=
  pushout.desc W.originalTheta A.rationalTheta W.scalar_square

@[reassoc (attr := simp)] theorem absolute_theta :
    W.absoluteToInf ≫ W.structuralTheta = A.rationalTheta := by
  exact pushout.inr_desc _ _ _

@[reassoc (attr := simp)] theorem original_theta :
    W.originalToInf ≫ W.structuralTheta = W.originalTheta := by
  exact pushout.inl_desc _ _ _

/-- The native theta-kernel completion of the naive `O_B_inf`: the naive structural positive
periods, not the corrected `OB_dR⁺` (see the module docstring). -/
def naiveStructuralPositive : Sheaf J CommRingCat.{1} :=
  completion W.naiveStructuralInf (completedRegular p Rplus) W.structuralTheta

def infToPositive : W.naiveStructuralInf ⟶ W.naiveStructuralPositive :=
  completionUnit W.naiveStructuralInf (completedRegular p Rplus) W.structuralTheta

def originalToPositive : O ⟶ W.naiveStructuralPositive := W.originalToInf ≫ W.infToPositive

def positiveTheta : W.naiveStructuralPositive ⟶ completedRegular p Rplus :=
  SheafKernelCompletion.completedTheta W.naiveStructuralInf
    (completedRegular p Rplus) W.structuralTheta

/-- Absolute positive scalars are mapped by all native finite completion maps. -/
def absoluteToPositive : A.deRhamPositive ⟶ W.naiveStructuralPositive :=
  completionMap (rationalInf p Rplus) (completedRegular p Rplus)
    W.naiveStructuralInf (completedRegular p Rplus) A.rationalTheta W.structuralTheta
    W.absoluteToInf (𝟙 _) (by simpa using W.absolute_theta)

/-- The absolute full ring retains every local theta-line generator. -/
def absoluteFull : Sheaf J CommRingCat.{1} :=
  localization A.deRhamPositive (completedRegular p Rplus) A.deRhamPositive
    A.completedTheta (𝟙 _)

def absolutePositiveToFull : A.deRhamPositive ⟶ absoluteFull p Rplus A :=
  unit A.deRhamPositive (completedRegular p Rplus) A.deRhamPositive A.completedTheta (𝟙 _)

/-- Structural full periods invert the ABSOLUTE theta line, never the structural ideal. -/
def naiveStructuralFull : Sheaf J CommRingCat.{1} :=
  localization A.deRhamPositive (completedRegular p Rplus) W.naiveStructuralPositive
    A.completedTheta W.absoluteToPositive

def positiveToFull : W.naiveStructuralPositive ⟶ W.naiveStructuralFull :=
  unit A.deRhamPositive (completedRegular p Rplus) W.naiveStructuralPositive
    A.completedTheta W.absoluteToPositive

def originalToFull : O ⟶ W.naiveStructuralFull := W.originalToPositive ≫ W.positiveToFull

def absoluteToFull : absoluteFull p Rplus A ⟶ W.naiveStructuralFull :=
  localizationMap A.deRhamPositive (completedRegular p Rplus) A.deRhamPositive
    A.completedTheta (𝟙 _) W.naiveStructuralPositive W.absoluteToPositive
      W.absoluteToPositive (by simp)

/-- Positive absolute filtration consists of actual ideal sheaf powers. -/
def absolutePositiveFiltration (n : ℕ) (U : Cᵒᵖ) : Ideal (A.deRhamPositive.obj.obj U) :=
  idealSheafPower A.deRhamPositive (completedRegular p Rplus) A.completedTheta n U

/-- Positive structural filtration uses the complete structural theta ideal sheaf. -/
def naiveStructuralPositiveFiltration (n : ℕ) (U : Cᵒᵖ) : Ideal (W.naiveStructuralPositive.obj.obj U) :=
  idealSheafPower W.naiveStructuralPositive (completedRegular p Rplus) W.positiveTheta n U

def absoluteFiltration (i : ℤ) :
    SaturatedSubmodule A.deRhamPositive (absoluteFull p Rplus A) (absolutePositiveToFull p Rplus A) :=
  fullFiltration A.deRhamPositive (completedRegular p Rplus) A.deRhamPositive
    A.completedTheta (𝟙 _) (completedRegular p Rplus) A.completedTheta i

def structuralFiltration (i : ℤ) :
    SaturatedSubmodule W.naiveStructuralPositive W.naiveStructuralFull W.positiveToFull :=
  fullFiltration A.deRhamPositive (completedRegular p Rplus) W.naiveStructuralPositive
    A.completedTheta W.absoluteToPositive (completedRegular p Rplus) W.positiveTheta i

end WittScalarSource

end MathlibExt.CategoryTheory.StructuralDeRhamPeriodSources
