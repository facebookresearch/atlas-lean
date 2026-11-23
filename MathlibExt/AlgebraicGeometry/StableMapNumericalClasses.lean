/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
public import MathlibExt.AlgebraicGeometry.ProjectiveLineSystems

/-!
# Numerical classes for moduli of stable maps

Li indexes moduli of relative stable maps by numerical data of the source curves measured
against line bundles on the target (J. Li, *Stable morphisms to singular schemes and relative
stable morphisms*, J. Differential Geom. 57 (2001), Def. 4.6; *A degeneration formula of
GW-invariants*, J. Differential Geom. 60 (2002), §§2–3). Degrees of line bundles are locally
constant in flat proper families of curves, unlike the rational Chow class of the image curve.
Recording the degree against every line bundle (the numerical class) also fixes the degree of
the canonical bundle, hence the expected dimension, which the degree against one polarization
does not; fixing the degree against an ample bundle gives finite type.

## Main definitions

* `NumericalClass X`: an integer for every line bundle on `X`.
* `HasFibreDegree π map L d`: every geometric fibre of the family of maps `map` over `π` pulls
  `L` back to a line bundle of degree `d` on the fibre curve.
* `HasNumericalClass π map β`: every geometric fibre has degree `β L` against each `L`.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StableMapNumericalClasses

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open CoherentCurveLinearSeries ProjectiveLineSystems

/-- A candidate numerical curve class on `X`: an integer for every line bundle on `X`. Through
`HasNumericalClass` it is the degree profile of a family of curves, a curve class up to
numerical equivalence. It labels the components of moduli of stable maps (Li, Def. 4.6):
unlike a rational Chow class it is locally constant in families, and unlike the degree against
a single polarization it fixes the degrees of the (log) canonical bundle, hence the expected
dimension. Labels are compared as integer-valued functions, not through line-bundle
presentations. -/
abbrev NumericalClass (X : Scheme.{0}) := LineBundle X → ℤ

/-- Every geometric fibre `C_p` of the family of maps `map : C ⟶ X` over `π : C ⟶ S` is a
proper curve on which the pullback of `L` is a line bundle of degree `d`. -/
def HasFibreDegree {C X S : Scheme.{0}} (π : C ⟶ S) (map : C ⟶ X) (L : X.Modules) (d : ℤ) :
    Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ S),
    ∃ (_ : IsProperCurve (pullback.snd π p))
      (hL : IsLineBundle ((Scheme.Modules.pullback (pullback.fst π p ≫ map)).obj L)),
      degree (pullback.snd π p) _ hL = d

/-- Every geometric fibre of the family of maps `map : C ⟶ X` over `π : C ⟶ S` has numerical
class `β`: its degree against each line bundle `L` on `X` is `β L`. -/
def HasNumericalClass {C X S : Scheme.{0}} (π : C ⟶ S) (map : C ⟶ X)
    (β : NumericalClass X) : Prop :=
  ∀ L : LineBundle X, HasFibreDegree π map L.val (β L)

end MathlibExt.AlgebraicGeometry.StableMapNumericalClasses
