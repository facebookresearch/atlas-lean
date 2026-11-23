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
# Degree labels for moduli of stable maps

Li indexes moduli of relative stable maps by the degree of the pullback of a fixed ample line
bundle on the target (J. Li, *Stable morphisms to singular schemes and relative stable
morphisms*, J. Differential Geom. 57 (2001), Def. 4.6; *A degeneration formula of GW-invariants*,
J. Differential Geom. 60 (2002), §§2–3). Such a degree is locally constant in flat proper
families of curves, unlike the rational Chow class of the image curve, so it labels unions of
connected components of the moduli of stable maps, which are of finite type.

## Main definitions

* `DegreeLabel X`: an ample line bundle on `X` and a degree.
* `HasFibreDegree π map L d`: every geometric fibre of the family of maps `map` over `π` pulls
  `L` back to a line bundle of degree `d` on the fibre curve.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StableMapDegreeLabels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open CoherentCurveLinearSeries ProjectiveLineSystems

/-- A component label for moduli of stable maps to `X`: an ample line bundle on `X` and the
degree of its pullback to the source curves. -/
structure DegreeLabel (X : Scheme.{0}) [IsNoetherian X] where
  /-- The polarization. -/
  line : LineBundle X
  ample : IsAmpleLine line
  /-- The degree of the pullback of `line` to the source curves. -/
  degree : ℕ

/-- Every geometric fibre `C_p` of the family of maps `map : C ⟶ X` over `π : C ⟶ S` is a
proper curve on which the pullback of `L` is a line bundle of degree `d`. -/
def HasFibreDegree {C X S : Scheme.{0}} (π : C ⟶ S) (map : C ⟶ X) (L : X.Modules) (d : ℕ) :
    Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (.of Ω) ⟶ S),
    ∃ (_ : IsProperCurve (pullback.snd π p))
      (hL : IsLineBundle ((Scheme.Modules.pullback (pullback.fst π p ≫ map)).obj L)),
      degree (pullback.snd π p) _ hL = d

end MathlibExt.AlgebraicGeometry.StableMapDegreeLabels
