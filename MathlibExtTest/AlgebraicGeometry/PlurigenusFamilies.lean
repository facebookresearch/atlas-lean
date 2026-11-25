/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.PlurigenusFamilies

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.CurvePositivity
open MathlibExt.AlgebraicGeometry.PlurigenusFamilies

universe u

variable {k : Type u} [Field k] {n : ℕ}

-- The fiber conditions hold at every geometric point, over any algebraically closed
-- field `Ω`, not only at `k`-rational points of the base.
example (P : SmoothGeneralTypeFamilyOverCurve (k := k) n) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ P.B.left) :
    GeometricallyIrreducible (fiberStructure P.f x) ∧
      HasGeneralTypeGrowth (fiberStructure P.f x) (fiberCanonical P.f P.canonical x)
        (P.fiberDuality Ω x).line n :=
  ⟨P.fiberIrreducible Ω x, P.generalType Ω x⟩

-- The fiber of a proper family is proper, as `HasGeneralTypeGrowth` requires.
example (P : SmoothGeneralTypeFamilyOverCurve (k := k) n) (Ω : Type u) [Field Ω]
    (x : Spec (.of Ω) ⟶ P.B.left) : IsProper (fiberStructure P.f x) :=
  inferInstance

-- The plurigenus at a geometric point is the dimension over `Ω` of the sections of the
-- tensor powers of the fiber's canonical line.
example (P : SmoothGeneralTypeFamilyOverCurve (k := k) n) (Ω : Type u) [Field Ω]
    (x : Spec (.of Ω) ⟶ P.B.left) (m : ℕ) :
    plurigenus P x m =
      Module.finrank Ω (cohomology (fiberStructure P.f x)
        (power (fiberCanonical P.f P.canonical x) m) 0) := rfl

-- General-type growth is a lower bound `c m^n` with a positive constant, for all large `m`.
example {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (K : X.Modules)
    (hK : IsLineBundle K)
    (h : ∀ m : ℕ, ((m : ℚ) ^ n) ≤ Module.finrank k (cohomology f (power K m) 0)) :
    HasGeneralTypeGrowth f K hK n :=
  ⟨1, one_pos, 0, fun m _ ↦ by simpa using h m⟩

-- H-projectivity is the single definition of `RelativeProjectivity`, re-exported here.
example : @MathlibExt.AlgebraicGeometry.PlurigenusFamilies.IsHProjectiveOver =
    @MathlibExt.AlgebraicGeometry.RelativeProjectivity.IsHProjectiveOver := rfl
