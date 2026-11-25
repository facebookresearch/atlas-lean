/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.LogPairs

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

universe u
variable {k : Type u} [Field k] {n : ℕ}

/-- Actual global scalar units have zero divisor order, checking the
normalization needed for canonical-frame changes. -/
example (V : NormalVariety k n) (p : PrimePoint V) (c : kˣ) :
    V.X.left.ord (fractionScalar V c) p.val = 0 := by
  let : Nonempty (⊤ : V.X.left.Opens) := ⟨⟨genericPoint V.X.left, by trivial⟩⟩
  have hu : IsUnit (globalScalarMap V.X.hom (c : k)) :=
    (Units.isUnit c).map (globalScalarMap V.X.hom)
  simpa only [fractionScalar, RingHom.comp_apply] using
    V.X.left.ord_of_isUnit hu (x := p.val) (show p.val ∈ (⊤ : V.X.left.Opens) from by trivial)

/-- Cartier coefficients can be read in every genuine chart containing
the prime point, independent of the internal cover choice. -/
example (V : NormalVariety k n) (D : CartierAtlas V) (p : PrimePoint V)
    (i : Fin D.size) (hi : p.val ∈ D.opens i) :
    D.coefficient p = V.X.left.ord (D.functions i) p.val := D.coefficient_eq p i hi

/-- Local-to-rational coefficients use the actual structural scalar map. -/
example (V : NormalVariety k n) (x : V.X.left) (a : k) :
    localToField V x (localScalar V x a) = fractionScalar V a := by
  let : Algebra k (LocalRing V x) := localAlgebra V x
  let : Algebra k (FunctionField V) := fractionAlgebra V
  exact (localToField V x).commutes a
