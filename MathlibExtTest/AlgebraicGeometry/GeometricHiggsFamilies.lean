/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.GeometricHiggsFamilies

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.GeometricHiggsFamilies

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

universe u

variable {k : Type u} [Field k] (C : Over (Spec (.of k))) [IsProperCurve C.hom]
  [SmoothOfRelativeDimension 1 C.hom] [IsIntegral C.left] {L : C.left.Modules}

-- A twisted line bundle on a smooth proper integral curve is stable: there is no
-- intermediate rank to test.
example (E : TwistedBundle C.left L 1) : IsStableCurve C E :=
  ⟨Nat.one_pos, fun _ hs hs1 ↦ absurd hs1 (by omega)⟩

-- Stability is only defined in positive rank.
example (E : TwistedBundle C.left L 0) : ¬ IsStableCurve C E :=
  fun h ↦ lt_irrefl 0 h.1

-- Stability implies semistability.
example {r : ℕ} (E : TwistedBundle C.left L r) (h : IsStableCurve C E) :
    IsSemistableCurve C E :=
  ⟨h.1, fun s hs hsr F i hi hF hQ hinv ↦ (h.2 s hs hsr F i hi hF hQ hinv).le⟩

end MathlibExt.AlgebraicGeometry.GeometricHiggsFamilies
