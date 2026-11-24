/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AnalyticProperSmoothSources

/-!
# Tests for smooth charts and restricted power series

The finite étale leg of a smooth chart is finite étale as a map of Tate pairs: the identity of a
pair qualifies, while a ring map whose target plus ring has an element that is not integral over
the source plus ring (for instance the identity of a ring into a larger plus ring) does not. The
restricted power series carry the standard plus ring, so scalars from the plus ring are integral.
-/

open MathlibExt.AlgebraicGeometry.AnalyticTateAdicModels
open MathlibExt.AlgebraicGeometry.AnalyticDiamondEtaleSites
open MathlibExt.AlgebraicGeometry.AnalyticProperSmoothSources

namespace MathlibExtTest.AnalyticProperSmoothSources

variable {p : ℕ} [Fact p.Prime]

/-- The identity map of a Tate pair. -/
private def tateId (V : TatePair p) : TateRingMap p V V :=
  ⟨RingHom.id V.ring, continuous_id, fun _ h ↦ h⟩

/-- The identity of a Tate pair can be the finite étale leg of a smooth chart. -/
example (V : TatePair p) : IsFiniteEtalePair p (tateId V) := by
  refine ⟨Module.Finite.self _, inferInstanceAs (Algebra.Etale V.ring V.ring), fun s ↦ ?_⟩
  change s ∈ V.plus ↔ V.plus.subtype.IsIntegralElem s
  constructor
  · intro hs
    exact V.plus.subtype.isIntegralElem_map (x := ⟨s, hs⟩)
  · intro hs
    have := V.plus_integral
    obtain ⟨y, hy⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := V.plus) (A := V.ring)).mp hs
    rw [← hy]
    exact y.property

/-- A ring map whose target plus ring contains an element not integral over the source plus ring
(such as the identity of a ring into a strictly larger plus ring) is never the finite étale leg of a
smooth chart. -/
example {X Y : AnalyticAdicSpace p} {f : X ⟶ Y} {x : X.obj.space} (c : SmoothChart p f x)
    (s : c.source.pair.ring) (hs : s ∈ c.source.pair.plus)
    (hn : ¬ (c.etale.hom.comp c.neighborhood.pair.plus.subtype).IsIntegralElem s) : False :=
  hn ((c.finite_etale.2.2 s).mp hs)

/-- Restricted power series carry the standard plus ring: scalars from the plus ring lie in it. -/
example {P : TatePair p} {n : ℕ} (T : TatePowerSeries p P n) {a : P.ring} (ha : a ∈ P.plus) :
    T.scalar.hom a ∈ T.pair.plus := by
  rw [T.plus_coefficients]
  intro d
  rw [T.scalar_coefficients]
  split_ifs
  · exact ha
  · exact zero_mem _

end MathlibExtTest.AnalyticProperSmoothSources
