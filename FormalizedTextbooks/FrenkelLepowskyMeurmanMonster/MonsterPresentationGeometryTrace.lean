/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual Griess-operator trace is a conjugacy invariant of genuine Monster geometry points. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryPoints
public import Mathlib.LinearAlgebra.Trace

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Trace of the literal actual Griess operator underlying an element of the generated group. -/
def monsterGeometryTrace (g : G) : ℝ := LinearMap.trace ℝ GriessSpace g.val.toLinearMap

/-- Actual group conjugation preserves the trace of the genuine Griess operator. -/
theorem monsterGeometryTrace_conjugation (g h : G) :
    monsterGeometryTrace (g * h * g⁻¹) = monsterGeometryTrace h := by
  change LinearMap.trace ℝ GriessSpace (g.val * h.val * g.val⁻¹).toLinearMap = _
  have he : (g.val * h.val * g.val⁻¹).toLinearMap = g.val.conj h.val.toLinearMap := by
    ext x
    rfl
  rw [he, LinearMap.trace_conj']
  rfl

/-- Every actual source point has the trace of the actual distinguished central involution. -/
theorem monsterGeometryPoint_trace (p : MonsterGeometryPoint) :
    monsterGeometryTrace p.val = monsterGeometryTrace generatedCentralInvolution := by
  obtain ⟨g, hg⟩ := isConj_iff.mp p.property
  rw [← hg, monsterGeometryTrace_conjugation]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
