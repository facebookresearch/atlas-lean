/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCo1GeometryPoints

/-! Actual subgroup conjugation preserves its Q intersection and binary image. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Each local subgroup element preserves the binary image of its own Q intersection. -/
theorem generatedAxisQImage_invariant (K : Subgroup H) (h : H) (hh : h ∈ K)
    (v : Fin 24 → ZMod 2) (hv : v ∈ localNormalQImage K) :
    co1BinaryAction (projH h) v ∈ localNormalQImage K := by
  induction h using QuotientGroup.induction_on with
  | H f =>
    obtain ⟨q, hq, hqv⟩ := hv
    have hqv : toAdd (qQuotHom q) = v := congrArg toAdd hqv
    have hm : inclQ (spinConjugation f.val.1 q) ∈ K := by
      rw [inclQ_spinConjugation]
      exact K.mul_mem (K.mul_mem hh hq) (K.inv_mem hh)
    have hi := mem_localNormalQImage_of_mem K (spinConjugation f.val.1 q) hm
    rw [← qBinaryAction_apply] at hi
    change spinBinaryAction f.val.1 (toAdd (qQuotHom q)) ∈ localNormalQImage K at hi
    rw [f.property, hqv] at hi
    exact hi

/-- A unique actual frame-class point in the Q image must be fixed by the whole local subgroup. -/
theorem generatedAxisQImage_unique_frame_fixed (K : Subgroup H)
    (w : Fin 24 → ZMod 2) (hw : w ∈ localNormalQImage K)
    (hp : w ∈ generatedCo1GeometryPoints)
    (hunique : ∀ v, v ∈ localNormalQImage K → v ∈ generatedCo1GeometryPoints → v = w)
    (h : H) (hh : h ∈ K) : co1BinaryAction (projH h) w = w :=
  hunique _ (generatedAxisQImage_invariant K h hh w hw)
    (generatedCo1GeometryPoints_action (projH h) w hp)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
