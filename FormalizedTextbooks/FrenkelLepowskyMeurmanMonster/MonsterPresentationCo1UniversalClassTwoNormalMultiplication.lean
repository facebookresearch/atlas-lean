/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The ordered source coordinate section has exactly the original qBeta cocycle multiplication. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1UniversalClassTwoNormalLift

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped commutatorElement
set_option backward.isDefEq.respectTransparency false

/-- The actual source section realizes the precise cocycle of the existing extraspecial group. -/
theorem co1UniversalNormalLift_mul
    (hfinite : Finite (commutator Co1UniversalPresentation))
    (hcard : Nat.card (commutator Co1UniversalPresentation) ≤ 2)
    (hne : commutator Co1UniversalPresentation ≠ ⊥) (v w : Fin 24 → ZMod 2) :
    co1UniversalNormalLift hfinite hcard hne v * co1UniversalNormalLift hfinite hcard hne w =
      co1UniversalCentralEmbedding hfinite hcard hne (Multiplicative.ofAdd (qBeta v w)) *
        co1UniversalNormalLift hfinite hcard hne (v + w) := by
  let A := fun u : Fin 24 → ZMod 2 => co1UniversalHalfLift hfinite hcard hne 0
    (Multiplicative.ofAdd (fun i => u (Fin.castAdd 12 i)))
  let B := fun u : Fin 24 → ZMod 2 => co1UniversalHalfLift hfinite hcard hne 1
    (Multiplicative.ofAdd (fun i => u (Fin.natAdd 12 i)))
  let z := co1UniversalCentralEmbedding hfinite hcard hne (Multiplicative.ofAdd (qBeta v w))
  have hA : A (v + w) = A v * A w :=
    map_mul (co1UniversalHalfLift hfinite hcard hne 0) _ _
  have hB : B (v + w) = B v * B w :=
    map_mul (co1UniversalHalfLift hfinite hcard hne 1) _ _
  have hc : ⁅A v, B w⁆ = z := co1UniversalHalfLift_cross_commutator hfinite hcard hne v w
  have hs : A v * B w = z * B w * A v := by
    rw [← hc]
    simp only [commutatorElement_def, mul_assoc, inv_mul_cancel,
      mul_one]
  have hz : B v * z = z * B v :=
    Subgroup.mem_center_iff.mp
      (co1UniversalCentralEmbedding_mem_center hfinite hcard hne _) _
  change (B v * A v) * (B w * A w) = z * (B (v + w) * A (v + w))
  calc
    (B v * A v) * (B w * A w) = B v * (A v * B w) * A w := by simp only [mul_assoc]
    _ = B v * (z * B w * A v) * A w := by rw [hs]
    _ = (B v * z) * B w * (A v * A w) := by simp only [mul_assoc]
    _ = (z * B v) * B w * (A v * A w) := by rw [hz]
    _ = z * ((B v * B w) * (A v * A w)) := by simp only [mul_assoc]
    _ = z * (B (v + w) * A (v + w)) := by rw [← hA, ← hB]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
