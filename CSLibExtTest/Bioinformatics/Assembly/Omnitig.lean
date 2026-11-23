/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.Assembly.Omnitig
public meta import CSLibExt.Bioinformatics.Assembly.Omnitig

/-!
# Omnitig tests

A three-edge multigraph on two nodes: `e₀ : 0 → 1`, `e₁ : 1 → 0` and a loop `e₂ : 1 → 1`.
Non-vacuity: `[e₀, e₂, e₁]` is a circular edge-covering walk, and the single edge `[e₀]` is an
omnitig. Boundary: `[e₂, e₂]` is not an omnitig, witnessed by the forbidden path `[e₁, e₀]`
from `v₁ = 1` back to `v₁` that avoids `e₂` at both ends, and it is not a subwalk of the
covering walk `[e₀, e₂, e₁]`. The theorems instantiated: `[e₀]` is safe and `[e₂, e₂]` is not.
Axiom audit follows.
-/

namespace Cslib.Bioinformatics.Assembly.Omnitig

/-- The test multigraph: `e₀ : 0 → 1`, `e₁ : 1 → 0`, `e₂ : 1 → 1`. -/
def G : Multigraph (Fin 2) (Fin 3) where
  src e := if e = 0 then 0 else 1
  tgt e := if e = 1 then 0 else 1

/-- A circular edge-covering walk of `G`. -/
def cover : List (Fin 3) := [0, 2, 1]

/-- `[e₀, e₂, e₁]` is a circular edge-covering walk. -/
theorem isCircularCovering_cover : IsCircularCovering G cover := by
  refine ⟨by simp [cover], ?_, ?_, ?_⟩
  · simp [IsWalk, cover, G]
  · simp [cover, G]
  · decide

/-- Non-vacuity: the single edge `[e₀]` is an omnitig. -/
theorem isOmnitig_single : IsOmnitig G [0] := by
  refine ⟨by simp, by simp [IsWalk], ?_⟩
  intro i j hi hij hj
  simp at hj
  omega

/-- `[e₂, e₂]` is not an omnitig: `[e₁, e₀]` is a forbidden path. -/
theorem not_isOmnitig_loop_loop : ¬ IsOmnitig G [2, 2] := by
  rintro ⟨-, -, h⟩
  refine h 1 1 (Nat.le_refl 1) (Nat.le_refl 1) (by simp) [1, 0] ⟨by simp, ?_, ?_, ?_⟩
    1 (by simp) 0 (by simp) (by simp [G]) (by simp [G]) (by decide) (by decide)
  · simp [IsWalk, G]
  · simp [G]
  · simp [G]

/-- `[e₂, e₂]` does not occur in the circular walk `[e₀, e₂, e₁]`. -/
theorem not_isCircularSubwalk_loop_loop : ¬ IsCircularSubwalk [(2 : Fin 3), 2] cover := by
  rintro ⟨p, hp⟩
  have h0 := hp 0 (by simp)
  have h1 := hp 1 (by simp)
  simp only [cover, List.length_cons, List.length_nil, Nat.add_zero] at h0 h1
  have hmod : (p + 1) % 3 = (p % 3 + 1) % 3 := by omega
  rw [hmod] at h1
  have hcases : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hcases with hpm | hpm | hpm <;> simp_all

/-- The single edge `[e₀]` is safe: it is an omnitig. -/
example : IsSafe G [0] := isOmnitig_single.isSafe G

/-- `[e₂, e₂]` is not safe: a safe walk would be an omnitig. -/
example : ¬ IsSafe G [2, 2] := fun hs =>
  not_isOmnitig_loop_loop (isOmnitig_of_isSafe G (by simp) (by simp [IsWalk, G])
    ⟨cover, isCircularCovering_cover⟩ hs)

/-- Directly: `[e₂, e₂]` is not a subwalk of the covering walk `[e₀, e₂, e₁]`. -/
example : ¬ IsSafe G [2, 2] := fun hs =>
  not_isCircularSubwalk_loop_loop (hs cover isCircularCovering_cover)

#print axioms IsOmnitig.isSafe
#print axioms isOmnitig_of_isSafe

end Cslib.Bioinformatics.Assembly.Omnitig
