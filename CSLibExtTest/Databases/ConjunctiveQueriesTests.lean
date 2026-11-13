/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Databases.ConjunctiveQueries

/-!
# Tests for conjunctive queries

Queries over a binary relation `R` (relation `0`) and a binary relation `S` (relation `1`):
* Proper containment through a non-identity homomorphism: `path2 = Q(x) :- R(x, y), R(y, z)` is
  contained in `edge = Q(x) :- R(x, u)` via `u ↦ y`, but `edge` is not contained in `path2`. The
  failure is checked both through `contained_iff_hom` (no homomorphism maps `path2` to `edge`) and
  directly on the database with the single fact `R(0, 1)`, where `edge` has an answer and `path2`
  none.
* Heads must be preserved: `Q(x) :- R(x, y)` is not contained in `Q(y) :- R(x, y)`.
* Body atoms must be mapped to body atoms: `Q(x) :- R(x, y)` is not contained in
  `Q(x) :- S(x, y)`.
-/

@[expose] public section

namespace Cslib.Databases.ConjunctiveQueriesTests

open Cslib.Databases.ConjunctiveQueries

/-- `Q(x) :- R(x, y), R(y, z)` with `x, y, z = 0, 1, 2`: starts of paths of length two. -/
def path2 : CQ := ⟨[0], [(0, [0, 1]), (0, [1, 2])]⟩

/-- `Q(x) :- R(x, u)` with `x, u = 0, 5`: starts of edges. -/
def edge : CQ := ⟨[0], [(0, [0, 5])]⟩

/-- The homomorphism from `edge` to `path2`: `u ↦ y` (`5 ↦ 1`), the identity elsewhere. -/
def g : ℕ → ℕ := fun v => if v = 5 then 1 else v

example : g ≠ id := fun h => absurd (congrFun h 5) (by decide)

example : Hom edge path2 g := by
  unfold Hom
  decide

/-- Every start of a path of length two starts an edge. -/
example : Contained path2 edge :=
  (contained_iff_hom path2 edge).mpr ⟨g, by unfold Hom; decide⟩

/-- No homomorphism maps `path2` to `edge`: the second atom `R(y, z)` would need `y ↦ x` while the
first atom `R(x, y)` needs `y ↦ u`. -/
example : ¬ Contained edge path2 := by
  rw [contained_iff_hom]
  rintro ⟨h, -, hbody⟩
  have h₁ := hbody (0, [0, 1]) (by simp [path2])
  have h₂ := hbody (0, [1, 2]) (by simp [path2])
  simp [edge] at h₁ h₂
  omega

/-- The database with the single fact `R(0, 1)`. -/
def D₀ : DB := fun r => if r = 0 then {[0, 1]} else ∅

/-- `edge` has the answer `0` on `D₀` (assignment `x, u ↦ 0, 1`)... -/
example : Satisfies D₀ edge g := by
  unfold Satisfies
  decide

/-- ...but no assignment satisfies `path2` on `D₀`. -/
theorem not_satisfies_path2 (τ : Assign) : ¬ Satisfies D₀ path2 τ := by
  intro hτ
  have h₁ := hτ (0, [0, 1]) (by simp [path2])
  have h₂ := hτ (0, [1, 2]) (by simp [path2])
  simp [D₀] at h₁ h₂
  omega

/-- The same non-containment, read off `D₀` without the homomorphism theorem. -/
example : ¬ Contained edge path2 := fun hC => by
  obtain ⟨τ, hτ, -⟩ := hC D₀ g (by unfold Satisfies; decide)
  exact not_satisfies_path2 τ hτ

/-- `Q(x) :- R(x, y)`. -/
def headX : CQ := ⟨[0], [(0, [0, 1])]⟩

/-- `Q(y) :- R(x, y)`: the same body with a different head. -/
def headY : CQ := ⟨[1], [(0, [0, 1])]⟩

/-- A homomorphism from `headY` to `headX` would have to send `y` both to `x` (heads) and to `y`
(body). -/
example : ¬ Contained headX headY := by
  rw [contained_iff_hom]
  rintro ⟨h, hhead, hbody⟩
  have h₁ := hbody (0, [0, 1]) (by simp [headY])
  simp [headX, headY] at hhead h₁
  omega

/-- `Q(x) :- S(x, y)`: the head of `headX` over the relation `S` instead of `R`. -/
def overS : CQ := ⟨[0], [(1, [0, 1])]⟩

/-- No homomorphism maps the `S`-atom of `overS` to an atom of `headX`, which only uses `R`. -/
example : ¬ Contained headX overS := by
  rw [contained_iff_hom]
  rintro ⟨h, -, hbody⟩
  have h₁ := hbody (1, [0, 1]) (by simp [overS])
  simp [headX] at h₁

end Cslib.Databases.ConjunctiveQueriesTests
