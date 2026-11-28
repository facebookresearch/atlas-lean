/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Set.Card
import MathlibExt.Combinatorics.Enumerative.GridCylinderTorusTilings

/-! # Tests for `MathlibExt.Combinatorics.Enumerative.GridCylinderTorusTilings` -/

namespace MetaMathlibExt

-- All `3 ^ 2 = 9` maps from two cells to three designs are fixed by the identity.
example : fixedTilingCount (α := Fin 2) (T := Fin 3) id 1 = 9 := by
  decide +kernel

-- A cell map that cycles the three cells of `ZMod 3` fixes exactly the constant tilings.
example : fixedTilingCount (fun c : ZMod 3 => c + 1) (1 : Equiv.Perm (Fin 2)) = 2 := by
  decide +kernel

-- A swap on three cells has one pair and one fixed cell. With the same swap on the designs,
-- enumerate three fixed tilings independently of the restriction equivalence.
example : fixedTilingCount (Equiv.swap (0 : Fin 3) 1) (Equiv.swap (0 : Fin 3) 1) = 3 := by
  decide +kernel

private def swapFirstTwo : Equiv.Perm (Fin 3) := Equiv.swap 0 1

-- Choose design 1 at representative cell 0 and design 2 at fixed cell 2. Extension must
-- use the swapped design 0 at cell 1, and restriction must recover the two choices.
example :
    let e := fixedTilingsEquiv swapFirstTwo (by
        unfold Function.Involutive
        decide +kernel) (fun c => c = 0)
      (by decide +kernel) (by decide +kernel) swapFirstTwo (by
        unfold Function.Involutive
        decide +kernel)
    let F := e.symm (fun _ => 1, fun _ => ⟨2, by decide +kernel⟩)
    (F.val 0 = 1 ∧ F.val 1 = 0 ∧ F.val 2 = 2) ∧
      (e F).1 ⟨0, rfl⟩ = 1 ∧ ((e F).2 ⟨2, by decide +kernel⟩).val = 2 := by
  decide +kernel

-- The 2 × 3 grid with two designs: all `2 ^ 6 = 64` tilings are fixed by the identity.
example :
    fixedTilingCount (id : ZMod 2 × ZMod 3 → ZMod 2 × ZMod 3) (1 : Equiv.Perm (Fin 2)) = 64 := by
  rw [rectangularGrid_identity 2 3 1 (one_pow 1), Fintype.card_fin]
  rfl

-- The count of the theorem agrees with a direct computation on the 1 × 2 grid.
example :
    fixedTilingCount (id : ZMod 1 × ZMod 2 → ZMod 1 × ZMod 2) (1 : Equiv.Perm (Fin 3)) =
      Fintype.card (Fin 3) ^ (1 * 2) ∧
    fixedTilingCount (id : ZMod 1 × ZMod 2 → ZMod 1 × ZMod 2) (1 : Equiv.Perm (Fin 3)) = 9 :=
  ⟨rectangularGrid_identity 1 2 1 (one_pow 1), by decide +kernel⟩

-- Edge case `n = m = 1`: the grid has one cell, and each tile gives one fixed tiling.
example {T : Type*} [Fintype T] [DecidableEq T] (σ : Equiv.Perm T) (hσ : σ ^ 1 = 1) :
    fixedTilingCount (id : ZMod 1 × ZMod 1 → ZMod 1 × ZMod 1) σ = Fintype.card T := by
  rw [rectangularGrid_identity 1 1 σ hσ, Nat.mul_one, pow_one]

-- Edge case of no tiles: a grid with at least one cell has no tiling at all.
example (n m : ℕ) [NeZero n] [NeZero m] :
    fixedTilingCount (id : ZMod n × ZMod m → ZMod n × ZMod m) (1 : Equiv.Perm Empty) = 0 := by
  rw [rectangularGrid_identity n m 1 (one_pow 1), Fintype.card_empty,
    zero_pow (Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne m))]

-- The hypothesis `σ ^ 1 = 1` is needed: the swap of two designs fixes no design, so no tiling
-- of the 1 × 2 grid satisfies `F c = σ (F c)`, while `2 ^ (1 * 2) = 4`.
example :
    fixedTilingCount (id : ZMod 1 × ZMod 2 → ZMod 1 × ZMod 2) (Equiv.swap (0 : Fin 2) 1) = 0 := by
  decide +kernel

-- The 3 × 3 grid with two designs: all `2 ^ 9 = 512` tilings are fixed by the identity.
example :
    fixedTilingCount (id : ZMod 3 × ZMod 3 → ZMod 3 × ZMod 3) (1 : Equiv.Perm (Fin 2)) = 512 := by
  rw [squareGrid_identity 3 1 (one_pow 1), Fintype.card_fin]
  rfl

-- The count of the theorem agrees with a direct computation on the 2 × 2 grid.
example :
    fixedTilingCount (id : ZMod 2 × ZMod 2 → ZMod 2 × ZMod 2) (1 : Equiv.Perm (Fin 3)) =
      Fintype.card (Fin 3) ^ (2 ^ 2) ∧
    fixedTilingCount (id : ZMod 2 × ZMod 2 → ZMod 2 × ZMod 2) (1 : Equiv.Perm (Fin 3)) = 81 :=
  ⟨squareGrid_identity 2 1 (one_pow 1), by decide +kernel⟩

-- The square grid is the rectangular grid with `m = n`: both theorems count the same tilings.
example {T : Type*} [Fintype T] [DecidableEq T] (n : ℕ) [NeZero n] (σ : Equiv.Perm T)
    (hσ : σ ^ 1 = 1) : Fintype.card T ^ (n ^ 2) = Fintype.card T ^ (n * n) :=
  (squareGrid_identity n σ hσ).symm.trans (rectangularGrid_identity n n σ hσ)

-- Edge case `n = 1`: the grid has one cell, and each tile gives one fixed tiling.
example {T : Type*} [Fintype T] [DecidableEq T] (σ : Equiv.Perm T) (hσ : σ ^ 1 = 1) :
    fixedTilingCount (id : ZMod 1 × ZMod 1 → ZMod 1 × ZMod 1) σ = Fintype.card T := by
  rw [squareGrid_identity 1 σ hσ, one_pow, pow_one]

-- Edge case of a single design: every square grid has exactly one tiling.
example (n : ℕ) [NeZero n] :
    fixedTilingCount (id : ZMod n × ZMod n → ZMod n × ZMod n) (1 : Equiv.Perm Unit) = 1 := by
  rw [squareGrid_identity n 1 (one_pow 1), Fintype.card_unit, one_pow]

-- The hypothesis `σ ^ 1 = 1` is needed: the swap of two designs fixes no design, so no tiling
-- of the 2 × 2 grid satisfies `F c = σ (F c)`, while `2 ^ (2 ^ 2) = 16`.
example :
    fixedTilingCount (id : ZMod 2 × ZMod 2 → ZMod 2 × ZMod 2) (Equiv.swap (0 : Fin 2) 1) = 0 := by
  decide +kernel

-- On the smallest even square, swapping the two designs allows one choice per opposite pair.
example : fixedTilingCount (cellR2 2 2) (Equiv.swap (0 : Fin 2) 1) = 4 := by
  decide +kernel

-- An even square has no fixed tilings when there are no designs.
example : fixedTilingCount (cellR2 4 4) (1 : Equiv.Perm Empty) = 0 := by
  rw [squareGrid_r2_even 4 1 (one_pow 2) (by decide), Fintype.card_empty]
  decide

-- At prime width 3, the zero shift fixes all eight binary tilings and each other shift fixes two.
example : cylinderShiftSum 3 1 id (1 : Equiv.Perm (Fin 2)) = 12 := by
  rw [cylinder_identity (n := 3) (m := 1) (σ := 1) (hσ := one_pow 1)]
  decide +kernel

-- At composite width 4 and height 2, the orders 1, 2 and 4 contribute `256`, `16` and `2 * 4`.
example : cylinderShiftSum 4 2 id (1 : Equiv.Perm (Fin 2)) = 280 := by
  rw [cylinder_identity (n := 4) (m := 2) (σ := 1) (hσ := one_pow 1)]
  decide +kernel

-- At width 1 only the zero shift occurs; the two cells are colored independently.
example : cylinderShiftSum 1 2 id (1 : Equiv.Perm (Fin 3)) = 9 := by
  rw [cylinder_identity (n := 1) (m := 2) (σ := 1) (hσ := one_pow 1)]
  decide +kernel

-- On the 2 × 2 torus the zero shift fixes 16 binary tilings and each other shift fixes four.
example : torusShiftSum 2 2 id (1 : Equiv.Perm (Fin 2)) = 28 := by
  decide +kernel

-- On the 1 × 1 torus only the zero shift occurs, and each design gives one tiling.
example : torusShiftSum 1 1 id (1 : Equiv.Perm (Fin 2)) = 2 := by
  rw [squareTorus_identity 1 1 (one_pow 1)]
  decide +kernel

-- The square-torus divisor formula agrees with the direct 2 × 2 count above.
example : torusShiftSum 2 2 id (1 : Equiv.Perm (Fin 2)) = 28 := by
  rw [squareTorus_identity 2 1 (one_pow 1)]
  decide +kernel

-- On the 2 × 3 torus the two shifts of order six each fix the two constant tilings.
example : torusShiftSum 2 3 id (1 : Equiv.Perm (Fin 2)) = 84 := by
  rw [rectangularTorus_identity 2 3 1 (one_pow 1)]
  decide +kernel

-- On a single row of two cells a tile swap fixes only the two alternating tilings,
-- both under the nonzero shift.
example : torusShiftSum 1 2 id (Equiv.swap (0 : Fin 2) 1) = 2 := by
  decide +kernel

-- For `n = 5` and `a = 2` the coefficient is `(5 + 1) / 2 = 3`, and the unique solution is
-- `3 * (-1 - 2) = -9 = 1` in `ZMod 5`.
example : {x : ZMod 5 | x = -1 - x - 2} = {1} := by
  rw [reflection_shift_solutions_odd 5 2 (by decide)]
  exact congrArg _ (by decide)

-- That residue does solve the equation: `-1 - 1 - 2 = -4 = 1` in `ZMod 5`.
example : (1 : ZMod 5) = -1 - 1 - 2 := by decide

-- For `n = 7` and `a = 3`, every solution equals `4 * (-1 - 3) = -16 = 5` in `ZMod 7`.
example (x : ZMod 7) (hx : x = -1 - x - 3) : x = 5 := by
  have h : x ∈ {x : ZMod 7 | x = -1 - x - 3} := hx
  rw [reflection_shift_solutions_odd 7 3 (by decide), Set.mem_singleton_iff] at h
  exact h.trans (by decide)

-- Edge case `n = 1`: `ZMod 1` has a single element, and it is the solution for every `a`.
example (a : ZMod 1) : {x : ZMod 1 | x = -1 - x - a} = {0} := by
  rw [reflection_shift_solutions_odd 1 a odd_one]
  exact congrArg _ (Subsingleton.elim _ _)

-- For every odd modulus and every shift the equation has exactly one solution.
example (n : ℕ) [NeZero n] (a : ZMod n) (hn : Odd n) : ∃! x : ZMod n, x = -1 - x - a := by
  obtain ⟨hmem, huniq⟩ :=
    Set.eq_singleton_iff_unique_mem.mp (reflection_shift_solutions_odd n a hn)
  exact ⟨_, hmem, huniq⟩

-- The hypothesis `Odd n` is needed: modulo `4` the equation `x = -1 - x - 0` says `2 * x = -1`,
-- and has no solution because `2 * x` is even.
example : ∀ x : ZMod 4, x ≠ -1 - x - 0 := by decide

-- For `n = 6` and `a = 3` the two integers are `(-1 - 3) / 2 = -2` and `(6 - 1 - 3) / 2 = 1`,
-- so the solutions are `4` and `1` in `ZMod 6`.
example : {x : ZMod 6 | x = -1 - x - 3} = {4, 1} := by
  rw [reflection_shift_solutions_even_odd 6 3 (by decide) (by decide)]
  exact congrArg₂ (fun b c => ({b, c} : Set (ZMod 6))) (by decide) (by decide)

-- Both residues do solve the equation: `-1 - 4 - 3 = -8 = 4` and `-1 - 1 - 3 = -5 = 1`.
example : (4 : ZMod 6) = -1 - 4 - 3 ∧ (1 : ZMod 6) = -1 - 1 - 3 := by decide

-- For `n = 8` and `a = 5`, every solution is `(-1 - 5) / 2 = -3 = 5` or `(8 - 1 - 5) / 2 = 1`.
example (x : ZMod 8) (hx : x = -1 - x - 5) : x = 5 ∨ x = 1 := by
  have h : x ∈ {x : ZMod 8 | x = -1 - x - 5} := hx
  rw [reflection_shift_solutions_even_odd 8 5 (by decide) (by decide)] at h
  rcases h with h | h
  · exact Or.inl (h.trans (by decide))
  · exact Or.inr ((Set.mem_singleton_iff.mp h).trans (by decide))

-- Edge case `n = 2`: the only shift with odd representative is `1`, and the two residues
-- `(-1 - 1) / 2 = -1 = 1` and `(2 - 1 - 1) / 2 = 0` exhaust `ZMod 2`.
example : {x : ZMod 2 | x = -1 - x - 1} = Set.univ := by
  rw [reflection_shift_solutions_even_odd 2 1 (by decide) (by decide), Set.eq_univ_iff_forall]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  decide

-- For every even modulus and every shift with odd representative, the residue of
-- `(-1 - a.val) / 2` solves the equation.
example (n : ℕ) [NeZero n] (a : ZMod n) (hn : Even n) (ha : Odd a.val) :
    ((((-1 : ℤ) - a.val) / 2 : ℤ) : ZMod n) =
      -1 - ((((-1 : ℤ) - a.val) / 2 : ℤ) : ZMod n) - a := by
  have h : ((((-1 : ℤ) - a.val) / 2 : ℤ) : ZMod n) ∈ {x : ZMod n | x = -1 - x - a} := by
    rw [reflection_shift_solutions_even_odd n a hn ha]
    exact Set.mem_insert _ _
  exact h

-- The two residues differ by `n / 2`, so the equation always has exactly two solutions.
example (n : ℕ) [NeZero n] (a : ZMod n) (hn : Even n) (ha : Odd a.val) :
    {x : ZMod n | x = -1 - x - a}.ncard = 2 := by
  rw [reflection_shift_solutions_even_odd n a hn ha, Set.ncard_pair]
  obtain ⟨k, hk⟩ := hn
  obtain ⟨j, hj⟩ := ha
  have hk0 : 0 < k := by
    have := NeZero.pos n
    omega
  rw [Ne, ZMod.intCast_eq_intCast_iff_dvd_sub, hj, hk]
  push_cast
  rw [show ((k : ℤ) + k - 1 - (2 * j + 1)) / 2 - (-1 - (2 * j + 1)) / 2 = k by omega]
  intro h
  have := Int.le_of_dvd (by omega) h
  omega

-- The hypothesis `Even n` is needed: modulo `5` with `a = 1`, the second residue is
-- `(5 - 1 - 1) / 2 = 1` (integer division rounds down), and `1` is not a solution.
example : (((((5 : ℕ) : ℤ) - 1 - (1 : ZMod 5).val) / 2 : ℤ) : ZMod 5) = 1 ∧
    (1 : ZMod 5) ≠ -1 - 1 - 1 := by decide

-- The hypothesis `Odd a.val` is needed: modulo `4` with `a = 2` the equation says
-- `2 * x = -3`, and has no solution because `2 * x` is even.
example : ∀ x : ZMod 4, x ≠ -1 - x - 2 := by decide

end MetaMathlibExt
