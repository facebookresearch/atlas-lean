/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Games.Parity

/-!
# Tests for parity games

* A two-position game where `even` owns both positions and can stay on priority `0`: `even` wins
  from everywhere with the positional strategy "go to `0`", so `odd` wins nowhere.
* A two-position game owned by `odd` where `odd` can stay on priority `1`: `odd` wins from
  everywhere.
-/

@[expose] public section

namespace Cslib.Games.ParityGame.Tests

open Cslib.ωSequence Filter

/-- Complete graph on two positions, both owned by `p`, with priority equal to the position. -/
def twoCycle (p : Player) : ParityGame (Fin 2) where
  owner _ := p
  Move _ _ := True
  priority i := i.val
  serial _ := ⟨0, trivial⟩

/-- The constant strategy moving to `target`. -/
def goTo (p : Player) (target : Fin 2) : (twoCycle p).PositionalStrategy p where
  next _ := target
  legal _ _ := trivial

/-- In a conforming play of a constant strategy owned everywhere by its player, every position
after the first is the target. -/
theorem conforms_goTo {p : Player} {target : Fin 2} {π : ωSequence (Fin 2)}
    (h : Conforms (goTo p target) π) (i : ℕ) : π (i + 1) = target :=
  h i rfl

theorem isMaxInfOcc_goTo {p : Player} {target : Fin 2} {π : ωSequence (Fin 2)}
    (h : Conforms (goTo p target) π) :
    IsMaxInfOcc (π.map (twoCycle p).priority) target.val := by
  have hev : ∀ᶠ k in atTop, (π.map (twoCycle p).priority) k = target.val := by
    rw [eventually_atTop]
    refine ⟨1, fun k hk => ?_⟩
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    simp [twoCycle, conforms_goTo h i]
  refine ⟨hev.frequently, fun m hm => ?_⟩
  obtain ⟨k, hk, hk'⟩ := (hm.and_eventually hev).exists
  omega

/-- `even` wins everywhere by staying on priority `0`. -/
example : (twoCycle .even).WinningRegion .even = Set.univ := by
  refine Set.eq_univ_of_forall fun v => ⟨goTo .even 0, fun π _ _ hconf => ?_⟩
  exact ⟨0, ⟨0, rfl⟩, isMaxInfOcc_goTo hconf⟩

/-- Hence `odd` wins nowhere in that game. -/
example : (twoCycle .even).WinningRegion .odd = ∅ := by
  have h := disjoint_winningRegion (twoCycle .even) .even
  have hall : (twoCycle .even).WinningRegion .even = Set.univ := by
    refine Set.eq_univ_of_forall fun v => ⟨goTo .even 0, fun π _ _ hconf => ?_⟩
    exact ⟨0, ⟨0, rfl⟩, isMaxInfOcc_goTo hconf⟩
  rw [hall] at h
  exact Set.univ_disjoint.mp h

/-- `odd` wins everywhere in its own game by staying on priority `1`. -/
example : (twoCycle .odd).WinningRegion .odd = Set.univ := by
  refine Set.eq_univ_of_forall fun v => ⟨goTo .odd 1, fun π _ _ hconf => ?_⟩
  exact ⟨1, odd_one, isMaxInfOcc_goTo hconf⟩

/-- Every play of the two-position game has exactly one winner. -/
example (π : ωSequence (Fin 2)) :
    (twoCycle .even).WonBy .even π ∨ (twoCycle .even).WonBy .odd π :=
  wonBy_or_wonBy_opponent (d := 1) (fun v => by simp [twoCycle]; omega) .even π

end Cslib.Games.ParityGame.Tests
