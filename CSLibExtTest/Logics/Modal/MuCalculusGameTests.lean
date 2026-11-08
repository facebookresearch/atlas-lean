/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Modal.MuCalculusGame

/-!
# Tests for the μ-calculus model-checking game

Public-API checks on the two-world model `0 → 1`, `1 → 1`, with the atom true
only at `1`, plus the one-world reflexive model. Covered: game moves
(`Move`), binder priorities (`prio`, nesting depth), free-variable terminals
(`TerminalWin` with an environment), the `Wins` / satisfaction correspondence
(`wins_iff_sat`, `wins_iff_verifierWins`), and the totalized fragment game
(`fragmentGame`, `fragmentWins_iff_winningRegion`). These elaborate against
the public import, so they also pin the exported names. The in-file
regression `counterexample_parityWin_false` covers the nested-priority cycle;
these tests cover the remaining public surface.
-/

set_option autoImplicit false

open Cslib.Modal.MuCalculus.Game
open Cslib.Modal.MuCalculus
open Cslib.Modal
open Cslib.Games
open Cslib.Games.ParityGame

namespace CSLibExtTest.Logics.Modal.MuCalculusGame

/-- The two-world model `0 → 1`, `1 → 1`, with the atom true only at `1`. -/
def twoWorld : KripkeModel (Fin 2) Unit :=
  ⟨⟨0⟩, fun w v => (w = 0 ∧ v = 1) ∨ (w = 1 ∧ v = 1), fun w _ => w = 1⟩

/-- The one-world reflexive model, no atoms true. -/
def oneWorld : KripkeModel Unit Unit :=
  ⟨⟨Unit.unit⟩, fun _ _ => True, fun _ _ => False⟩

/-- The empty environment: no free variable is true anywhere. -/
def envBot : ℕ → Fin 2 → Prop := fun _ _ => False

/-- The environment with variable `0` true everywhere, rest false. -/
def envVar0 : ℕ → Fin 2 → Prop
  | 0 => fun _ => True
  | _ => fun _ => False

/-! ### Moves -/

example : Move twoWorld
    (⟨.and (.atom ()) (.top), 0, []⟩ : GamePosition Unit (Fin 2))
    ⟨.atom (), 0, []⟩ :=
  Move.andLeft

example : Move twoWorld
    (⟨.or (.atom ()) (.top), 0, []⟩ : GamePosition Unit (Fin 2))
    ⟨.top, 0, []⟩ :=
  Move.orRight

example : Move twoWorld
    (⟨.box (.atom ()), 0, []⟩ : GamePosition Unit (Fin 2))
    ⟨.atom (), 1, []⟩ :=
  Move.box (Or.inl ⟨rfl, rfl⟩)

example : Move twoWorld
    (⟨.dia (.atom ()), 0, []⟩ : GamePosition Unit (Fin 2))
    ⟨.atom (), 1, []⟩ :=
  Move.dia (Or.inl ⟨rfl, rfl⟩)

example : Move twoWorld
    (⟨.mu (.var 0), 0, []⟩ : GamePosition Unit (Fin 2))
    ⟨.var 0, 0, [.mu (.var 0)]⟩ :=
  Move.mu

example : Move twoWorld
    (⟨.var 0, 0, [.nu (.var 0)]⟩ : GamePosition Unit (Fin 2))
    ⟨.nu (.var 0), 0, []⟩ :=
  Move.var (by decide)

/-! ### Priorities: nesting depth, not fixed μ/ν ranks -/

example : prio (⟨.mu (.var 0), 0, []⟩ : GamePosition Unit (Fin 2)) = some 1 := rfl

example : prio (⟨.nu (.var 0), 0, [.mu (.var 0)]⟩ :
    GamePosition Unit (Fin 2)) = some 4 := rfl

example : prio (⟨.mu (.var 0), 0, [.nu (.var 0), .mu (.var 0)]⟩ :
    GamePosition Unit (Fin 2)) = some 5 := rfl

example : prio (⟨.atom (), 0, []⟩ : GamePosition Unit (Fin 2)) = none := rfl

example : prio (⟨.box (.atom ()), 0, []⟩ : GamePosition Unit (Fin 2)) = none := rfl

/-! ### Terminals: atoms and free variables read the environment -/

example : TerminalWin twoWorld envBot (⟨.atom (), 1, []⟩ : GamePosition Unit (Fin 2)) :=
  rfl

example : ¬ TerminalWin twoWorld envBot
    (⟨.atom (), 0, []⟩ : GamePosition Unit (Fin 2)) :=
  fun h => (by decide : ¬ (0 : Fin 2) = 1) h

example : TerminalWin twoWorld envBot
    (⟨.natom (), 0, []⟩ : GamePosition Unit (Fin 2)) :=
  fun h => (by decide : ¬ (0 : Fin 2) = 1) h

example : TerminalWin twoWorld envBot (⟨.top, 0, []⟩ : GamePosition Unit (Fin 2)) :=
  trivial

example : ¬ TerminalWin twoWorld envBot (⟨.bot, 0, []⟩ : GamePosition Unit (Fin 2)) :=
  fun h => h

/-- A free variable (`var 0` at empty stack) is won by Verifier exactly when
the environment says so: true here. -/
example : TerminalWin twoWorld envVar0
    (⟨.var 0, 0, []⟩ : GamePosition Unit (Fin 2)) :=
  trivial

/-- The same free variable is lost under the empty environment. -/
example : ¬ TerminalWin twoWorld envBot
    (⟨.var 0, 0, []⟩ : GamePosition Unit (Fin 2)) :=
  fun h => h

/-- A variable past the stack is free and shifted: `var 2` at stack length
`1` reads `env 1` (here false). -/
example : ¬ TerminalWin twoWorld envVar0
    (⟨.var 2, 0, [.nu (.var 0)]⟩ : GamePosition Unit (Fin 2)) := by
  show ¬ envVar0 (2 - 1) 0
  exact fun h => h

/-- A variable past the stack is free and shifted: `var 1` at stack length
`1` reads `env 0` (here true). -/
example : TerminalWin twoWorld envVar0
    (⟨.var 1, 0, [.nu (.var 0)]⟩ : GamePosition Unit (Fin 2)) :=
  trivial

/-- `var 0` at a nonempty stack is a *bound* variable: it has a move
(`Move.var`), so it is not a terminal position at all. -/
example : ∃ q, Move twoWorld
    (⟨.var 0, 0, [.nu (.var 0)]⟩ : GamePosition Unit (Fin 2)) q :=
  ⟨⟨.nu (.var 0), 0, []⟩, Move.var (by decide)⟩

/-! ### Closed formulas -/

example : Closed (MuFormula.mu (MuFormula.var 0 : MuFormula Unit)) :=
  Nat.le.refl

example : ¬ Closed (MuFormula.var 0 : MuFormula Unit) :=
  fun h => Nat.not_succ_le_zero 0 h

example : Closed (counterexampleFormula) :=
  Nat.le.refl

/-! ### Fragment winning region = satisfaction = winning strategies -/

example : Wins twoWorld (.and (.atom ()) (.top)) 1 := ⟨rfl, trivial⟩

example : ¬ Wins twoWorld (.and (.atom ()) (.top)) 0 := fun h => (by decide : ¬ (0 : Fin 2) = 1) h.1

example : Wins twoWorld (.dia (.atom ())) 0 := ⟨1, Or.inl ⟨rfl, rfl⟩, rfl⟩

example : Wins twoWorld (.box (.atom ())) 1 := by
  intro v hv
  rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd h1 (by decide : ¬ (1 : Fin 2) = 0)
  · exact h2

example : Wins twoWorld (.dia (.atom ())) 0 ↔
    sat twoWorld envBot (FixFreeFormula.toMu (.dia (.atom ()))) 0 :=
  wins_iff_sat twoWorld envBot _ _

example : Wins twoWorld (.atom ()) 1 ↔
    VerifierWins twoWorld envBot ⟨FixFreeFormula.toMu (.atom ()), 1, []⟩ :=
  wins_iff_verifierWins twoWorld envBot _ _

/-! ### Totalized fragment game (canonical parity game) -/

example : (fragmentGame twoWorld envBot).owner
    (FragPos.pos (.or (.atom ()) (.top)) 0) =
      Player.even := rfl

example : (fragmentGame twoWorld envBot).owner
    (FragPos.pos (.and (.atom ()) (.top)) 0) =
      Player.odd := rfl

example : fragPriority (FragPos.win : FragPos Unit (Fin 2)) = 0 := rfl

example : fragPriority (FragPos.lose : FragPos Unit (Fin 2)) = 1 := rfl

example : FragMove twoWorld envBot
    (FragPos.pos (.atom ()) 0 : FragPos Unit (Fin 2)) FragPos.lose :=
  FragMove.toLose (fun q hq => by cases hq) (fun h => (by decide : ¬ (0 : Fin 2) = 1) h)

example : FragMove twoWorld envBot
    (FragPos.pos (.atom ()) 1 : FragPos Unit (Fin 2)) FragPos.win :=
  FragMove.toWin (fun q hq => by cases hq) rfl

example : FragMove twoWorld envBot (FragPos.win : FragPos Unit (Fin 2)) FragPos.win :=
  FragMove.win_self

example : FragMove twoWorld envBot (FragPos.lose : FragPos Unit (Fin 2)) FragPos.lose :=
  FragMove.lose_self

example : (FragPos.pos (.atom ()) 1 :
    FragPos Unit (Fin 2)) ∈
      (fragmentGame twoWorld envBot).WinningRegion Player.even := by
  rw [← fragmentWins_iff_winningRegion twoWorld envBot (.atom ()) 1]
  exact rfl

example : (FragPos.pos (.atom ()) 0 :
    FragPos Unit (Fin 2)) ∉
      (fragmentGame twoWorld envBot).WinningRegion Player.even := by
  rw [← fragmentWins_iff_winningRegion twoWorld envBot (.atom ()) 0]
  exact fun h => (by decide : ¬ (0 : Fin 2) = 1) h

/-- Every arena position is embedded: `pos` carries only a fragment
formula and a world, so a fixpoint position such as `⟨μ X. X, w, []⟩`
is not a term of the arena type. -/
example : ∀ v : FragPos Unit (Fin 2),
    v = .win ∨ v = .lose ∨ ∃ φ w, v = .pos φ w := by
  intro v
  cases v with
  | pos φ w => exact Or.inr (Or.inr ⟨φ, w, rfl⟩)
  | win => exact Or.inl rfl
  | lose => exact Or.inr (Or.inl rfl)

/-- No `pos` position projects to the `μ X. X` game position: the
counterexample position from the review is not constructible in the
restricted arena. -/
example (φ : FixFreeFormula Unit) (w : Fin 2) :
    fragToPos ⟨.mu (.var 0), 0, []⟩ (FragPos.pos φ w) ≠ ⟨.mu (.var 0), 0, []⟩ := by
  intro h
  simp only [fragToPos] at h
  have h1 : FixFreeFormula.toMu φ = .mu (.var 0) := by
    simp only [Prod.mk.injEq] at h
    exact h.1
  cases φ <;> simp [FixFreeFormula.toMu] at h1

/-- Every fragment move strictly decreases the formula, so no infinite
`pos`-only play exists: this is why priority `0` on `pos` positions is
sound in the totalized fragment game. -/
example {φ φ' : FixFreeFormula Unit} {w w' : Fin 2}
    (h : FragMove twoWorld envBot (.pos φ w) (.pos φ' w')) :
    MuFormula.size (FixFreeFormula.toMu φ') <
      MuFormula.size (FixFreeFormula.toMu φ) := by
  have hMove := FragMove.pos_move_iff h
  obtain ⟨ψ, w'', hEq, hSize⟩ := move_of_toMu hMove
  have hToMu : FixFreeFormula.toMu φ' = FixFreeFormula.toMu ψ := by
    simp only [Prod.mk.injEq] at hEq
    exact hEq.1
  have hφ : φ' = ψ := FixFreeFormula.toMu_injective hToMu
  rw [hφ]
  exact hSize

/-- The fragment game is serial: every position has a move (terminal
positions move to `win`/`lose`). -/
example (v : FragPos Unit (Fin 2)) : ∃ w, (fragmentGame twoWorld envBot).Move v w :=
  (fragmentGame twoWorld envBot).serial v

end CSLibExtTest.Logics.Modal.MuCalculusGame
