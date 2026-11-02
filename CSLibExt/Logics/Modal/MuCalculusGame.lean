/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The model-checking game for the modal μ-calculus
-/
module

public import CSLibExt.Computability.Games.Parity
public import CSLibExt.Logics.Modal.MuCalculus
public import Mathlib.Data.List.Chain

/-!
# The model-checking game for the modal μ-calculus

The model-checking game for a μ-calculus formula on a finite Kripke model, in the
form of [Emerson-Jutla] and [Stirling]: two players, Verifier and Refuter, move a
token along positions `(φ, w, stack)` — the formula, the world, and the stack of
enclosing fixpoint binders (innermost first). Verifier owns disjunctions, diamonds,
and greatest fixed points; Refuter owns conjunctions, boxes, and least fixed points.
Unfolding a fixpoint pushes its binder on the stack; a variable jumps back to the
binder it refers to, restoring that binder's stack. A finite play ends at a position
with no moves: Verifier wins at true atoms, `⊤`, and boxes with no successors
(Refuter is stuck); Refuter wins at false atoms, `⊥`, and diamonds with no
successors. A free variable (one with no binder on the stack) is a terminal position
whose winner is read off the environment, shifted by the stack length: at
`(var n, w, st)` with `n ≥ st.length` the winner is `env (n - st.length) w`.
An infinite play is won by Verifier exactly when the *least* binder priority
occurring infinitely often is even. Only fixpoint-binder positions carry a
priority: a binder unfolded with `k` binders already on the stack gets priority
`2 * k + 1` if it is a `μ`-binder and `2 * k + 2` if it is a `ν`-binder, so
priorities strictly increase with nesting depth and outer binders dominate
inner ones. In particular, fixed priorities `μ ↦ 1`, `ν ↦ 2` would be wrong:
in `μ X. ν Y. X` the inner `ν` (priority `2`) would dominate the outer `μ`
(priority `1`) under max-parity and declare Verifier the winner, while the
formula is `⊥`. With nesting-depth priorities the least binder priority seen
infinitely often is the outer `μ`'s `1` (odd), so Refuter wins, as it should.

Main results:

* The game (positions, moves, owners, binder priorities, strategies, plays, the
  parity condition) for μ-calculus formulas, with free variables evaluated in
  the environment.
* `FixFreeFormula`, the fixpoint-free fragment, with `FixFreeFormula.toMu` and
  `wins_iff_sat`: the backward-induction winning region `Wins` for the fragment
  is exactly satisfaction.
* `wins_iff_verifierWins`: for the fragment, `Wins` is exactly the set of
  positions from which Verifier has a winning strategy. Since every move of the
  fragment game strictly decreases the formula, all fragment plays are finite, so
  the parity clause is vacuous there.
* `fragmentWins_iff_winningRegion`: the fragment game as a canonical
  `Cslib.Games.ParityGame` (`fragmentGame`, terminal positions totalized with
  absorbing winning/losing states): `Wins` is exactly the canonical winning
  region of the even player. `FragPos.pos` carries only embedded fragment
  positions `(φ, w)` (formula `toMu φ`, empty stack), so the arena contains
  no fixpoint positions at all: a position such as `⟨μ X. X, w, []⟩` is not
  a term of the arena type, and priority `0` on `pos` positions is sound
  because every fragment move strictly decreases the formula (so no
  infinite `pos`-only play exists). The bespoke
  `Strategy`/`StrategyWins`/`VerifierWins` API is retained for the general
  (fixpoint) game, where the arena has unboundedly many stack
  configurations; the canonical conversion for the general game
  (bounded-stack arena, priorities inverted to max-parity) is future work,
  documented in the section header.

The full correctness theorem — `VerifierWins` iff satisfaction for arbitrary
formulas, including alternating fixpoints — is *not* proved here: it needs
parity determinacy (positional determinacy of finite parity games), which is
`WantedExt` (`WantedExt/TheoryOfComputation/ParityDeterminacyWanted.lean`), and
the unfolding/approximant argument for alternating fixpoints. It is stated
explicitly as out of scope for this file. The corrected binder priorities in
this file are the ones that argument must use: the least binder priority
occurring infinitely often, with priorities increasing with nesting depth.

## References

- D. Kozen, *Results on the propositional μ-calculus*, Theoretical Computer Science
  27 (1983), 333-354 (the μ-calculus and its semantics).
- E. A. Emerson and C. S. Jutla, "Tree automata, μ-calculus and determinacy",
  *Proceedings of FOCS 1991*, 368-377 (the model-checking game and parity).
- C. Stirling, *Modal and Temporal Properties of Processes*, Springer 2001,
  Chapter 6 (the μ-calculus game).
- W. Zielonka, "Infinite games on finitely coloured graphs with applications to
  automata on infinite trees", *Theoretical Computer Science* 200 (1998), 135-183
  (parity games; determinacy is `WantedExt`).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib
namespace Modal
namespace MuCalculus
namespace Game

variable {World Atom : Type u}

/-- A position of the μ-calculus model-checking game: the formula, the world, and
the stack of enclosing fixpoint binders, innermost first. -/
abbrev GamePosition (Atom World : Type u) :=
  MuFormula Atom × World × List (MuFormula Atom)

/-- The player to move: `true` is Verifier, `false` is Refuter. -/
abbrev Player := Bool

/-- **Moves of the μ-calculus model-checking game.** Fix a Kripke model $M$ with accessibility
relation $R$. A game position $(\varphi, w, s)$ consists of a μ-calculus formula $\varphi$ (with
de Bruijn variables), a world $w$ and a stack $s$ of fixpoint binders, innermost first. The
moves are exactly the following. From $(\varphi \wedge \psi, w, s)$ and from
$(\varphi \vee \psi, w, s)$ to $(\varphi, w, s)$ and to $(\psi, w, s)$. From
$(\Box \varphi, w, s)$ and from $(\Diamond \varphi, w, s)$ to $(\varphi, v, s)$ for every world
$v$ with $w R v$. From $(\mu \varphi, w, s)$ to $(\varphi, w, s')$, where $s'$ is $s$ with
$\mu \varphi$ pushed on top, and likewise from $(\nu \varphi, w, s)$ to $(\varphi, w, s'')$,
where $s''$ is $s$ with $\nu \varphi$ pushed on top. From $(x_n, w, s)$, where $x_n$ is the
variable with de Bruijn index $n$ and $n$ is less than the length of $s$, to $(s_n, w, t)$,
where $s_n$ is the entry of $s$ at index $n$ (counting from $0$) and $t$ is $s$ with its first
$n + 1$ entries removed.

Source: C. Stirling, *Modal and Temporal
Properties of Processes*, Springer 2001, Chapter 6. -/
inductive Move (M : KripkeModel World Atom) :
    GamePosition Atom World → GamePosition Atom World → Prop
  /-- Refuter chooses a conjunct. -/
  | andLeft {φ ψ : MuFormula Atom} {w : World} {st : List (MuFormula Atom)} :
      Move M ⟨.and φ ψ, w, st⟩ ⟨φ, w, st⟩
  /-- Refuter chooses a conjunct. -/
  | andRight {φ ψ : MuFormula Atom} {w : World} {st : List (MuFormula Atom)} :
      Move M ⟨.and φ ψ, w, st⟩ ⟨ψ, w, st⟩
  /-- Verifier chooses a disjunct. -/
  | orLeft {φ ψ : MuFormula Atom} {w : World} {st : List (MuFormula Atom)} :
      Move M ⟨.or φ ψ, w, st⟩ ⟨φ, w, st⟩
  /-- Verifier chooses a disjunct. -/
  | orRight {φ ψ : MuFormula Atom} {w : World} {st : List (MuFormula Atom)} :
      Move M ⟨.or φ ψ, w, st⟩ ⟨ψ, w, st⟩
  /-- Refuter chooses a successor. -/
  | box {φ : MuFormula Atom} {w v : World} {st : List (MuFormula Atom)}
      (h : M.rel w v) : Move M ⟨.box φ, w, st⟩ ⟨φ, v, st⟩
  /-- Verifier chooses a successor. -/
  | dia {φ : MuFormula Atom} {w v : World} {st : List (MuFormula Atom)}
      (h : M.rel w v) : Move M ⟨.dia φ, w, st⟩ ⟨φ, v, st⟩
  /-- Unfold a least fixed point, pushing its binder on the stack. -/
  | mu {φ : MuFormula Atom} {w : World} {st : List (MuFormula Atom)} :
      Move M ⟨.mu φ, w, st⟩ ⟨φ, w, .mu φ :: st⟩
  /-- Unfold a greatest fixed point, pushing its binder on the stack. -/
  | nu {φ : MuFormula Atom} {w : World} {st : List (MuFormula Atom)} :
      Move M ⟨.nu φ, w, st⟩ ⟨φ, w, .nu φ :: st⟩
  /-- Jump back to the binder a variable refers to, restoring that binder's stack. -/
  | var {n : ℕ} {w : World} {st : List (MuFormula Atom)} (h : n < st.length) :
      Move M ⟨.var n, w, st⟩ ⟨st.getD n .bot, w, st.drop (n + 1)⟩

/-- **Owner of a game position.** The owner of a game position $(\varphi, w, s)$ is Verifier when
$\varphi$ is a disjunction, a diamond formula or a greatest fixed point, and Refuter for every
other formula.

Source: C. Stirling, *Modal and
Temporal Properties of Processes*, Springer 2001, Chapter 6. -/
def Owner : GamePosition Atom World → Player
  | ⟨.or _ _, _, _⟩ | ⟨.dia _, _, _⟩ | ⟨.nu _, _, _⟩ => true
  | _ => false

/-- **Priority of a game position.** Only fixpoint-binder positions carry a priority. For a
formula $\varphi$, a world $w$ and a binder stack $s$ of length $k$, the position
$(\mu X.\,\varphi, w, s)$, whose formula is the least fixpoint with body $\varphi$, has priority
$2k+1$, the position $(\nu X.\,\varphi, w, s)$, whose formula is the greatest fixpoint with body
$\varphi$, has priority $2k+2$, and every other position has no priority. Priorities strictly
increase with nesting depth, so the outermost binder regenerated infinitely often has the least
priority.

This is the nesting-depth refinement of the alternation-depth priority assignment: same-type
nesting counts toward the depth, which only refines the order (outer still strictly below inner)
and keeps parity tied to the binder kind. Fixed priorities ($\mu \mapsto 1$, $\nu \mapsto 2$)
under the greatest-recurring-priority rule would let an inner vacuous $\nu$ dominate an outer
$\mu$: in $\mu X.\,\nu Y.\,X$, whose denotation is empty, Verifier would win the only play.

Source: E. A. Emerson and C. S. Jutla, "Tree automata, μ-calculus and
determinacy", *Proceedings of FOCS 1991*, 368-377; C. Stirling, *Modal and
Temporal Properties of Processes*, Springer 2001, Chapter 6; J. A. Bradfield,
"The modal μ-calculus alternation hierarchy is strict", *Theoretical Computer
Science* 195 (1998), 133-153 (alternation depth). -/
def prio : GamePosition Atom World → Option ℕ
  | ⟨.mu _, _, st⟩ => some (2 * st.length + 1)
  | ⟨.nu _, _, st⟩ => some (2 * st.length + 2)
  | _ => none

/-- **Positions with no moves.** In a Kripke model $M$, a game position $p$ has no moves when
there is no position $q$ such that going from $p$ to $q$ is a move of the model-checking game
in $M$. -/
def NoMoves (M : KripkeModel World Atom) (p : GamePosition Atom World) : Prop :=
  ∀ q, ¬ Move M p q

/-- **Winner at a terminal position.** Let $M$ be a Kripke model and $\mathit{env}$ an environment
assigning a predicate on worlds to every index. At a game position $(\varphi, w, st)$, where $st$
is the stack of enclosing fixpoint binders and $|st|$ its length, Verifier wins exactly when
$\varphi$ is an atom $a$ true at $w$, a negated atom $\neg a$ with $a$ false at $w$, $\top$, a
box $\Box\psi$, or a variable with de Bruijn index $n \ge |st|$ such that
$\mathit{env}(n - |st|)$ holds at $w$. At every other position (a variable with index
$n < |st|$, $\bot$, a diamond, a conjunction, a disjunction or a fixpoint) Refuter wins.

The condition is consulted only at positions with no moves: a box with no successors leaves
Refuter stuck and a diamond with no successors leaves Verifier stuck, while a bound variable,
a conjunction, a disjunction and a fixpoint always have a move. The environment index is
shifted by $|st|$ because each binder on the stack shifts de Bruijn indices by one.

Source: C. Stirling, *Modal and Temporal Properties of
Processes*, Springer 2001, Chapter 6. -/
def TerminalWin (M : KripkeModel World Atom) (env : ℕ → World → Prop) :
    GamePosition Atom World → Prop
  | ⟨.atom a, w, _⟩ => M.valuation w a
  | ⟨.natom a, w, _⟩ => ¬ M.valuation w a
  | ⟨.var n, w, st⟩ => if n < st.length then False else env (n - st.length) w
  | ⟨.top, _, _⟩ => True
  | ⟨.bot, _, _⟩ => False
  | ⟨.box _, _, _⟩ => True
  | ⟨.dia _, _, _⟩ => False
  | _ => False

/-- **Parity winning condition.** For an infinite sequence of game positions $p_0, p_1, \dots$,
Verifier wins by the parity condition when there is an even priority $e$ such that infinitely
many positions $p_n$ have priority $e$, and every priority $e' < e$ is the priority of only
finitely many positions $p_n$. Equivalently, some priority occurs infinitely often and the least
such priority is even; in particular, if no priority occurs infinitely often, Verifier does not
win. Only fixpoint-binder positions carry a priority, so the other positions do not affect the
outcome.

The least-priority convention is what makes outer binders dominate: an outer binder has a smaller
priority than any binder nested inside it.

Source: E. A. Emerson and C. S. Jutla, "Tree
automata, μ-calculus and determinacy", *Proceedings of FOCS 1991*, 368-377. -/
def ParityWin (play : ℕ → GamePosition Atom World) : Prop :=
  ∃ e, Even e ∧ (∀ N, ∃ n, N ≤ n ∧ prio (play n) = some e) ∧
    ∀ e', e' < e → ∃ N, ∀ n, N ≤ n → prio (play n) ≠ some e'

/-- **Verifier strategy.** A Verifier strategy for the model-checking game on a Kripke model $M$
is a map $\sigma$ from game positions to game positions such that, at every Verifier-owned
position $p$ from which some move exists, there is a move from $p$ to $\sigma(p)$.

The move-respecting condition is what makes Verifier's winning meaningful: without it, a
strategy could "win" by choosing a non-move at a Verifier position, leaving no
legal play at all. -/
structure Strategy (M : KripkeModel World Atom) where
  /-- The chosen successor at a Verifier-owned position. -/
  choose : GamePosition Atom World → GamePosition Atom World
  /-- The chosen successor is a legal move whenever one exists. -/
  choose_move : ∀ p, Owner p = true → (∃ q, Move M p q) → Move M p (choose p)

/-- **Finite plays consistent with a strategy.** Fix a Kripke model $M$ and a Verifier strategy
$\sigma$. The finite plays from a position $p$ that follow $\sigma$ are the lists of positions
defined inductively: the one-element list $[p]$ is such a play; and if the game has a move from
$p$ to $q$, where $q$ is the position chosen by $\sigma$ at $p$ whenever Verifier owns $p$, then
$p$ followed by any such play from $q$ is such a play from $p$.

A play need not end at a position with no moves: every finite prefix counts. -/
inductive PlayFrom (M : KripkeModel World Atom) (σ : Strategy M) :
    GamePosition Atom World → List (GamePosition Atom World) → Prop
  /-- The trivial play. -/
  | single {p : GamePosition Atom World} : PlayFrom M σ p [p]
  /-- A move followed by a play from the successor. -/
  | cons {p q : GamePosition Atom World} {ps : List (GamePosition Atom World)}
      (h : Move M p q) (hσ : Owner p = true → q = σ.choose p) (hps : PlayFrom M σ q ps) :
      PlayFrom M σ p (p :: ps)

/-- **Last position of a play.** The last position of a finite list of game positions is its
final entry when the list is nonempty; the empty list has no last position. -/
def playLast (ps : List (GamePosition Atom World)) : Option (GamePosition Atom World) :=
  ps.getLast?

/-- **Winning strategy from a position.** Let $M$ be a Kripke model, $\mathit{env}$ an environment
assigning a predicate on worlds to every index, $\sigma$ a Verifier strategy for the
model-checking game on $M$ and $p$ a game position. A play is consistent with $\sigma$ when each
step is a move and, at every Verifier-owned position, goes to the position chosen by $\sigma$.
The strategy $\sigma$ wins from $p$ in $\mathit{env}$ when every finite play from $p$ consistent
with $\sigma$ whose last position has no moves ends in a position that is a terminal win for
Verifier in $\mathit{env}$, and every infinite play from $p$ consistent with $\sigma$ satisfies
the parity condition. -/
def StrategyWins (M : KripkeModel World Atom) (env : ℕ → World → Prop)
    (σ : Strategy M) (p : GamePosition Atom World) : Prop :=
  (∀ ps : List (GamePosition Atom World), PlayFrom M σ p ps →
    (∃ q, playLast ps = some q ∧ NoMoves M q) →
      ∃ q, playLast ps = some q ∧ TerminalWin M env q) ∧
  (∀ play : ℕ → GamePosition Atom World, play 0 = p →
    (∀ n, Move M (play n) (play (n + 1)) ∧
      (Owner (play n) = true → play (n + 1) = σ.choose (play n))) →
      ParityWin play)

/-- **Verifier has a winning strategy.** For a Kripke model $M$, an environment $\mathit{env}$
and a game position $p$, Verifier wins from $p$ when some Verifier strategy $\sigma$ in the
model-checking game on $M$ wins from $p$ in environment $\mathit{env}$: every complete finite
$\sigma$-consistent play from $p$ ends at a terminal winning position, and every infinite
$\sigma$-consistent play from $p$ satisfies the parity condition. -/
def VerifierWins (M : KripkeModel World Atom) (env : ℕ → World → Prop)
    (p : GamePosition Atom World) : Prop :=
  ∃ σ : Strategy M, StrategyWins M env σ p

/-! ### Closed formulas and the regression for nesting-depth priorities -/

/-- **Formulas closed at depth $d$.** Closedness of a μ-calculus formula $\varphi$ (with de Bruijn
variables) at a depth $d \in \mathbb{N}$ is defined by recursion on $\varphi$: atoms, negated
atoms, $\bot$ and $\top$ are closed at every depth; the variable with index $n$ is closed at
depth $d$ exactly when $n < d$; $\varphi \wedge \psi$ and $\varphi \vee \psi$ are closed at
depth $d$ when both $\varphi$ and $\psi$ are; $\Box\varphi$ and $\Diamond\varphi$ are closed at
depth $d$ when $\varphi$ is; and $\mu\varphi$ and $\nu\varphi$ are closed at depth $d$ when
$\varphi$ is closed at depth $d + 1$. Thus every free variable of $\varphi$ refers to one of $d$
enclosing binders.

Source: C. Stirling, *Modal and
Temporal Properties of Processes*, Springer 2001, Chapter 6 (de Bruijn
variables). -/
def ClosedAt : MuFormula Atom → ℕ → Prop
  | .atom _, _ => True
  | .natom _, _ => True
  | .var n, d => n < d
  | .bot, _ => True
  | .top, _ => True
  | .and φ ψ, d => ClosedAt φ d ∧ ClosedAt ψ d
  | .or φ ψ, d => ClosedAt φ d ∧ ClosedAt ψ d
  | .box φ, d => ClosedAt φ d
  | .dia φ, d => ClosedAt φ d
  | .mu φ, d => ClosedAt φ (d + 1)
  | .nu φ, d => ClosedAt φ (d + 1)

/-- **Closed formulas.** A μ-calculus formula $\varphi$ is closed when it is closed at depth $0$,
that is, when it has no free variables. -/
def Closed (φ : MuFormula Atom) : Prop := ClosedAt φ 0

/-- **Closedness is monotone in the depth.** Let $\varphi$ be a μ-calculus formula and let
$d \le d'$ be natural numbers. If $\varphi$ is closed at depth $d$ (every free variable of
$\varphi$ is less than $d$), then $\varphi$ is closed at depth $d'$: more enclosing binders can
only bind more variables. -/
theorem ClosedAt.mono {φ : MuFormula Atom} {d d' : ℕ} (h : d ≤ d')
    (hc : ClosedAt φ d) : ClosedAt φ d' := by
  induction φ generalizing d d' with
  | atom _ => trivial
  | natom _ => trivial
  | var n => exact Nat.lt_of_lt_of_le hc h
  | bot => trivial
  | top => trivial
  | and φ ψ ihφ ihψ => exact ⟨ihφ h hc.1, ihψ h hc.2⟩
  | or φ ψ ihφ ihψ => exact ⟨ihφ h hc.1, ihψ h hc.2⟩
  | box φ ih => exact ih h hc
  | dia φ ih => exact ih h hc
  | mu φ ih => exact ih (by omega) hc
  | nu φ ih => exact ih (by omega) hc

/-- **Satisfaction depends only on the environment below the closure depth.** Let $M$ be a
Kripke model, $\varphi$ a μ-calculus formula and $d$ a natural number such that $\varphi$ is
closed at depth $d$: every occurrence of a variable with de Bruijn index $n$ lying under $k$
fixpoint binders of $\varphi$ satisfies $n < d + k$. If two environments $\mathit{env}$ and
$\mathit{env}'$, each assigning a predicate on worlds to every index, agree at every index
$n < d$, then for every world $w$, $\varphi$ is satisfied at $w$ in $M$ under $\mathit{env}$ if
and only if it is satisfied at $w$ in $M$ under $\mathit{env}'$.

In particular, satisfaction of a closed formula is independent of the environment.

Source: D. Kozen, *Results on the propositional μ-calculus*,
Theoretical Computer Science 27 (1983), 333-354. -/
theorem sat_eq_of_closedAt (M : KripkeModel World Atom) :
    ∀ (φ : MuFormula Atom) {env env' : ℕ → World → Prop} {d : ℕ},
      (∀ n, n < d → env n = env' n) → ClosedAt φ d → ∀ w,
        sat M env φ w ↔ sat M env' φ w := by
  intro φ
  induction φ with
  | atom a => intro env env' d _ _ w; exact Iff.rfl
  | natom a => intro env env' d _ _ w; exact Iff.rfl
  | var n =>
      intro env env' d hagree hclosed w
      show env n w ↔ env' n w
      rw [hagree n hclosed]
  | bot => intro env env' d _ _ w; exact Iff.rfl
  | top => intro env env' d _ _ w; exact Iff.rfl
  | and φ ψ ihφ ihψ =>
      intro env env' d hagree hclosed w
      simp only [sat_and]
      exact and_congr (ihφ hagree hclosed.1 w) (ihψ hagree hclosed.2 w)
  | or φ ψ ihφ ihψ =>
      intro env env' d hagree hclosed w
      simp only [sat_or]
      exact or_congr (ihφ hagree hclosed.1 w) (ihψ hagree hclosed.2 w)
  | box φ ih =>
      intro env env' d hagree hclosed w
      simp only [sat_box]
      exact forall_congr' fun v => imp_congr_right fun _ => ih hagree hclosed v
  | dia φ ih =>
      intro env env' d hagree hclosed w
      simp only [sat_dia]
      exact exists_congr fun v => and_congr Iff.rfl (ih hagree hclosed v)
  | mu φ ih =>
      intro env env' d hagree hclosed w
      simp only [sat_mu]
      constructor
      · intro h S hS
        apply h S
        intro v hv
        apply hS v
        have hagree' : ∀ n, n < d + 1 →
            extendEnv env S n = extendEnv env' S n := by
          intro n hn
          cases n with
          | zero => rfl
          | succ n => exact hagree n (by omega)
        exact (ih hagree' hclosed v).mp hv
      · intro h S hS
        apply h S
        intro v hv
        apply hS v
        have hagree' : ∀ n, n < d + 1 →
            extendEnv env S n = extendEnv env' S n := by
          intro n hn
          cases n with
          | zero => rfl
          | succ n => exact hagree n (by omega)
        exact (ih hagree' hclosed v).mpr hv
  | nu φ ih =>
      intro env env' d hagree hclosed w
      simp only [sat_nu]
      constructor
      · rintro ⟨S, hS, hwS⟩
        have hagree' : ∀ n, n < d + 1 →
            extendEnv env S n = extendEnv env' S n := by
          intro n hn
          cases n with
          | zero => rfl
          | succ n => exact hagree n (by omega)
        refine ⟨S, ?_, hwS⟩
        intro v hv
        exact (ih hagree' hclosed v).mp (hS v hv)
      · rintro ⟨S, hS, hwS⟩
        have hagree' : ∀ n, n < d + 1 →
            extendEnv env' S n = extendEnv env S n := by
          intro n hn
          cases n with
          | zero => rfl
          | succ n => exact (hagree n (by omega)).symm
        refine ⟨S, ?_, hwS⟩
        intro v hv
        exact (ih hagree' hclosed v).mp (hS v hv)

/-- **Closed formulas are environment-independent.** Let $M$ be a Kripke model and $\varphi$ a
closed μ-calculus formula, that is, one with no free variables. For any two environments
$\mathrm{env}$ and $\mathrm{env}'$, each assigning a set of worlds to every variable index, and
every world $w$, $\varphi$ is satisfied at $w$ in $M$ under $\mathrm{env}$ if and only if it is
satisfied at $w$ in $M$ under $\mathrm{env}'$. -/
theorem sat_closed (M : KripkeModel World Atom) {φ : MuFormula Atom}
    (hφ : Closed φ) (env env' : ℕ → World → Prop) (w : World) :
    sat M env φ w ↔ sat M env' φ w :=
  sat_eq_of_closedAt M φ (fun n hn => absurd hn (by omega)) hφ w

/-- **The one-world reflexive Kripke model.** The Kripke model with a single world, which is
related to itself, and a single atom, which is false at that world. -/
def counterexampleModel : KripkeModel Unit Unit where
  nonempty_world := ⟨Unit.unit⟩
  rel := fun _ _ => True
  valuation := fun _ _ => False

/-- **A least fixpoint over a vacuous greatest fixpoint.** The μ-calculus formula
$\mu X.\, \nu Y.\, X$ over a one-element type of atoms: a least fixpoint whose body is a greatest
fixpoint whose body is the variable $X$ bound by the outer least fixpoint, so the variable $Y$
bound by the inner greatest fixpoint never occurs.

Its denotation is empty: the outer functional is the identity, and the least fixed point of the
identity on predicates is the empty predicate. -/
def counterexampleFormula : MuFormula Unit := .mu (.nu (.var 1))

/-- **Starting position of the regression play.** The game position consisting of the formula
$\mu X.\,\nu Y.\,X$, the unique world of the one-world model, and the empty binder stack. -/
def cePos0 : GamePosition Unit Unit :=
  ⟨.mu (.nu (.var 1)), Unit.unit, []⟩
/-- **Second position of the regression play.** The game position consisting of the formula
$\nu Y.\,X$, the unique world of the one-world model, and the binder stack
$[\mu X.\,\nu Y.\,X]$. Here $X$ is the de Bruijn variable $1$, which refers to the binder
$\mu X$ on the stack. -/
def cePos1 : GamePosition Unit Unit :=
  ⟨.nu (.var 1), Unit.unit, [.mu (.nu (.var 1))]⟩
/-- **Third position of the regression play.** The game position consisting of the variable $X$,
the unique world of the one-world model, and the binder stack $[\nu Y.\,X,\ \mu X.\,\nu Y.\,X]$,
listed innermost first. Here $X$ is the de Bruijn variable $1$, which refers to the outer binder
$\mu X$. -/
def cePos2 : GamePosition Unit Unit :=
  ⟨.var 1, Unit.unit, [.nu (.var 1), .mu (.nu (.var 1))]⟩

/-- **Step map of the regression play.** Let $\Phi = \mu X.\, \nu Y.\, X$ be the regression
formula over the one-element type of atoms, and write game positions over the one-element type
of worlds as (formula, world, stack of enclosing binders, innermost first). For every world $w$,
the step map sends $(\Phi, w, [\,])$ to $(\nu Y.\, X, w, [\Phi])$, sends
$(\nu Y.\, X, w, [\Phi])$ to $(X, w, [\nu Y.\, X, \Phi])$, and sends
$(X, w, [\nu Y.\, X, \Phi])$ to $(\Phi, w, [\,])$, where $X$ is the variable bound by the
outer $\mu$; every other game position is sent to itself. -/
def ceNext : GamePosition Unit Unit → GamePosition Unit Unit
  | ⟨.mu (.nu (.var 1)), w, []⟩ => ⟨.nu (.var 1), w, [.mu (.nu (.var 1))]⟩
  | ⟨.nu (.var 1), w, [.mu (.nu (.var 1))]⟩ =>
      ⟨.var 1, w, [.nu (.var 1), .mu (.nu (.var 1))]⟩
  | ⟨.var 1, w, [.nu (.var 1), .mu (.nu (.var 1))]⟩ =>
      ⟨.mu (.nu (.var 1)), w, []⟩
  | p => p

/-- **The regression play.** Write $\ast$ for the unique world, and consider the game positions
(formula, world, binder stack listed innermost first)
$P_0 = (\mu X.\,\nu Y.\,X,\ \ast,\ [\,])$, $P_1 = (\nu Y.\,X,\ \ast,\ [\mu X.\,\nu Y.\,X])$ and
$P_2 = (X,\ \ast,\ [\nu Y.\,X,\ \mu X.\,\nu Y.\,X])$. Let $s$ be the step map sending $P_0$ to
$P_1$, $P_1$ to $P_2$ and $P_2$ to $P_0$, and fixing every other position. The regression play is
the sequence of positions $p_0 = P_0$, $p_{n+1} = s(p_n)$, which cycles through $P_0, P_1, P_2$.

These are the successive positions of the model-checking game for $\mu X.\,\nu Y.\,X$ on the
one-world model. -/
def cePlay : ℕ → GamePosition Unit Unit
  | 0 => cePos0
  | n + 1 => ceNext (cePlay n)

/-- **Regression cycle, first step.** Let $\Phi = \mu X.\, \nu Y.\, X$ be the regression formula,
$\ast$ the unique world, and write game positions as (formula, world, stack of enclosing
binders, innermost first). The step map of the regression play sends the first cycle position
$(\Phi, \ast, [\,])$ to the second cycle position $(\nu Y.\, X, \ast, [\Phi])$. -/
theorem ceNext_cePos0 : ceNext cePos0 = cePos1 := rfl
/-- **Regression cycle, second step.** Let $\Phi = \mu X.\, \nu Y.\, X$ be the regression formula,
$\ast$ the unique world, and write game positions as (formula, world, stack of enclosing
binders, innermost first). The step map of the regression play sends the second cycle position
$(\nu Y.\, X, \ast, [\Phi])$ to the third cycle position $(X, \ast, [\nu Y.\, X, \Phi])$, where
$X$ is the variable bound by the outer $\mu$. -/
theorem ceNext_cePos1 : ceNext cePos1 = cePos2 := rfl
/-- **Regression cycle, third step.** Let $\Phi = \mu X.\, \nu Y.\, X$ be the regression formula,
$\ast$ the unique world, and write game positions as (formula, world, stack of enclosing
binders, innermost first). The step map of the regression play sends the third cycle position
$(X, \ast, [\nu Y.\, X, \Phi])$, where $X$ is the variable bound by the outer $\mu$, back to
the first cycle position $(\Phi, \ast, [\,])$. -/
theorem ceNext_cePos2 : ceNext cePos2 = cePos0 := rfl

/-- **The regression play stays on the cycle.** For every $n \in \mathbb{N}$, the position at
step $n$ of the regression play is the first, the second or the third cycle position. -/
theorem cePlay_mem (n : ℕ) :
    cePlay n = cePos0 ∨ cePlay n = cePos1 ∨ cePlay n = cePos2 := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
      show ceNext (cePlay n) = cePos0 ∨ ceNext (cePlay n) = cePos1 ∨
        ceNext (cePlay n) = cePos2
      rcases ih with h | h | h <;> rw [h]
      · exact Or.inr (Or.inl ceNext_cePos0)
      · exact Or.inr (Or.inr ceNext_cePos1)
      · exact Or.inl ceNext_cePos2

/-- **The regression play has period three.** Number the positions of the regression play
from $0$. For every natural number $n$, its position number $n + 3$ equals its position
number $n$. -/
theorem cePlay_period (n : ℕ) : cePlay (n + 3) = cePlay n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show ceNext (cePlay (n + 3)) = ceNext (cePlay n)
      rw [ih]

/-- **The regression play returns to its start every three steps.** Number the positions of
the regression play of $\mu X.\,\nu Y.\,X$ from $0$. For every natural number $k$, its
position number $3k$ is its starting position: the formula $\mu X.\,\nu Y.\,X$ at the unique
world, with the empty binder stack. -/
theorem cePlay_mul_three (k : ℕ) : cePlay (3 * k) = cePos0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h : 3 * (k + 1) = 3 * k + 3 := by omega
      rw [h, cePlay_period, ih]

/-- **The regression play is a play.** For every $n \in \mathbb{N}$, in the model-checking game
on the one-world regression model there is a move from the position at step $n$ of the
regression play to the position at step $n + 1$. -/
theorem cePlay_moves (n : ℕ) :
    Move counterexampleModel (cePlay n) (cePlay (n + 1)) := by
  have hsucc : cePlay (n + 1) = ceNext (cePlay n) := rfl
  rw [hsucc]
  rcases cePlay_mem n with h | h | h <;> rw [h]
  · exact Move.mu
  · exact Move.nu
  · exact Move.var (by decide)

/-- **Priority of the outer binder in the regression play.** The starting position of the
regression play, consisting of the formula $\mu X.\,\nu Y.\,X$, the unique world and the empty
binder stack, has priority $1$: a $\mu$-binder position with $k$ binders on the stack has
priority $2k + 1$, and here $k = 0$.

Under fixed priorities ($\mu \mapsto 1$, $\nu \mapsto 2$) the greatest priority recurring on this
play would be $2$ (even, Verifier wins); with priorities increasing with nesting depth (the inner
$\nu$ here has priority $4$) and the least-priority rule, the least binder priority recurring on
this play is $1$ (odd, Refuter wins). -/
theorem ce_prio0 : prio (cePos0 : GamePosition Unit Unit) = some 1 := rfl
/-- **Priority of the inner binder in the regression play.** The second position of the
regression play, consisting of the formula $\nu Y.\,X$, the unique world and the binder stack
$[\mu X.\,\nu Y.\,X]$, has priority $4$: a $\nu$-binder position with $k$ binders on the stack
has priority $2k + 2$, and here $k = 1$. -/
theorem ce_prio1 : prio (cePos1 : GamePosition Unit Unit) = some 4 := rfl

/-- **Verifier loses the infinite play of $\mu X.\, \nu Y.\, X$.** Consider the infinite
sequence of positions of the model-checking game for $\mu X.\, \nu Y.\, X$ (with one-element
types of worlds and atoms) that starts at this formula with empty binder stack and repeats three
steps: unfold $\mu X$, unfold $\nu Y$, and follow the variable $X$ back to the formula with empty
stack. This play does not satisfy the parity condition: it is not the case that the least binder
priority occurring infinitely often is even. -/
theorem counterexample_parityWin_false : ¬ ParityWin cePlay := by
  rintro ⟨e, heven, hfreq, hmin⟩
  obtain ⟨n, -, hEq⟩ := hfreq 0
  rcases cePlay_mem n with h | h | h
  · rw [h, ce_prio0] at hEq
    have he1 : (1 : ℕ) = e := Option.some.inj hEq
    rw [← he1] at heven
    exact (by rintro ⟨r, hr⟩; omega : ¬ Even (1 : ℕ)) heven
  · rw [h, ce_prio1] at hEq
    have he4 : (4 : ℕ) = e := Option.some.inj hEq
    rw [← he4] at hmin
    obtain ⟨N, hN⟩ := hmin 1 (by omega)
    have hge : N ≤ 3 * (N + 1) := by omega
    have hplay : cePlay (3 * (N + 1)) = cePos0 := cePlay_mul_three (N + 1)
    exact hN _ hge (by rw [hplay, ce_prio0])
  · have hnone : prio (cePos2 : GamePosition Unit Unit) = none := rfl
    rw [h, hnone] at hEq
    cases hEq

/-- **$\mu X.\, \nu Y.\, X$ is false in the one-world model.** In the Kripke model with a single
world, which is related to itself, and a single atom, which is false there, under the environment
that assigns the empty set to every variable, the formula $\mu X.\, \nu Y.\, X$ is not satisfied
at the unique world.

This agrees with the model-checking game, where Verifier loses the play of this formula. -/
theorem counterexample_sat_false :
    ¬ sat counterexampleModel (fun _ => fun _ => False)
      counterexampleFormula Unit.unit := by
  intro h
  have hpre : sat counterexampleModel
      (extendEnv (fun _ => fun _ => False) (fun _ => False)) (.nu (.var 1)) ≤
        fun _ => False := by
    intro v hv
    obtain ⟨S', hS', hvS'⟩ :=
      (sat_nu counterexampleModel _ _ _).mp hv
    exact hS' v hvS'
  exact h _ hpre

/-! ### The fixpoint-free fragment -/

/-- **Fixpoint-free formulas.** The fixpoint-free formulas over a type of atoms are built from
atoms $p$, negated atoms $\neg p$, $\bot$ and $\top$ by conjunction $\varphi \land \psi$,
disjunction $\varphi \lor \psi$, necessity $\Box\varphi$ and possibility $\Diamond\varphi$.

These are the formulas of basic modal logic in negation normal form: the μ-calculus formulas with
no fixpoint operators and no variables. -/
inductive FixFreeFormula (Atom : Type u) : Type u where
  /-- An atom. -/
  | atom : Atom → FixFreeFormula Atom
  /-- A negated atom. -/
  | natom : Atom → FixFreeFormula Atom
  /-- Falsity. -/
  | bot : FixFreeFormula Atom
  /-- Truth. -/
  | top : FixFreeFormula Atom
  /-- Conjunction. -/
  | and : FixFreeFormula Atom → FixFreeFormula Atom → FixFreeFormula Atom
  /-- Disjunction. -/
  | or : FixFreeFormula Atom → FixFreeFormula Atom → FixFreeFormula Atom
  /-- Necessity. -/
  | box : FixFreeFormula Atom → FixFreeFormula Atom
  /-- Possibility. -/
  | dia : FixFreeFormula Atom → FixFreeFormula Atom

namespace FixFreeFormula

/-- **Embedding of the fixpoint-free fragment into the μ-calculus.** The map from fixpoint-free
formulas to μ-calculus formulas defined by recursion: atoms, negated atoms, $\bot$ and $\top$
go to the same atom, negated atom, $\bot$ and $\top$, and $\varphi \wedge \psi$,
$\varphi \vee \psi$, $\Box \varphi$ and $\Diamond \varphi$ go to the conjunction, disjunction,
box and diamond of the images of $\varphi$ and $\psi$. -/
def toMu : FixFreeFormula Atom → MuFormula Atom
  | .atom a => .atom a
  | .natom a => .natom a
  | .bot => .bot
  | .top => .top
  | .and φ ψ => .and (toMu φ) (toMu ψ)
  | .or φ ψ => .or (toMu φ) (toMu ψ)
  | .box φ => .box (toMu φ)
  | .dia φ => .dia (toMu φ)

end FixFreeFormula

/-- **Backward-induction winning region of the fixpoint-free fragment.** Let $M$ be a Kripke
model with accessibility relation $R$. For a fixpoint-free formula $\varphi$ and a world $w$,
"$\varphi$ is winning at $w$" is defined by recursion on $\varphi$: an atom $a$ is winning at
$w$ iff $a$ is true at $w$ in $M$; a negated atom $\lnot a$ iff $a$ is not true at $w$; $\bot$
is never winning and $\top$ is always winning; $\varphi \land \psi$ is winning at $w$ iff both
$\varphi$ and $\psi$ are; $\varphi \lor \psi$ iff $\varphi$ or $\psi$ is; $\Box \varphi$ iff
$\varphi$ is winning at every $v$ with $w \mathrel{R} v$; and $\Diamond \varphi$ iff $\varphi$
is winning at some $v$ with $w \mathrel{R} v$.

Verifier has a winning strategy in the model-checking game from the position $(\varphi, w, [])$
with empty stack exactly when $\varphi$ is winning at $w$. -/
def Wins (M : KripkeModel World Atom) : FixFreeFormula Atom → World → Prop
  | .atom a, w => M.valuation w a
  | .natom a, w => ¬ M.valuation w a
  | .bot, _ => False
  | .top, _ => True
  | .and φ ψ, w => Wins M φ w ∧ Wins M ψ w
  | .or φ ψ, w => Wins M φ w ∨ Wins M ψ w
  | .box φ, w => ∀ v, M.rel w v → Wins M φ v
  | .dia φ, w => ∃ v, M.rel w v ∧ Wins M φ v

/-- **Backward-induction winning equals satisfaction on the fixpoint-free fragment.** For every
Kripke model $M$, environment $\mathit{env}$, fixpoint-free formula $\varphi$ and world $w$, $w$
lies in the backward-induction winning region of $\varphi$ if and only if $w$ satisfies the
μ-calculus embedding of $\varphi$ in $M$ under $\mathit{env}$.

Source: C. Stirling, *Modal and Temporal Properties of Processes*, Springer 2001, Chapter 6. -/
theorem wins_iff_sat (M : KripkeModel World Atom) (env : ℕ → World → Prop)
    (φ : FixFreeFormula Atom) (w : World) :
    Wins M φ w ↔ sat M env (FixFreeFormula.toMu φ) w := by
  induction φ generalizing w with
  | atom a => exact Iff.rfl
  | natom a => exact Iff.rfl
  | bot => exact Iff.rfl
  | top => exact Iff.rfl
  | and φ ψ ihφ ihψ =>
    simp only [Wins, FixFreeFormula.toMu, sat_and]
    exact and_congr (ihφ w) (ihψ w)
  | or φ ψ ihφ ihψ =>
    simp only [Wins, FixFreeFormula.toMu, sat_or]
    exact or_congr (ihφ w) (ihψ w)
  | box φ ih =>
    simp only [Wins, FixFreeFormula.toMu, sat_box]
    exact forall_congr' fun v => imp_congr_right fun _ => ih v
  | dia φ ih =>
    simp only [Wins, FixFreeFormula.toMu, sat_dia]
    exact exists_congr fun v => and_congr Iff.rfl (ih v)

/-! ### The Wins-guided strategy -/

/-- **Size of a μ-calculus formula.** The size $|\varphi|$ of a μ-calculus formula $\varphi$ is
the number of nodes of its syntax tree: an atom, a negated atom, a variable, $\bot$ and $\top$
have size $1$; $|\varphi \wedge \psi| = |\varphi \vee \psi| = |\varphi| + |\psi| + 1$; and
$|\Box\varphi| = |\Diamond\varphi| = |\mu\varphi| = |\nu\varphi| = |\varphi| + 1$. -/
def MuFormula.size : MuFormula Atom → ℕ
  | .atom _ | .natom _ | .var _ | .bot | .top => 1
  | .and φ ψ | .or φ ψ => MuFormula.size φ + MuFormula.size ψ + 1
  | .box φ | .dia φ | .mu φ | .nu φ => MuFormula.size φ + 1

/-- **Partial inverse of the fixpoint-free embedding.** The partial map from μ-calculus formulas
to fixpoint-free formulas defined by recursion: an atom, a negated atom, $\bot$ and $\top$ are
sent to the same formula; a conjunction or disjunction is sent to the conjunction or
disjunction of the values at its two parts, and $\Box\psi$, $\Diamond\psi$ to the box or diamond
of the value at $\psi$, whenever those values are defined; the map is undefined at variables
and at least and greatest fixpoints, and at every formula with a part where it is undefined.

It inverts the embedding of fixpoint-free formulas into μ-calculus formulas on its image. -/
def toMuInv : MuFormula Atom → Option (FixFreeFormula Atom)
  | .atom a => some (.atom a)
  | .natom a => some (.natom a)
  | .bot => some .bot
  | .top => some .top
  | .and φ ψ => (toMuInv φ).bind fun φ' => (toMuInv ψ).map (FixFreeFormula.and φ')
  | .or φ ψ => (toMuInv φ).bind fun φ' => (toMuInv ψ).map (FixFreeFormula.or φ')
  | .box φ => (toMuInv φ).map FixFreeFormula.box
  | .dia φ => (toMuInv φ).map FixFreeFormula.dia
  | _ => none

/-- **The partial inverse recovers fixpoint-free formulas.** For every fixpoint-free formula
$\varphi$, the partial inverse of the embedding of fixpoint-free formulas into μ-calculus
formulas is defined at the image of $\varphi$ under the embedding, with value $\varphi$. -/
theorem toMuInv_toMu (φ : FixFreeFormula Atom) :
    toMuInv (FixFreeFormula.toMu φ) = some φ := by
  induction φ with
  | atom a => rfl
  | natom a => rfl
  | bot => rfl
  | top => rfl
  | and φ ψ ihφ ihψ => simp [toMuInv, FixFreeFormula.toMu, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp [toMuInv, FixFreeFormula.toMu, ihφ, ihψ]
  | box φ ih => simp [toMuInv, FixFreeFormula.toMu, ih]
  | dia φ ih => simp [toMuInv, FixFreeFormula.toMu, ih]

/-- **The embedding inverts the partial inverse.** For every μ-calculus formula $\psi$ and every
fixpoint-free formula $\varphi$: if the partial inverse of the embedding of fixpoint-free
formulas into μ-calculus formulas is defined at $\psi$ with value $\varphi$, then the embedding
sends $\varphi$ to $\psi$. -/
theorem toMu_toMuInv {φ : FixFreeFormula Atom} {ψ : MuFormula Atom}
    (h : toMuInv ψ = some φ) : FixFreeFormula.toMu φ = ψ := by
  induction ψ generalizing φ with
  | atom b =>
      simp only [toMuInv, Option.some.injEq] at h
      subst h
      rfl
  | natom b =>
      simp only [toMuInv, Option.some.injEq] at h
      subst h
      rfl
  | bot =>
      simp only [toMuInv, Option.some.injEq] at h
      subst h
      rfl
  | top =>
      simp only [toMuInv, Option.some.injEq] at h
      subst h
      rfl
  | var _ => simp [toMuInv] at h
  | mu _ => simp [toMuInv] at h
  | nu _ => simp [toMuInv] at h
  | and ψ₁ ψ₂ ih₁ ih₂ =>
      simp only [toMuInv] at h
      cases h₁ : toMuInv ψ₁ with
      | none => simp [h₁] at h
      | some φ₁ =>
          cases h₂ : toMuInv ψ₂ with
          | none => simp [h₁, h₂] at h
          | some φ₂ =>
              rw [h₁, h₂] at h
              have hinj : (φ₁.and φ₂ : FixFreeFormula Atom) = φ := Option.some.inj h
              subst hinj
              simp only [FixFreeFormula.toMu, ih₁ h₁, ih₂ h₂]
  | or ψ₁ ψ₂ ih₁ ih₂ =>
      simp only [toMuInv] at h
      cases h₁ : toMuInv ψ₁ with
      | none => simp [h₁] at h
      | some φ₁ =>
          cases h₂ : toMuInv ψ₂ with
          | none => simp [h₁, h₂] at h
          | some φ₂ =>
              rw [h₁, h₂] at h
              have hinj : (φ₁.or φ₂ : FixFreeFormula Atom) = φ := Option.some.inj h
              subst hinj
              simp only [FixFreeFormula.toMu, ih₁ h₁, ih₂ h₂]
  | box ψ' ih =>
      simp only [toMuInv] at h
      cases h' : toMuInv ψ' with
      | none => simp [h'] at h
      | some φ' =>
          rw [h'] at h
          have hinj : (φ'.box : FixFreeFormula Atom) = φ := Option.some.inj h
          subst hinj
          simp only [FixFreeFormula.toMu, ih h']

  | dia ψ' ih =>
      simp only [toMuInv] at h
      cases h' : toMuInv ψ' with
      | none => simp [h'] at h
      | some φ' =>
          rw [h'] at h
          have hinj : (φ'.dia : FixFreeFormula Atom) = φ := Option.some.inj h
          subst hinj
          simp only [FixFreeFormula.toMu, ih h']

/-- **The fixpoint-free embedding is injective.** The embedding of fixpoint-free formulas into
μ-calculus formulas is injective: distinct fixpoint-free formulas have distinct images.

This is what lets the canonical fragment game recover a fragment formula from an
embedded game position. -/
theorem FixFreeFormula.toMu_injective :
    Function.Injective (FixFreeFormula.toMu (Atom := Atom)) := by
  intro φ ψ h
  have h1 := congrArg toMuInv h
  rw [toMuInv_toMu, toMuInv_toMu] at h1
  exact Option.some.inj h1

open Classical in
/-- **Wins-guided move.** Let $M$ be a Kripke model, and identify each fixpoint-free formula with
its embedding into the μ-calculus. For a μ-calculus formula $\psi$, a world $w$ and a stack $s$
of fixpoint binders, the Wins-guided move at the game position $(\psi, w, s)$ is the following
position. If $s$ is empty and $\psi$ is a fixpoint-free disjunction $\psi_1 \lor \psi_2$, it is
$(\psi_1, w, [])$ when $\psi_1$ is winning at $w$ (in the backward-induction winning region of
the fixpoint-free fragment) and $(\psi_2, w, [])$ otherwise. If $s$ is empty and $\psi$ is a
fixpoint-free formula $\Diamond \psi_1$, it is $(\psi_1, v, [])$ for a chosen successor $v$ of
$w$ at which $\psi_1$ is winning, if one exists; otherwise $(\psi_1, v, [])$ for a chosen
successor $v$ of $w$, if one exists; otherwise $(\psi, w, [])$. In every other case: at a
disjunction $\varphi_1 \lor \varphi_2$ it is $(\varphi_1, w, s)$; at $\Diamond \varphi_1$ it is
$(\varphi_1, v, s)$ for a chosen successor $v$ of $w$ if one exists, and $(\psi, w, s)$
otherwise; at $\nu \varphi_1$ it is $(\varphi_1, w, s')$, where $s'$ is $s$ with
$\nu \varphi_1$ pushed on top; and at every remaining formula (the positions owned by Refuter)
it is $(\psi, w, s)$.

Only the left disjunct is tested: if a fixpoint-free disjunction is winning at $w$ and its left
disjunct is not, then its right disjunct is.

Source: C. Stirling, *Modal and Temporal Properties of Processes*, Springer 2001,
Chapter 6. -/
noncomputable def winsMove (M : KripkeModel World Atom) (ψ : MuFormula Atom) (w : World)
    (st : List (MuFormula Atom)) : GamePosition Atom World :=
  match ψ, st with
  | .or φ₁ φ₂, [] =>
      match toMuInv (.or φ₁ φ₂) with
      | some (.or ψ₁ ψ₂) =>
          if _ : Wins M ψ₁ w then
            (⟨FixFreeFormula.toMu ψ₁, w, []⟩ : GamePosition Atom World)
          else (⟨FixFreeFormula.toMu ψ₂, w, []⟩ : GamePosition Atom World)
      | _ => (⟨φ₁, w, []⟩ : GamePosition Atom World)
  | .dia φ₁, [] =>
      match toMuInv (.dia φ₁) with
      | some (.dia ψ₁) =>
          if h : ∃ v, M.rel w v ∧ Wins M ψ₁ v then
            (⟨FixFreeFormula.toMu ψ₁, Classical.choose h, []⟩ : GamePosition Atom World)
          else if hsucc : ∃ v, M.rel w v then
            (⟨φ₁, Classical.choose hsucc, []⟩ : GamePosition Atom World)
          else (⟨.dia φ₁, w, []⟩ : GamePosition Atom World)
      | _ =>
          if h : ∃ v, M.rel w v then
            (⟨φ₁, Classical.choose h, []⟩ : GamePosition Atom World)
          else (⟨.dia φ₁, w, []⟩ : GamePosition Atom World)
  | .or φ₁ _, st => (⟨φ₁, w, st⟩ : GamePosition Atom World)
  | .dia φ₁, st =>
      if h : ∃ v, M.rel w v then
        (⟨φ₁, Classical.choose h, st⟩ : GamePosition Atom World)
      else (⟨.dia φ₁, w, st⟩ : GamePosition Atom World)
  | .nu φ₁, st => (⟨φ₁, w, .nu φ₁ :: st⟩ : GamePosition Atom World)
  | _, _ => (⟨ψ, w, st⟩ : GamePosition Atom World)

/-- **The Wins-guided move at a disjunction.** Let $M$ be a Kripke model, $\varphi_1$ and
$\varphi_2$ fixpoint-free formulas and $w$ a world in the backward-induction winning region of
$\varphi_1 \vee \varphi_2$. Then for some $i \in \{1, 2\}$, $w$ lies in the backward-induction
winning region of $\varphi_i$ and the Wins-guided move at the position made of the embedding of
$\varphi_1 \vee \varphi_2$, the world $w$ and the empty binder stack is the position made of the
embedding of $\varphi_i$, the world $w$ and the empty stack. -/
theorem winsMove_or {M : KripkeModel World Atom} {φ₁ φ₂ : FixFreeFormula Atom} {w : World}
    (hW : Wins M (.or φ₁ φ₂) w) :
    (winsMove M (FixFreeFormula.toMu (.or φ₁ φ₂)) w [] =
        ⟨FixFreeFormula.toMu φ₁, w, []⟩ ∧ Wins M φ₁ w) ∨
    (winsMove M (FixFreeFormula.toMu (.or φ₁ φ₂)) w [] =
        ⟨FixFreeFormula.toMu φ₂, w, []⟩ ∧ Wins M φ₂ w) := by
  have hInv : toMuInv (MuFormula.or (FixFreeFormula.toMu φ₁) (FixFreeFormula.toMu φ₂)) =
      some (.or φ₁ φ₂) := toMuInv_toMu (.or φ₁ φ₂)
  simp only [FixFreeFormula.toMu, winsMove, hInv]
  by_cases h₁ : Wins M φ₁ w
  · rw [dite_eq_left h₁]
    exact Or.inl ⟨rfl, h₁⟩
  · rw [dite_eq_right h₁]
    cases hW with
    | inl h => exact absurd h h₁
    | inr h₂ => exact Or.inr ⟨rfl, h₂⟩

/-- **The Wins-guided move at a diamond.** Let $M$ be a Kripke model, $\varphi$ a fixpoint-free
formula and $w$ a world in the backward-induction winning region of $\Diamond \varphi$. Then
there is a successor $v$ of $w$ in $M$ lying in the backward-induction winning region of
$\varphi$ such that the Wins-guided move at the position made of the embedding of
$\Diamond \varphi$, the world $w$ and the empty binder stack is the position made of the
embedding of $\varphi$, the world $v$ and the empty stack. -/
theorem winsMove_dia {M : KripkeModel World Atom} {φ₁ : FixFreeFormula Atom} {w : World}
    (hW : Wins M (.dia φ₁) w) :
    ∃ v, winsMove M (FixFreeFormula.toMu (.dia φ₁)) w [] =
        ⟨FixFreeFormula.toMu φ₁, v, []⟩ ∧ M.rel w v ∧ Wins M φ₁ v := by
  have hex : ∃ v, M.rel w v ∧ Wins M φ₁ v := hW
  refine ⟨Classical.choose hex, ?_, (Classical.choose_spec hex).1,
    (Classical.choose_spec hex).2⟩
  have hInv : toMuInv (MuFormula.dia (FixFreeFormula.toMu φ₁)) =
      some (.dia φ₁) := toMuInv_toMu (.dia φ₁)
  simp only [FixFreeFormula.toMu, winsMove, hInv]
  rw [dite_eq_left hex]

/-- **The Wins-guided move is legal.** For a Kripke model $M$ and a game position $p$ owned by
Verifier from which some move exists, the Wins-guided move at $p$ is a legal move of the
model-checking game on $M$ from $p$. -/
theorem winsMove_isMove (M : KripkeModel World Atom) (p : GamePosition Atom World)
    (hOwn : Owner p = true) (hExists : ∃ q, Move M p q) :
    Move M p (winsMove M p.1 p.2.1 p.2.2) := by
  obtain ⟨ψ, w, st⟩ := p
  cases ψ with
  | or φ₁ φ₂ =>
      cases st with
      | nil =>
          cases h : toMuInv (.or φ₁ φ₂) with
          | none =>
              simp only [winsMove, h]
              exact Move.orLeft
          | some φ' =>
              cases φ' with
              | or ψ₁ ψ₂ =>
                  have htoMu := toMu_toMuInv (φ := .or ψ₁ ψ₂) h
                  simp only [FixFreeFormula.toMu] at htoMu
                  obtain ⟨rfl, rfl⟩ := MuFormula.or.inj htoMu
                  simp only [winsMove, h]
                  by_cases h₁ : Wins M ψ₁ w
                  · rw [dite_eq_left h₁]
                    exact Move.orLeft
                  · rw [dite_eq_right h₁]
                    exact Move.orRight
              | _ =>
                  simp only [winsMove, h]
                  exact Move.orLeft
      | cons _ _ =>
          simp only [winsMove]
          exact Move.orLeft
  | dia φ₁ =>
      cases st with
      | nil =>
          cases h : toMuInv (.dia φ₁) with
          | none =>
              simp only [winsMove, h]
              by_cases hsucc : ∃ v, M.rel w v
              · rw [dite_eq_left hsucc]
                exact Move.dia (Classical.choose_spec hsucc)
              · rw [dite_eq_right hsucc]
                obtain ⟨q, hq⟩ := hExists
                cases hq with
                | dia hv => exact absurd ⟨_, hv⟩ hsucc
          | some φ' =>
              cases φ' with
              | dia ψ₁ =>
                  have htoMu := toMu_toMuInv (φ := .dia ψ₁) h
                  simp only [FixFreeFormula.toMu] at htoMu
                  obtain rfl := MuFormula.dia.inj htoMu
                  simp only [winsMove, h]
                  by_cases hex : ∃ v, M.rel w v ∧ Wins M ψ₁ v
                  · rw [dite_eq_left hex]
                    exact Move.dia (Classical.choose_spec hex).1
                  · rw [dite_eq_right hex]
                    by_cases hsucc : ∃ v, M.rel w v
                    · rw [dite_eq_left hsucc]
                      exact Move.dia (Classical.choose_spec hsucc)
                    · rw [dite_eq_right hsucc]
                      obtain ⟨q, hq⟩ := hExists
                      cases hq with
                      | dia hv => exact absurd ⟨_, hv⟩ hsucc
              | _ =>
                  simp only [winsMove, h]
                  by_cases hsucc : ∃ v, M.rel w v
                  · rw [dite_eq_left hsucc]
                    exact Move.dia (Classical.choose_spec hsucc)
                  · rw [dite_eq_right hsucc]
                    obtain ⟨q, hq⟩ := hExists
                    cases hq with
                    | dia hv => exact absurd ⟨_, hv⟩ hsucc
      | cons _ _ =>
          simp only [winsMove]
          by_cases hsucc : ∃ v, M.rel w v
          · rw [dite_eq_left hsucc]
            exact Move.dia (Classical.choose_spec hsucc)
          · rw [dite_eq_right hsucc]
            obtain ⟨q, hq⟩ := hExists
            cases hq with
            | dia hv => exact absurd ⟨_, hv⟩ hsucc
  | nu φ₁ =>
      simp only [winsMove]
      exact Move.nu
  | atom _ | natom _ | var _ | bot | top | and _ _ | box _ | mu _ =>
      simp [Owner] at hOwn

/-- **Wins-guided strategy.** For a Kripke model $M$, the Wins-guided strategy is the Verifier
strategy of the model-checking game on $M$ that chooses, at each game position $(\psi, w, s)$,
the Wins-guided move at $(\psi, w, s)$. At every Verifier-owned position that has a move, this
choice is a legal move. -/
noncomputable def winsStrategy (M : KripkeModel World Atom) : Strategy M where
  choose p := winsMove M p.1 p.2.1 p.2.2
  choose_move p hOwn hExists := winsMove_isMove M p hOwn hExists

/-! ### Play lemmas -/

/-- **Finite plays are nonempty.** Let $M$ be a Kripke model, $\sigma$ a Verifier strategy and
$p$ a game position. Every finite play from $p$ consistent with $\sigma$ is a nonempty list of
positions. -/
theorem PlayFrom.ne_nil {M : KripkeModel World Atom} {σ : Strategy M}
    {p : GamePosition Atom World} {ps : List (GamePosition Atom World)}
    (h : PlayFrom M σ p ps) : ps ≠ [] := by
  cases h with
  | single => simp
  | cons => simp

/-- **Prepending to a nonempty play keeps the last position.** For a game position $p$ and a
nonempty list $ps$ of game positions, the list obtained by prepending $p$ to $ps$ has the same
last position as $ps$. -/
theorem playLast_cons {p : GamePosition Atom World} {ps : List (GamePosition Atom World)}
    (hne : ps ≠ []) : playLast (p :: ps) = playLast ps := by
  cases ps with
  | nil => exact absurd rfl hne
  | cons _ _ => rfl

/-- **Fragment moves decrease the formula size.** Let $M$ be a Kripke model, $\varphi$ a
fixpoint-free formula and $w$ a world. Every move of the model-checking game in $M$ from the
position $(\varphi, w, [\,])$, with $\varphi$ embedded in the μ-calculus and the empty stack, leads
to a position $(\varphi', w', [\,])$ for some fixpoint-free formula $\varphi'$ and world $w'$,
and the size of $\varphi'$ is strictly smaller than the size of $\varphi$ (sizes of the embedded
μ-calculus formulas). -/
theorem move_of_toMu {M : KripkeModel World Atom} {φ : FixFreeFormula Atom} {w : World}
    {q : GamePosition Atom World} (h : Move M ⟨FixFreeFormula.toMu φ, w, []⟩ q) :
    ∃ φ' : FixFreeFormula Atom, ∃ w' : World, q = ⟨FixFreeFormula.toMu φ', w', []⟩ ∧
      MuFormula.size (FixFreeFormula.toMu φ') < MuFormula.size (FixFreeFormula.toMu φ) := by
  cases φ with
  | atom a => cases h
  | natom a => cases h
  | bot => cases h
  | top => cases h
  | and φ ψ =>
      simp only [FixFreeFormula.toMu] at h
      cases h with
      | andLeft => exact ⟨φ, w, rfl, by simp only [FixFreeFormula.toMu, MuFormula.size]; omega⟩
      | andRight => exact ⟨ψ, w, rfl, by simp only [FixFreeFormula.toMu, MuFormula.size]; omega⟩
  | or φ ψ =>
      simp only [FixFreeFormula.toMu] at h
      cases h with
      | orLeft => exact ⟨φ, w, rfl, by simp only [FixFreeFormula.toMu, MuFormula.size]; omega⟩
      | orRight => exact ⟨ψ, w, rfl, by simp only [FixFreeFormula.toMu, MuFormula.size]; omega⟩
  | box φ =>
      simp only [FixFreeFormula.toMu] at h
      cases h with
      | box hrel => exact ⟨φ, _, rfl, by simp only [FixFreeFormula.toMu, MuFormula.size]; omega⟩
  | dia φ =>
      simp only [FixFreeFormula.toMu] at h
      cases h with
      | dia hrel => exact ⟨φ, _, rfl, by simp only [FixFreeFormula.toMu, MuFormula.size]; omega⟩

/-- **No infinite play from a fragment position.** Let $M$ be a Kripke model, $\varphi$ a
fixpoint-free formula and $w$ a world. There is no sequence of game positions
$p_0, p_1, p_2, \dots$ with $p_0 = (\varphi, w, [\,])$ (the embedded formula with the empty
stack) such that each step from $p_n$ to $p_{n+1}$ is a move of the model-checking game in $M$.
The reason is that every move strictly decreases the formula size. -/
theorem no_infinite_play_of_fixFree {M : KripkeModel World Atom} {φ : FixFreeFormula Atom}
    {w : World} {play : ℕ → GamePosition Atom World}
    (h0 : play 0 = ⟨FixFreeFormula.toMu φ, w, []⟩)
    (hsteps : ∀ n, Move M (play n) (play (n + 1))) : False := by
  have key : ∀ n, ∃ φ' : FixFreeFormula Atom, ∃ w' : World,
      play n = ⟨FixFreeFormula.toMu φ', w', []⟩ ∧
        MuFormula.size (FixFreeFormula.toMu φ') + n ≤
          MuFormula.size (FixFreeFormula.toMu φ) := by
    intro n
    induction n with
    | zero => exact ⟨φ, w, h0, by simp⟩
    | succ n ih =>
        obtain ⟨φ', w', hplay, hsize⟩ := ih
        have hstep : Move M ⟨FixFreeFormula.toMu φ', w', []⟩ (play (n + 1)) := by
          have h := hsteps n
          rw [hplay] at h
          exact h
        obtain ⟨φ'', w'', hq, hlt⟩ := move_of_toMu hstep
        exact ⟨φ'', w'', hq, by omega⟩
  obtain ⟨φ', w', hplay, hsize⟩ := key (MuFormula.size (FixFreeFormula.toMu φ) + 1)
  omega

/-- **Winning strategies stay winning along consistent moves.** Let $M$ be a Kripke model,
$\mathit{env}$ an environment and $\sigma$ a Verifier strategy for the model-checking game on
$M$. If $\sigma$ wins from a position $p$ in $\mathit{env}$, and $q$ is a position reachable from
$p$ by one move that is the position chosen by $\sigma$ at $p$ whenever Verifier owns $p$, then
$\sigma$ also wins from $q$ in $\mathit{env}$. -/
theorem strategyWins_of_move {M : KripkeModel World Atom} {env : ℕ → World → Prop}
    {σ : Strategy M} {p q : GamePosition Atom World} (hW : StrategyWins M env σ p)
    (hmove : Move M p q) (hσ : Owner p = true → q = σ.choose p) :
    StrategyWins M env σ q := by
  obtain ⟨hfin, hinf⟩ := hW
  refine ⟨fun ps hplay hcomplete => ?_, fun play h0 hsteps => ?_⟩
  · have hplay' : PlayFrom M σ p (p :: ps) := PlayFrom.cons hmove hσ hplay
    have hcomplete' : ∃ r, playLast (p :: ps) = some r ∧ NoMoves M r := by
      obtain ⟨r, hlast, hno⟩ := hcomplete
      exact ⟨r, by rw [playLast_cons hplay.ne_nil]; exact hlast, hno⟩
    obtain ⟨r, hlast', hterm⟩ := hfin _ hplay' hcomplete'
    refine ⟨r, ?_, hterm⟩
    rw [playLast_cons hplay.ne_nil] at hlast'
    exact hlast'
  · obtain ⟨e, heven, hfreq, hev⟩ :=
      -- The prepended play's first step lands at `play 0`, which is `q` by `h0`.
      have hmove' : Move M p (play 0) := by rw [h0]; exact hmove
      have hσ' : Owner p = true → play 0 = σ.choose p := by rw [h0]; exact hσ
      hinf (fun n => match n with | 0 => p | n + 1 => play n) rfl
        (fun n => match n with
          | 0 => ⟨hmove', hσ'⟩
          | n + 1 => hsteps n)
    refine ⟨e, heven, ?_, ?_⟩
    · intro N
      obtain ⟨n, hn, hpri⟩ := hfreq (N + 1)
      refine ⟨n - 1, by omega, ?_⟩
      cases n with
      | zero => omega
      | succ m =>
          have : (fun n => match n with | 0 => p | n + 1 => play n) (m + 1) = play m := rfl
          rwa [this] at hpri
    · intro e' he'
      obtain ⟨N, hN⟩ := hev e' he'
      refine ⟨N, fun n hn => ?_⟩
      have h2 := hN (n + 1) (by omega)
      have : (fun n => match n with | 0 => p | n + 1 => play n) (n + 1) = play n := rfl
      rwa [this] at h2

/-- The Wins-guided strategy wins every complete finite play from a winning
fragment position. -/
theorem winsStrategy_wins_finite_aux (M : KripkeModel World Atom)
    {env : ℕ → World → Prop} {p : GamePosition Atom World}
    {ps : List (GamePosition Atom World)}
    (hplay : PlayFrom M (winsStrategy M) p ps) :
    (∀ (φ : FixFreeFormula Atom) (w : World), p = ⟨FixFreeFormula.toMu φ, w, []⟩ →
      Wins M φ w → (∃ q, playLast ps = some q ∧ NoMoves M q) →
        ∃ q, playLast ps = some q ∧ TerminalWin M env q) := by
  induction hplay with
  | single =>
      intro φ w hp hW hcomplete
      subst hp
      obtain ⟨q, hlast, hNoMoves⟩ := hcomplete
      simp only [playLast, List.getLast?_singleton] at hlast
      obtain rfl := Option.some.inj hlast
      refine ⟨⟨FixFreeFormula.toMu φ, w, []⟩, rfl, ?_⟩
      cases φ with
      | atom a => exact hW
      | natom a => exact hW
      | bot => exact hW.elim
      | top => trivial
      | and _ _ => exact absurd Move.andLeft (hNoMoves _)
      | or _ _ => exact absurd Move.orLeft (hNoMoves _)
      | box _ => trivial
      | dia φ' =>
          obtain ⟨v, hv, _⟩ := hW
          exact absurd (Move.dia hv) (hNoMoves _)
  | @cons p q ps h hσ hps ih =>
      intro φ w hp hW hcomplete
      subst hp
      obtain ⟨φ', w', hq, hW'⟩ : ∃ φ' : FixFreeFormula Atom, ∃ w' : World,
          q = ⟨FixFreeFormula.toMu φ', w', []⟩ ∧ Wins M φ' w' := by
        cases φ with
        | atom a => cases h
        | natom a => cases h
        | bot => cases h
        | top => cases h
        | and φ ψ =>
            simp only [FixFreeFormula.toMu] at h
            cases h with
            | andLeft => exact ⟨φ, w, rfl, hW.1⟩
            | andRight => exact ⟨ψ, w, rfl, hW.2⟩
        | or φ ψ =>
            have hchoice : q = winsMove M (FixFreeFormula.toMu (.or φ ψ)) w [] :=
              hσ rfl
            rcases winsMove_or hW with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact ⟨φ, w, hchoice.trans h1, h2⟩
            · exact ⟨ψ, w, hchoice.trans h1, h2⟩
        | box φ =>
            simp only [FixFreeFormula.toMu] at h
            cases h with
            | box hrel => exact ⟨φ, _, rfl, hW _ hrel⟩
        | dia φ =>
            have hchoice : q = winsMove M (FixFreeFormula.toMu (.dia φ)) w [] :=
              hσ rfl
            obtain ⟨v, hv, _, hWv⟩ := winsMove_dia hW
            exact ⟨φ, v, hchoice.trans hv, hWv⟩
      subst hq
      have hcomplete' : ∃ r, playLast ps = some r ∧ NoMoves M r := by
        obtain ⟨r, hlast, hno⟩ := hcomplete
        rw [playLast_cons hps.ne_nil] at hlast
        exact ⟨r, hlast, hno⟩
      obtain ⟨r, hlast', hterm⟩ := ih φ' w' rfl hW' hcomplete'
      refine ⟨r, ?_, hterm⟩
      rw [playLast_cons hps.ne_nil]
      exact hlast'

/-- The Wins-guided strategy wins every complete finite play from a winning
fragment position. -/
theorem winsStrategy_wins_finite (M : KripkeModel World Atom)
    {env : ℕ → World → Prop} :
    ∀ (φ : FixFreeFormula Atom) (w : World), Wins M φ w →
      ∀ ps : List (GamePosition Atom World),
        PlayFrom M (winsStrategy M) ⟨FixFreeFormula.toMu φ, w, []⟩ ps →
          (∃ q, playLast ps = some q ∧ NoMoves M q) →
            ∃ q, playLast ps = some q ∧ TerminalWin M env q := by
  intro φ w hW ps hplay hcomplete
  exact winsStrategy_wins_finite_aux M hplay φ w rfl hW hcomplete

/-- **Game-vs-satisfaction, strategy direction.** Let $M$ be a Kripke model, $\mathit{env}$ an
environment assigning a set of worlds to each variable index, $\varphi$ a fixpoint-free formula
and $w$ a world in the backward-induction winning region of $\varphi$. Then Verifier has a
winning strategy, in environment $\mathit{env}$, in the model-checking game on $M$ from the
position made of the μ-calculus embedding of $\varphi$, the world $w$ and the empty binder stack.

Source: C. Stirling, *Modal and Temporal Properties of Processes*, Springer 2001, Chapter 6. -/
theorem wins_implies_verifierWins (M : KripkeModel World Atom)
    (env : ℕ → World → Prop) (φ : FixFreeFormula Atom)
    (w : World) (hW : Wins M φ w) :
    VerifierWins M env ⟨FixFreeFormula.toMu φ, w, []⟩ := by
  refine ⟨winsStrategy M, ?_, ?_⟩
  · intro ps hplay hcomplete
    exact winsStrategy_wins_finite M φ w hW ps hplay hcomplete
  · intro play h0 hsteps
    exfalso
    exact no_infinite_play_of_fixFree h0 (fun n => (hsteps n).1)

/-- **Inversion for disjunction moves.** Let $M$ be a Kripke model, $\varphi$ and $\psi$
μ-calculus formulas, $w$ a world and $s$ a stack of fixpoint binders. If going from the game
position $(\varphi \vee \psi, w, s)$ to a position $q$ is a move of the model-checking game in
$M$, then $q$ is $(\varphi, w, s)$ or $(\psi, w, s)$: the world and the stack are unchanged. -/
theorem Move.or_cases {M : KripkeModel World Atom} {φ ψ : MuFormula Atom} {w : World}
    {st : List (MuFormula Atom)} {q : GamePosition Atom World}
    (h : Move M ⟨.or φ ψ, w, st⟩ q) : q = ⟨φ, w, st⟩ ∨ q = ⟨ψ, w, st⟩ := by
  cases h with
  | orLeft => exact Or.inl rfl
  | orRight => exact Or.inr rfl

/-- **Moves from a diamond position.** In the model-checking game on a Kripke model $M$, every
move from the position with formula $\Diamond\varphi$, world $w$ and binder stack $s$ goes to the
position with formula $\varphi$, world $v$ and the same stack $s$, for some world $v$ accessible
from $w$ in $M$. -/
theorem Move.dia_cases {M : KripkeModel World Atom} {φ : MuFormula Atom} {w : World}
    {st : List (MuFormula Atom)} {q : GamePosition Atom World}
    (h : Move M ⟨.dia φ, w, st⟩ q) :
    ∃ v, M.rel w v ∧ q = ⟨φ, v, st⟩ := by
  cases h with
  | dia hv => exact ⟨_, hv, rfl⟩

/-- **Game-vs-satisfaction, converse direction.** Let $M$ be a Kripke model, $\mathit{env}$ an
environment assigning a set of worlds to each variable index, $\varphi$ a fixpoint-free formula
and $w$ a world. If Verifier has a winning strategy, in environment $\mathit{env}$, in the
model-checking game on $M$ from the position made of the μ-calculus embedding of $\varphi$, the
world $w$ and the empty binder stack, then $w$ lies in the backward-induction winning region of
$\varphi$.

Source: C. Stirling, *Modal and Temporal Properties of Processes*, Springer 2001, Chapter 6. -/
theorem verifierWins_implies_wins (M : KripkeModel World Atom)
    (env : ℕ → World → Prop) (φ : FixFreeFormula Atom)
    (w : World) (hW : VerifierWins M env ⟨FixFreeFormula.toMu φ, w, []⟩) :
    Wins M φ w := by
  revert hW
  induction φ generalizing w with
  | atom a =>
      intro hW
      obtain ⟨σ, hσwin⟩ := hW
      have hplay : PlayFrom M σ ⟨.atom a, w, []⟩ [⟨.atom a, w, []⟩] := PlayFrom.single
      have hcomplete : ∃ q, playLast [⟨.atom a, w, []⟩] = some q ∧
          NoMoves M q := ⟨⟨.atom a, w, []⟩, rfl, fun q hq => by cases hq⟩
      obtain ⟨q, hlast, hterm⟩ := hσwin.1 _ hplay hcomplete
      simp only [playLast, List.getLast?_singleton] at hlast
      obtain rfl := Option.some.inj hlast
      exact hterm
  | natom a =>
      intro hW
      obtain ⟨σ, hσwin⟩ := hW
      have hplay : PlayFrom M σ ⟨.natom a, w, []⟩ [⟨.natom a, w, []⟩] := PlayFrom.single
      have hcomplete : ∃ q, playLast [⟨.natom a, w, []⟩] = some q ∧
          NoMoves M q := ⟨⟨.natom a, w, []⟩, rfl, fun q hq => by cases hq⟩
      obtain ⟨q, hlast, hterm⟩ := hσwin.1 _ hplay hcomplete
      simp only [playLast, List.getLast?_singleton] at hlast
      obtain rfl := Option.some.inj hlast
      exact hterm
  | bot =>
      intro hW
      obtain ⟨σ, hσwin⟩ := hW
      have hplay : PlayFrom M σ ⟨.bot, w, []⟩ [⟨.bot, w, []⟩] := PlayFrom.single
      have hcomplete : ∃ q, playLast [⟨.bot, w, []⟩] = some q ∧
          NoMoves M q := ⟨⟨.bot, w, []⟩, rfl, fun q hq => by cases hq⟩
      obtain ⟨q, hlast, hterm⟩ := hσwin.1 _ hplay hcomplete
      simp only [playLast, List.getLast?_singleton] at hlast
      obtain rfl := Option.some.inj hlast
      exact hterm
  | top => intro _; trivial
  | and φ ψ ihφ ihψ =>
      intro hW
      obtain ⟨σ, hσwin⟩ := hW
      refine ⟨?_, ?_⟩
      · exact ihφ w ⟨σ, strategyWins_of_move hσwin Move.andLeft
          (fun h => by simp [Owner, FixFreeFormula.toMu] at h)⟩
      · exact ihψ w ⟨σ, strategyWins_of_move hσwin Move.andRight
          (fun h => by simp [Owner, FixFreeFormula.toMu] at h)⟩
  | or φ ψ ihφ ihψ =>
      intro hW
      obtain ⟨σ, hσwin⟩ := hW
      have hmove : Move M ⟨FixFreeFormula.toMu (.or φ ψ), w, []⟩
          (σ.choose ⟨FixFreeFormula.toMu (.or φ ψ), w, []⟩) :=
        σ.choose_move _ rfl ⟨⟨FixFreeFormula.toMu φ, w, []⟩, Move.orLeft⟩
      have hSW : StrategyWins M env σ (σ.choose ⟨FixFreeFormula.toMu (.or φ ψ), w, []⟩) :=
        strategyWins_of_move hσwin hmove (fun _ => rfl)
      rcases Move.or_cases (φ := FixFreeFormula.toMu φ) (ψ := FixFreeFormula.toMu ψ)
          (w := w) (st := []) hmove with hEq | hEq <;>
        rw [hEq] at hSW
      · exact Or.inl (ihφ w ⟨σ, hSW⟩)
      · exact Or.inr (ihψ w ⟨σ, hSW⟩)
  | box φ ih =>
      intro hW
      obtain ⟨σ, hσwin⟩ := hW
      intro v hv
      exact ih v ⟨σ, strategyWins_of_move hσwin (Move.box hv)
        (fun h => by simp [Owner, FixFreeFormula.toMu] at h)⟩
  | dia φ ih =>
      intro hW
      obtain ⟨σ, hσwin⟩ := hW
      have hsucc : ∃ v, M.rel w v := by
        by_contra hnsucc
        push Not at hnsucc
        have hNoMoves : NoMoves M ⟨FixFreeFormula.toMu (.dia φ), w, []⟩ := by
          intro q hq
          simp only [FixFreeFormula.toMu] at hq
          cases hq with
          | dia hv => exact hnsucc _ hv
        have hplay : PlayFrom M σ ⟨FixFreeFormula.toMu (.dia φ), w, []⟩
            [⟨FixFreeFormula.toMu (.dia φ), w, []⟩] := PlayFrom.single
        have hcomplete : ∃ q, playLast [⟨FixFreeFormula.toMu (.dia φ), w, []⟩] = some q ∧
            NoMoves M q := ⟨⟨FixFreeFormula.toMu (.dia φ), w, []⟩, rfl, hNoMoves⟩
        obtain ⟨q, hlast, hterm⟩ := hσwin.1 _ hplay hcomplete
        simp only [playLast, List.getLast?_singleton] at hlast
        obtain rfl := Option.some.inj hlast
        exact hterm
      obtain ⟨v, hv⟩ := hsucc
      have hmove : Move M ⟨FixFreeFormula.toMu (.dia φ), w, []⟩
          (σ.choose ⟨FixFreeFormula.toMu (.dia φ), w, []⟩) :=
        σ.choose_move _ rfl ⟨⟨FixFreeFormula.toMu φ, v, []⟩, Move.dia hv⟩
      have hSW : StrategyWins M env σ (σ.choose ⟨FixFreeFormula.toMu (.dia φ), w, []⟩) :=
        strategyWins_of_move hσwin hmove (fun _ => rfl)
      obtain ⟨v', hv', hEq⟩ := Move.dia_cases (φ := FixFreeFormula.toMu φ) (w := w)
        (st := []) hmove
      rw [hEq] at hSW
      exact ⟨v', hv', ih v' ⟨σ, hSW⟩⟩

/-- **Backward-induction winning equals game winning on the fixpoint-free fragment.** For every
Kripke model $M$, environment $\mathit{env}$, fixpoint-free formula $\varphi$ and world $w$, $w$
lies in the backward-induction winning region of $\varphi$ if and only if Verifier has a winning
strategy, in environment $\mathit{env}$, in the model-checking game on $M$ from the position made
of the μ-calculus embedding of $\varphi$, the world $w$ and the empty binder stack.

Source: C. Stirling, *Modal and Temporal Properties of Processes*, Springer 2001, Chapter 6. -/
theorem wins_iff_verifierWins (M : KripkeModel World Atom)
    (env : ℕ → World → Prop) (φ : FixFreeFormula Atom) (w : World) :
    Wins M φ w ↔ VerifierWins M env ⟨FixFreeFormula.toMu φ, w, []⟩ :=
  ⟨wins_implies_verifierWins M env φ w, verifierWins_implies_wins M env φ w⟩

/-! ### The fragment game as a canonical parity game -/

/-- **Positions of the totalized fragment game.** A position of the totalized fragment game, over
a type of atoms and a type of worlds, is either an embedded position $(\varphi, w)$ of a
fixpoint-free formula $\varphi$ and a world $w$, standing for the model-checking game position
$(\varphi, w, [])$ with $\varphi$ embedded as a μ-calculus formula and the empty fixpoint stack,
or one of two absorbing states: the winning state, where Verifier has won, and the losing state,
where Refuter has won.

Since the arena contains no fixpoint positions and every move between embedded positions
strictly decreases the formula, priority $0$ on embedded positions is sound. An embedded
position with no moves leads to the winning state if it is a terminal win for Verifier and to
the losing state otherwise, and both absorbing states loop to themselves, so the game has no
dead ends and is a parity game. -/
inductive FragPos (Atom World : Type u) where
  /-- An embedded fragment position `(φ, w)`, standing for `⟨toMu φ, w, []⟩`. -/
  | pos : FixFreeFormula Atom → World → FragPos Atom World
  /-- Absorbing Verifier-wins state. -/
  | win : FragPos Atom World
  /-- Absorbing Refuter-wins state. -/
  | lose : FragPos Atom World

/-- **Projection of game positions onto the fragment arena.** A game position with empty binder
stack whose formula is the μ-calculus reading of a fixpoint-free formula $\varphi$, at world $w$,
is sent to the embedded position $(\varphi, w)$. Every other game position (one whose formula
contains a fixpoint operator or a variable, or one with a nonempty stack) is sent to the losing
state.

The losing state is a default that is never reached on plays that stay in the arena, since every
move from an embedded position lands on an embedded position.

Source: C. Stirling, *Modal
and Temporal Properties of Processes*, Springer 2001, Chapter 6. -/
def fragOfGamePos : GamePosition Atom World → FragPos Atom World
  | ⟨ψ, w, []⟩ =>
      match toMuInv ψ with
      | some φ => .pos φ w
      | none => .lose
  | ⟨_, _, _ :: _⟩ => .lose

/-- **Projection of an embedded position.** For every fixpoint-free formula $\varphi$ and world
$w$, projecting the game position with formula $\varphi$ (read as a μ-calculus formula), world $w$
and empty binder stack onto the fragment arena gives the embedded position $(\varphi, w)$. -/
theorem fragOfGamePos_toMu (φ : FixFreeFormula Atom) (w : World) :
    fragOfGamePos (⟨FixFreeFormula.toMu φ, w, []⟩ : GamePosition Atom World) =
      FragPos.pos φ w := by
  simp [fragOfGamePos, toMuInv_toMu]

/-- **Moves of the totalized fragment game.** Let $M$ be a Kripke model and $e$ an environment,
and read each fixpoint-free formula $\varphi$ as a μ-calculus formula. The totalized fragment game
of $M$ and $e$ has these moves: from an embedded position $(\varphi, w)$ to $(\varphi', w')$
whenever the model-checking game of $M$ has a move from $(\varphi, w)$ to $(\varphi', w')$ with
empty binder stacks; from $(\varphi, w)$ to the winning state when the game position
$(\varphi, w)$ with empty stack has no moves and is won by Verifier in environment $e$; from
$(\varphi, w)$ to the losing state when that game position has no moves and is not won by
Verifier; and from each of the winning and losing states to itself. -/
inductive FragMove (M : KripkeModel World Atom) (env : ℕ → World → Prop) :
    FragPos Atom World → FragPos Atom World → Prop
  /-- A game move between embedded fragment positions. -/
  | pos_move {φ φ' : FixFreeFormula Atom} {w w' : World}
      (h : Move M ⟨FixFreeFormula.toMu φ, w, []⟩
        ⟨FixFreeFormula.toMu φ', w', []⟩) :
      FragMove M env (.pos φ w) (.pos φ' w')
  /-- A terminal winning position moves to the absorbing win state. -/
  | toWin {φ : FixFreeFormula Atom} {w : World}
      (hNo : NoMoves M ⟨FixFreeFormula.toMu φ, w, []⟩)
      (hWin : TerminalWin M env ⟨FixFreeFormula.toMu φ, w, []⟩) :
      FragMove M env (.pos φ w) .win
  /-- A terminal losing position moves to the absorbing lose state. -/
  | toLose {φ : FixFreeFormula Atom} {w : World}
      (hNo : NoMoves M ⟨FixFreeFormula.toMu φ, w, []⟩)
      (hLose : ¬ TerminalWin M env ⟨FixFreeFormula.toMu φ, w, []⟩) :
      FragMove M env (.pos φ w) .lose
  /-- The win state loops. -/
  | win_self : FragMove M env .win .win
  /-- The lose state loops. -/
  | lose_self : FragMove M env .lose .lose

/-- **Owners in the totalized fragment game.** In the totalized fragment game, an embedded
position $(\varphi, w)$ of a fixpoint-free formula $\varphi$ at a world $w$ is owned by the even
player if Verifier owns the model-checking game position $(\varphi, w, [])$ (with $\varphi$
embedded as a μ-calculus formula and the empty fixpoint stack), and by the odd player otherwise,
that is, when Refuter owns it. The absorbing winning and losing states are both owned by the
even player.

Verifier plays the even player; the moves at the absorbing states are forced, so their owner
does not matter. -/
def fragOwner : FragPos Atom World → Cslib.Games.Player
  | .pos φ w =>
      if Owner ⟨FixFreeFormula.toMu φ, w, []⟩ = true then
        Cslib.Games.Player.even
      else Cslib.Games.Player.odd
  | .win => Cslib.Games.Player.even
  | .lose => Cslib.Games.Player.even

/-- **Priorities in the totalized fragment game.** In the totalized fragment game, every embedded
position $(\varphi, w)$ of a fixpoint-free formula $\varphi$ at a world $w$ has priority $0$, the
absorbing winning state has priority $0$, and the absorbing losing state has priority $1$.

So an infinite play that eventually stays at the winning state is won by the even player, and
one that eventually stays at the losing state by the odd player. Priority $0$ on embedded
positions is sound because the arena contains no fixpoint positions and every move between
embedded positions strictly decreases the formula, so no infinite play visits only embedded
positions. -/
def fragPriority : FragPos Atom World → ℕ
  | .pos _ _ => 0
  | .win => 0
  | .lose => 1

/-- **Fragment parity game.** Let $M$ be a Kripke model and $\rho$ an environment, and write
$(\varphi, w, [])$ for the game position with formula $\varphi$, world $w$ and empty binder
stack. The fragment game of $M$ and $\rho$ is the parity game on the totalized fragment
positions defined as follows. An embedded position $(\varphi, w)$ moves to $(\varphi', w')$
when $(\varphi, w, [])$ has a move to $(\varphi', w', [])$ in the model-checking game on $M$;
if $(\varphi, w, [])$ has no moves, $(\varphi, w)$ moves to the winning state when
$(\varphi, w, [])$ is a terminal win in $\rho$ and to the losing state otherwise; the winning
and losing states move only to themselves. The even player owns both absorbing states and the
embedded positions $(\varphi, w)$ such that Verifier owns $(\varphi, w, [])$; the odd player
owns the other embedded positions. Embedded positions and the winning state have priority $0$;
the losing state has priority $1$. -/
noncomputable def fragmentGame (M : KripkeModel World Atom)
    (env : ℕ → World → Prop) : Cslib.Games.ParityGame (FragPos Atom World) where
  owner := fragOwner
  Move := FragMove M env
  priority := fragPriority
  serial := by
    intro v
    cases v with
    | win => exact ⟨.win, FragMove.win_self⟩
    | lose => exact ⟨.lose, FragMove.lose_self⟩
    | pos φ w =>
        by_cases hExists : ∃ φ' w', Move M
            ⟨FixFreeFormula.toMu φ, w, []⟩ ⟨FixFreeFormula.toMu φ', w', []⟩
        · obtain ⟨φ', w', hq⟩ := hExists
          exact ⟨.pos φ' w', FragMove.pos_move hq⟩
        · have hNo : NoMoves M ⟨FixFreeFormula.toMu φ, w, []⟩ := by
            intro q hq
            obtain ⟨φ', w', hq', -⟩ := move_of_toMu hq
            exact hExists ⟨φ', w', by rwa [hq'] at hq⟩
          by_cases hWin : TerminalWin M env ⟨FixFreeFormula.toMu φ, w, []⟩
          · exact ⟨.win, FragMove.toWin hNo hWin⟩
          · exact ⟨.lose, FragMove.toLose hNo hWin⟩

/-- **The absorbing win state.** In the totalized fragment game on a Kripke model $M$ with
environment $\mathit{env}$, every move from the absorbing Verifier-wins state $\mathrm{win}$
leads back to it: if $\mathrm{win}$ moves to $v$, then $v = \mathrm{win}$. -/
theorem FragMove.win_eq {M : KripkeModel World Atom} {env : ℕ → World → Prop}
    {v : FragPos Atom World} (h : FragMove M env .win v) : v = .win := by
  cases h with
  | win_self => rfl

/-- **The losing state is absorbing.** In the fragment game of a Kripke model $M$ and an
environment $\rho$, every move from the losing state goes to the losing state. -/
theorem FragMove.lose_eq {M : KripkeModel World Atom} {env : ℕ → World → Prop}
    {v : FragPos Atom World} (h : FragMove M env .lose v) : v = .lose := by
  cases h with
  | lose_self => rfl

/-- **Fragment moves between embedded positions are game moves.** Let $M$ be a Kripke model,
$\mathrm{env}$ an environment, $\varphi, \varphi'$ fixpoint-free formulas and $w, w'$ worlds. If
the totalized fragment game has a move from the embedded position $(\varphi, w)$ to the embedded
position $(\varphi', w')$, then the model-checking game has a move from $(\varphi, w, [])$ to
$(\varphi', w', [])$, where the fixpoint-free formulas are viewed as μ-calculus formulas and
$[]$ is the empty binder stack. -/
theorem FragMove.pos_move_iff {M : KripkeModel World Atom}
    {env : ℕ → World → Prop} {φ φ' : FixFreeFormula Atom} {w w' : World}
    (h : FragMove M env (.pos φ w) (.pos φ' w')) :
    Move M ⟨FixFreeFormula.toMu φ, w, []⟩
      ⟨FixFreeFormula.toMu φ', w', []⟩ := by
  cases h with
  | pos_move h => exact h

/-- **Moves to the winning state come from terminal winning positions.** Let $M$ be a Kripke
model, $\mathrm{env}$ an environment, $\varphi$ a fixpoint-free formula and $w$ a world. If the
totalized fragment game has a move from the embedded position $(\varphi, w)$ to the absorbing
winning state, then the game position $(\varphi, w, [])$, with $\varphi$ viewed as a μ-calculus
formula and an empty binder stack, has no moves, and Verifier wins there as a terminal position
in the environment $\mathrm{env}$. -/
theorem FragMove.pos_toWin {M : KripkeModel World Atom} {env : ℕ → World → Prop}
    {φ : FixFreeFormula Atom} {w : World}
    (h : FragMove M env (.pos φ w) .win) :
    NoMoves M ⟨FixFreeFormula.toMu φ, w, []⟩ ∧
      TerminalWin M env ⟨FixFreeFormula.toMu φ, w, []⟩ := by
  cases h with
  | toWin hNo hWin => exact ⟨hNo, hWin⟩

/-- **Moves to the losing state come from terminal losing positions.** Let $M$ be a Kripke model,
$\mathrm{env}$ an environment, $\varphi$ a fixpoint-free formula and $w$ a world. If the
totalized fragment game has a move from the embedded position $(\varphi, w)$ to the absorbing
losing state, then the game position $(\varphi, w, [])$, with $\varphi$ viewed as a μ-calculus
formula and an empty binder stack, has no moves, and Verifier does not win there as a terminal
position in the environment $\mathrm{env}$. -/
theorem FragMove.pos_toLose {M : KripkeModel World Atom} {env : ℕ → World → Prop}
    {φ : FixFreeFormula Atom} {w : World}
    (h : FragMove M env (.pos φ w) .lose) :
    NoMoves M ⟨FixFreeFormula.toMu φ, w, []⟩ ∧
      ¬ TerminalWin M env ⟨FixFreeFormula.toMu φ, w, []⟩ := by
  cases h with
  | toLose hNo hLose => exact ⟨hNo, hLose⟩

/-- **Owner of an embedded position in the totalized fragment game.** For every fixpoint-free
formula $\varphi$ and world $w$, the even player owns the embedded position $(\varphi, w)$ of the
totalized fragment game if and only if Verifier owns the model-checking game position
$(\varphi, w, [])$, with $\varphi$ embedded as a μ-calculus formula and the empty fixpoint stack. -/
theorem fragOwner_pos_eq_even {φ : FixFreeFormula Atom} {w : World} :
    fragOwner (FragPos.pos φ w : FragPos Atom World) = Cslib.Games.Player.even ↔
      Owner ⟨FixFreeFormula.toMu φ, w, []⟩ = true := by
  show (if Owner ⟨FixFreeFormula.toMu φ, w, []⟩ = true then
      Cslib.Games.Player.even else Cslib.Games.Player.odd) =
      Cslib.Games.Player.even ↔ Owner ⟨FixFreeFormula.toMu φ, w, []⟩ = true
  by_cases h : Owner ⟨FixFreeFormula.toMu φ, w, []⟩ = true
  · rw [ite_eq_left h]; simp [h]
  · rw [ite_eq_right h]; simp [h]

open Classical in
/-- **Canonical next move induced by a bespoke strategy.** Let $M$ be a Kripke model,
$\mathit{env}$ an environment and $\sigma$ a Verifier strategy for the model-checking game on
$M$. Write $\langle \psi, v \rangle$ for the game position with the embedding of a
fixpoint-free formula $\psi$, the world $v$ and the empty binder stack. The canonical next move
is the map on positions of the fragment arena defined as follows. The absorbing states
$\mathrm{win}$ and $\mathrm{lose}$ are sent to themselves. A fragment position $(\varphi, w)$
such that $\langle \varphi, w \rangle$ has a move to some $\langle \varphi', w' \rangle$ is
sent, if Verifier owns $\langle \varphi, w \rangle$, to the projection into the fragment arena
of the position that $\sigma$ chooses there (an embedded position $\langle \varphi', w' \rangle$
projects to $(\varphi', w')$, every other game position to $\mathrm{lose}$), and otherwise to a
fragment position $(\varphi', w')$ chosen, by the axiom of choice, among those with a move from
$\langle \varphi, w \rangle$ to $\langle \varphi', w' \rangle$. A fragment position
$(\varphi, w)$ with no such move is sent to $\mathrm{win}$ if $\langle \varphi, w \rangle$
satisfies the terminal winning condition for Verifier in environment $\mathit{env}$, and to
$\mathrm{lose}$ otherwise. -/
noncomputable def canonicalNext (M : KripkeModel World Atom)
    (env : ℕ → World → Prop) (σ : Strategy M) : FragPos Atom World → FragPos Atom World
  | .win => .win
  | .lose => .lose
  | .pos φ w =>
      if hExists : ∃ φ' w', Move M ⟨FixFreeFormula.toMu φ, w, []⟩
          ⟨FixFreeFormula.toMu φ', w', []⟩ then
        if Owner ⟨FixFreeFormula.toMu φ, w, []⟩ = true then
          fragOfGamePos (σ.choose ⟨FixFreeFormula.toMu φ, w, []⟩)
        else
          .pos (Classical.choose hExists)
            (Classical.choose (Classical.choose_spec hExists))
      else if TerminalWin M env ⟨FixFreeFormula.toMu φ, w, []⟩ then .win else .lose

/-- **The canonical move follows the bespoke strategy at Verifier positions with a move.** Let
$M$ be a Kripke model, $\mathit{env}$ an environment and $\sigma$ a Verifier strategy for the
model-checking game on $M$. Write $\langle \psi, v \rangle$ for the game position with the
embedding of a fixpoint-free formula $\psi$, the world $v$ and the empty binder stack. Let
$\varphi$ be a fixpoint-free formula and $w$ a world such that Verifier owns
$\langle \varphi, w \rangle$ and $\langle \varphi, w \rangle$ has a move to some
$\langle \varphi'', w'' \rangle$. Then there are a fixpoint-free formula $\varphi'$ and a world
$w'$ such that the canonical next move induced by $\sigma$ (in environment $\mathit{env}$) sends
the fragment position $(\varphi, w)$ to the fragment position $(\varphi', w')$, and $\sigma$
chooses $\langle \varphi', w' \rangle$ at $\langle \varphi, w \rangle$. -/
theorem canonicalNext_pos_of_owner {M : KripkeModel World Atom}
    {env : ℕ → World → Prop} {σ : Strategy M} {φ : FixFreeFormula Atom}
    {w : World}
    (hOwn : Owner ⟨FixFreeFormula.toMu φ, w, []⟩ = true)
    (hExists : ∃ φ' w', Move M ⟨FixFreeFormula.toMu φ, w, []⟩
      ⟨FixFreeFormula.toMu φ', w', []⟩) :
    ∃ φ' w', canonicalNext M env σ (.pos φ w) = .pos φ' w' ∧
      σ.choose ⟨FixFreeFormula.toMu φ, w, []⟩ = ⟨FixFreeFormula.toMu φ', w', []⟩ := by
  classical
  have hEx : ∃ q, Move M ⟨FixFreeFormula.toMu φ, w, []⟩ q := by
    obtain ⟨φ₀, w₀, h₀⟩ := hExists
    exact ⟨⟨FixFreeFormula.toMu φ₀, w₀, []⟩, h₀⟩
  obtain ⟨φ', w', heq, -⟩ :=
    move_of_toMu (σ.choose_move ⟨FixFreeFormula.toMu φ, w, []⟩ hOwn hEx)
  refine ⟨φ', w', ?_, heq⟩
  show (if h : ∃ φ' w', Move M ⟨FixFreeFormula.toMu φ, w, []⟩
        ⟨FixFreeFormula.toMu φ', w', []⟩ then
      (if Owner ⟨FixFreeFormula.toMu φ, w, []⟩ = true then
        fragOfGamePos (σ.choose ⟨FixFreeFormula.toMu φ, w, []⟩)
      else .pos (Classical.choose h)
        (Classical.choose (Classical.choose_spec h)))
    else if TerminalWin M env ⟨FixFreeFormula.toMu φ, w, []⟩ then FragPos.win
    else FragPos.lose) = FragPos.pos φ' w'
  rw [dite_eq_left hExists, ite_eq_left hOwn, heq]
  exact fragOfGamePos_toMu φ' w'

/-- The canonical positional strategy induced by a bespoke strategy. -/
noncomputable def fragStrategy (M : KripkeModel World Atom)
    (env : ℕ → World → Prop) (σ : Strategy M) :
    (fragmentGame M env).PositionalStrategy Cslib.Games.Player.even where
  next := canonicalNext M env σ
  legal := by
    intro v hv
    cases v with
    | win =>
        show FragMove M env .win (canonicalNext M env σ .win)
        rw [show canonicalNext M env σ (FragPos.win : FragPos Atom World) = .win from rfl]
        exact FragMove.win_self
    | lose =>
        show FragMove M env .lose (canonicalNext M env σ .lose)
        rw [show canonicalNext M env σ (FragPos.lose : FragPos Atom World) = .lose from rfl]
        exact FragMove.lose_self
    | pos φ w =>
        have hOwn : Owner ⟨FixFreeFormula.toMu φ, w, []⟩ = true :=
          (fragOwner_pos_eq_even).mp hv
        show FragMove M env (.pos φ w) (canonicalNext M env σ (.pos φ w))
        by_cases hExists : ∃ φ' w', Move M ⟨FixFreeFormula.toMu φ, w, []⟩
            ⟨FixFreeFormula.toMu φ', w', []⟩
        · obtain ⟨φ', w', hNext, heq⟩ := canonicalNext_pos_of_owner hOwn hExists
          obtain ⟨φ₀, w₀, h₀⟩ := hExists
          have hChoose : Move M ⟨FixFreeFormula.toMu φ, w, []⟩
              ⟨FixFreeFormula.toMu φ', w', []⟩ := by
            rw [← heq]
            exact σ.choose_move _ hOwn ⟨⟨FixFreeFormula.toMu φ₀, w₀, []⟩, h₀⟩
          rw [hNext]
          exact FragMove.pos_move hChoose
        · have hNo : NoMoves M ⟨FixFreeFormula.toMu φ, w, []⟩ := by
            intro q hq
            obtain ⟨φ', w', hq', -⟩ := move_of_toMu hq
            exact hExists ⟨φ', w', by rwa [hq'] at hq⟩
          by_cases hWin : TerminalWin M env ⟨FixFreeFormula.toMu φ, w, []⟩
          · have hNext : canonicalNext M env σ (.pos φ w) = FragPos.win := by
              classical
              show (if h : ∃ φ' w', Move M ⟨FixFreeFormula.toMu φ, w, []⟩
                  ⟨FixFreeFormula.toMu φ', w', []⟩ then
                (if Owner ⟨FixFreeFormula.toMu φ, w, []⟩ = true then
                  fragOfGamePos (σ.choose ⟨FixFreeFormula.toMu φ, w, []⟩)
                else .pos (Classical.choose h)
                  (Classical.choose (Classical.choose_spec h)))
                else if TerminalWin M env ⟨FixFreeFormula.toMu φ, w, []⟩ then
                  FragPos.win else FragPos.lose) = FragPos.win
              rw [dite_eq_right hExists, ite_eq_left hWin]
            rw [hNext]
            exact FragMove.toWin hNo hWin
          · have hNext : canonicalNext M env σ (.pos φ w) = FragPos.lose := by
              classical
              show (if h : ∃ φ' w', Move M ⟨FixFreeFormula.toMu φ, w, []⟩
                  ⟨FixFreeFormula.toMu φ', w', []⟩ then
                (if Owner ⟨FixFreeFormula.toMu φ, w, []⟩ = true then
                  fragOfGamePos (σ.choose ⟨FixFreeFormula.toMu φ, w, []⟩)
                else .pos (Classical.choose h)
                  (Classical.choose (Classical.choose_spec h)))
                else if TerminalWin M env ⟨FixFreeFormula.toMu φ, w, []⟩ then
                  FragPos.win else FragPos.lose) = FragPos.lose
              rw [dite_eq_right hExists, ite_eq_right hWin]
            rw [hNext]
            exact FragMove.toLose hNo hWin

/-- **Game position of a fragment position.** Given a default game position $p_0$, an embedded
fragment position $(\varphi, w)$ is sent to the game position with formula $\varphi$, world $w$
and empty binder stack, and the absorbing winning and losing states are both sent to $p_0$.

The default is never used on plays that stay among embedded positions. -/
def fragToPos (p0 : GamePosition Atom World) : FragPos Atom World → GamePosition Atom World
  | .pos φ w => ⟨FixFreeFormula.toMu φ, w, []⟩
  | _ => p0

/-- **Segment of a fragment play as game positions.** Let $p_0$ be a game position and let
$\pi = \pi_0 \pi_1 \pi_2 \dots$ be an infinite sequence of positions of the totalized fragment
game. For natural numbers $s$ and $k$, the segment of $\pi$ from $s$ of length $k + 1$ is the
list of game positions obtained from $\pi_s, \pi_{s+1}, \dots, \pi_{s+k}$, in this order, by
sending each embedded position $(\varphi, w)$ to the game position with formula $\varphi$, world
$w$ and empty binder stack, and each of the absorbing winning and losing states to $p_0$. -/
def fragSegment (p0 : GamePosition Atom World) (π : ωSequence (FragPos Atom World))
    (start : ℕ) : ℕ → List (GamePosition Atom World)
  | 0 => [fragToPos p0 (π start)]
  | k + 1 => fragToPos p0 (π start) :: fragSegment p0 π (start + 1) k

/-- **Splitting off the head of a segment.** Let $p_0$ be a model-checking game position and $\pi$
an infinite sequence of positions of the totalized fragment game. For each $i$, let $\hat\pi_i$ be
$p_0$ if $\pi_i$ is an absorbing state; if $\pi_i$ is the embedded position $(\varphi, w)$ of a
fixpoint-free formula $\varphi$ and a world $w$, let $\hat\pi_i$ be the game position
$(\varphi, w, [])$, with $\varphi$ embedded as a μ-calculus formula and the empty fixpoint stack.
For all natural numbers $s$ and $k$, the segment $[\hat\pi_s, \dots, \hat\pi_{s+k+1}]$ of $\pi$ is
the list with head $\hat\pi_s$ followed by the segment $[\hat\pi_{s+1}, \dots, \hat\pi_{s+k+1}]$. -/
theorem fragSegment_cons (p0 : GamePosition Atom World)
    (π : ωSequence (FragPos Atom World)) (start k : ℕ) :
    fragSegment p0 π start (k + 1) =
      fragToPos p0 (π start) :: fragSegment p0 π (start + 1) k := rfl

/-- **Segments of canonical plays through fragment positions are bespoke plays.** Let $M$ be a
Kripke model, $\mathit{env}$ an environment and $\sigma$ a Verifier strategy for the
model-checking game on $M$. Write $\langle \psi, v \rangle$ for the game position with the
embedding of a fixpoint-free formula $\psi$, the world $v$ and the empty binder stack. Let $\pi$
be a play of the fragment game of $M$ and $\mathit{env}$ that conforms to the canonical
positional strategy induced by $\sigma$, and let $s, k \in \mathbb{N}$. Suppose every $\pi_i$
with $s \le i \le s + k$ is a fragment position $(\varphi_i, w_i)$, not $\mathrm{win}$ or
$\mathrm{lose}$. Then the list
$\langle \varphi_s, w_s \rangle, \langle \varphi_{s+1}, w_{s+1} \rangle, \dots,
\langle \varphi_{s+k}, w_{s+k} \rangle$ is a finite play from $\langle \varphi_s, w_s \rangle$
consistent with $\sigma$: each position has a game move to the next, and at Verifier-owned
positions the next position is the one $\sigma$ chooses. -/
theorem canonical_playFrom_segment {M : KripkeModel World Atom}
    {env : ℕ → World → Prop} {σ : Strategy M} {π : ωSequence (FragPos Atom World)}
    (p0 : GamePosition Atom World) (start k : ℕ)
    (φ : FixFreeFormula Atom) (w : World)
    (hplay : (fragmentGame M env).IsPlay π)
    (hconf : Cslib.Games.ParityGame.Conforms (fragStrategy M env σ) π)
    (hstart : π start = .pos φ w)
    (hpos : ∀ i, start ≤ i → i ≤ start + k → ∃ φ' w', π i = .pos φ' w') :
    PlayFrom M σ ⟨FixFreeFormula.toMu φ, w, []⟩ (fragSegment p0 π start k) := by
  induction k generalizing start φ w with
  | zero =>
      have hseg : fragSegment p0 π start 0 = [⟨FixFreeFormula.toMu φ, w, []⟩] := by
        simp [fragSegment, fragToPos, hstart]
      rw [hseg]
      exact PlayFrom.single
  | succ k ih =>
      rw [fragSegment_cons]
      have hhead : fragToPos p0 (π start) = ⟨FixFreeFormula.toMu φ, w, []⟩ := by
        rw [hstart]; rfl
      rw [hhead]
      obtain ⟨φNext, wNext, hNext⟩ := hpos (start + 1) (by omega) (by omega)
      have hMove : Move M ⟨FixFreeFormula.toMu φ, w, []⟩
          ⟨FixFreeFormula.toMu φNext, wNext, []⟩ := by
        have hm : FragMove M env (π start) (π (start + 1)) := hplay start
        rw [hstart, hNext] at hm
        exact FragMove.pos_move_iff hm
      have htail : PlayFrom M σ ⟨FixFreeFormula.toMu φNext, wNext, []⟩
          (fragSegment p0 π (start + 1) k) :=
        ih (start + 1) φNext wNext hNext (fun i hi1 hi2 => hpos i (by omega) (by omega))
      refine PlayFrom.cons hMove ?_ htail
      intro hOwn
      have howner : (fragmentGame M env).owner (π start) = Cslib.Games.Player.even := by
        rw [hstart]
        exact (fragOwner_pos_eq_even).mpr hOwn
      have hconf' := hconf start howner
      rw [hstart] at hconf'
      obtain ⟨φ', w', hnext, heq⟩ :=
        canonicalNext_pos_of_owner hOwn ⟨φNext, wNext, hMove⟩
      have hnext' : (fragStrategy M env σ).next (.pos φ w) = .pos φ' w' := by
        show canonicalNext M env σ (.pos φ w) = .pos φ' w'
        exact hnext
      rw [hnext', hNext] at hconf'
      injection hconf' with hφ hw
      subst hφ
      subst hw
      exact heq.symm

/-- **Plays of the totalized fragment game stay at the winning state.** Let $M$ be a Kripke model
and $\mathit{env}$ an environment assigning a set of worlds to each free-variable index. If
$\pi$ is a play of the totalized fragment game of $M$ and $\mathit{env}$ and $\pi_k$ is the
absorbing winning state, then $\pi_n$ is the winning state for every $n \ge k$. -/
theorem fragPlay_eq_win_of_le {M : KripkeModel World Atom}
    {env : ℕ → World → Prop} {π : ωSequence (FragPos Atom World)} {k n : ℕ}
    (hplay : (fragmentGame M env).IsPlay π) (hk : π k = .win) (hn : k ≤ n) :
    π n = .win := by
  induction n, hn using Nat.le_induction with
  | base => exact hk
  | succ n hn ih =>
      have hmove : FragMove M env (π n) (π (n + 1)) := hplay n
      rw [ih] at hmove
      exact FragMove.win_eq hmove

/-- **Plays of the totalized fragment game stay at the losing state.** Let $M$ be a Kripke model
and $\mathit{env}$ an environment assigning a set of worlds to each free-variable index. If
$\pi$ is a play of the totalized fragment game of $M$ and $\mathit{env}$ and $\pi_k$ is the
absorbing losing state, then $\pi_n$ is the losing state for every $n \ge k$. -/
theorem fragPlay_eq_lose_of_le {M : KripkeModel World Atom}
    {env : ℕ → World → Prop} {π : ωSequence (FragPos Atom World)} {k n : ℕ}
    (hplay : (fragmentGame M env).IsPlay π) (hk : π k = .lose) (hn : k ≤ n) :
    π n = .lose := by
  induction n, hn using Nat.le_induction with
  | base => exact hk
  | succ n hn ih =>
      have hmove : FragMove M env (π n) (π (n + 1)) := hplay n
      rw [ih] at hmove
      exact FragMove.lose_eq hmove

/-- **Sequences that stay at the win state are won by the even player.** Let $M$ be a Kripke
model and $\mathit{env}$ an environment for free variables. If an infinite sequence
$\pi_0 \pi_1 \pi_2 \dots$ of positions of the totalized fragment game of $M$ and $\mathit{env}$
has a $k_0$ such that $\pi_n$ is the absorbing winning state for all $n \ge k_0$, then $\pi$ is
won by the even player in that game. -/
theorem wonBy_even_of_eventually_win {M : KripkeModel World Atom}
    {env : ℕ → World → Prop} {π : ωSequence (FragPos Atom World)} {k0 : ℕ}
    (hwin : ∀ n, k0 ≤ n → π n = .win) :
    (fragmentGame M env).WonBy Cslib.Games.Player.even π := by
  show Cslib.ωSequence.ParityEven (π.map fragPriority)
  refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
  · have hev : ∀ᶠ n in Filter.atTop, (π.map fragPriority) n = 0 :=
      Filter.eventually_atTop.mpr ⟨k0, fun n hn => by
        show fragPriority (π n) = 0
        rw [hwin n hn]
        rfl⟩
    exact hev.frequently
  · intro m hm
    obtain ⟨n, hn, hEq⟩ := Filter.frequently_atTop.mp hm k0
    have h1 : (π.map fragPriority) n = 0 := by
      show fragPriority (π n) = 0
      rw [hwin n hn]
      rfl
    rw [h1] at hEq
    omega

/-- **Sequences that stay at the lose state are won by the odd player.** Let $M$ be a Kripke
model and $\mathit{env}$ an environment for free variables. If an infinite sequence
$\pi_0 \pi_1 \pi_2 \dots$ of positions of the totalized fragment game of $M$ and $\mathit{env}$
has a $k_0$ such that $\pi_n$ is the absorbing losing state for all $n \ge k_0$, then $\pi$ is
won by the odd player in that game. -/
theorem wonBy_odd_of_eventually_lose {M : KripkeModel World Atom}
    {env : ℕ → World → Prop} {π : ωSequence (FragPos Atom World)} {k0 : ℕ}
    (hlose : ∀ n, k0 ≤ n → π n = .lose) :
    (fragmentGame M env).WonBy Cslib.Games.Player.odd π := by
  show Cslib.ωSequence.ParityOdd (π.map fragPriority)
  refine ⟨1, ⟨0, rfl⟩, ?_, ?_⟩
  · have hev : ∀ᶠ n in Filter.atTop, (π.map fragPriority) n = 1 :=
      Filter.eventually_atTop.mpr ⟨k0, fun n hn => by
        show fragPriority (π n) = 1
        rw [hlose n hn]
        rfl⟩
    exact hev.frequently
  · intro m hm
    obtain ⟨n, hn, hEq⟩ := Filter.frequently_atTop.mp hm k0
    have h1 : (π.map fragPriority) n = 1 := by
      show fragPriority (π n) = 1
      rw [hlose n hn]
      rfl
    rw [h1] at hEq
    omega

/-- **Segments are nonempty.** Let $p_0$ be a model-checking game position and $\pi$ an infinite
sequence of positions of the totalized fragment game. For all natural numbers $s$ and $k$, the
segment of $\pi$ from index $s$ to index $s + k$, read as a list of model-checking game positions
with $p_0$ standing for the absorbing states, is not the empty list. -/
theorem fragSegment_ne_nil (p0 : GamePosition Atom World)
    (π : ωSequence (FragPos Atom World)) (start k : ℕ) :
    fragSegment p0 π start k ≠ [] := by
  cases k with
  | zero => simp [fragSegment]
  | succ k => simp [fragSegment]

/-- **Last position of a segment.** Let $p_0$ be a model-checking game position and $\pi$ an
infinite sequence of positions of the totalized fragment game. For each $i$, let $\hat\pi_i$ be
$p_0$ if $\pi_i$ is an absorbing state; if $\pi_i$ is the embedded position $(\varphi, w)$ of a
fixpoint-free formula $\varphi$ and a world $w$, let $\hat\pi_i$ be the game position
$(\varphi, w, [])$, with $\varphi$ embedded as a μ-calculus formula and the empty fixpoint stack.
For all natural numbers $s$ and $k$, the segment $[\hat\pi_s, \dots, \hat\pi_{s+k}]$ has a last
position, and it is $\hat\pi_{s+k}$. -/
theorem fragSegment_playLast (p0 : GamePosition Atom World)
    (π : ωSequence (FragPos Atom World)) (start k : ℕ) :
    playLast (fragSegment p0 π start k) = some (fragToPos p0 (π (start + k))) := by
  induction k generalizing start with
  | zero => simp [fragSegment, playLast]
  | succ k ih =>
      rw [fragSegment_cons]
      rw [playLast_cons (fragSegment_ne_nil p0 π (start + 1) k)]
      rw [ih (start + 1)]
      rw [show start + 1 + k = start + (k + 1) from by omega]

/-- **Winning Verifier strategies transfer to the fragment game.** Let $M$ be a Kripke model,
$\rho$ an environment, $\sigma$ a Verifier strategy of the model-checking game on $M$,
$\varphi$ a fixpoint-free formula and $w$ a world. If $\sigma$ wins in environment $\rho$ from
the game position with formula $\varphi$, world $w$ and empty binder stack, then the positional
strategy of the even player induced by $\sigma$ wins from the embedded position $(\varphi, w)$
in the fragment game of $M$ and $\rho$.

Every play conforming to the induced strategy reaches the absorbing winning state: it cannot
reach the losing state, by the finite-play clause for $\sigma$ applied to the segment before the
first losing state, and it cannot stay among embedded positions forever, since fragment moves
strictly decrease the formula. -/
theorem fragment_bespoke_to_canonical {M : KripkeModel World Atom}
    {env : ℕ → World → Prop} {σ : Strategy M} {φ : FixFreeFormula Atom}
    {w : World}
    (hσ : StrategyWins M env σ ⟨FixFreeFormula.toMu φ, w, []⟩) :
    (fragmentGame M env).WinsFrom (fragStrategy M env σ)
      (.pos φ w) := by
  intro π hplay h0 hconf
  have hWinExists : ∃ k, π k = .win := by
    by_contra hNoWin
    push Not at hNoWin
    by_cases hLose : ∃ k, π k = .lose
    · classical
      obtain ⟨k, hkLose, hmin⟩ :
          ∃ k, π k = .lose ∧ ∀ i, i < k → π i ≠ .lose :=
        ⟨Nat.find hLose, Nat.find_spec hLose, fun i hi => Nat.find_min hLose hi⟩
      have hkPos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h
          rw [h0] at hkLose
          exact absurd hkLose (by simp)
        · exact h
      have hk' : k - 1 + 1 = k := by omega
      have hpos : ∀ i, i ≤ k - 1 → ∃ φ' w', π i = .pos φ' w' := by
        intro i hi
        have hi_lt : i < k := by omega
        have hne_lose : π i ≠ .lose := hmin i hi_lt
        have hne_win : π i ≠ .win := hNoWin i
        cases hπi : π i with
        | pos φ' w' => exact ⟨φ', w', rfl⟩
        | win => exact absurd hπi hne_win
        | lose => exact absurd hπi hne_lose
      have hseg : PlayFrom M σ ⟨FixFreeFormula.toMu φ, w, []⟩
          (fragSegment ⟨FixFreeFormula.toMu φ, w, []⟩ π 0 (k - 1)) :=
        canonical_playFrom_segment ⟨FixFreeFormula.toMu φ, w, []⟩ 0 (k - 1)
          φ w hplay hconf h0
          (fun i _ hi => hpos i (by omega))
      have hlast : playLast (fragSegment ⟨FixFreeFormula.toMu φ, w, []⟩ π 0 (k - 1)) =
          some (fragToPos ⟨FixFreeFormula.toMu φ, w, []⟩ (π (k - 1))) := by
        have h := fragSegment_playLast ⟨FixFreeFormula.toMu φ, w, []⟩ π 0 (k - 1)
        rwa [Nat.zero_add] at h
      obtain ⟨φ'', w'', hq⟩ := hpos (k - 1) (by omega)
      have hmove : FragMove M env (π (k - 1)) (π k) := by
        have hm : FragMove M env (π (k - 1)) (π (k - 1 + 1)) := hplay (k - 1)
        rwa [hk'] at hm
      rw [hq, hkLose] at hmove
      obtain ⟨hNo, hNotWin⟩ := FragMove.pos_toLose hmove
      have hcomplete : ∃ r,
          playLast (fragSegment ⟨FixFreeFormula.toMu φ, w, []⟩ π 0 (k - 1)) =
            some r ∧ NoMoves M r := by
        refine ⟨fragToPos ⟨FixFreeFormula.toMu φ, w, []⟩ (π (k - 1)), hlast, ?_⟩
        rw [hq]
        show NoMoves M ⟨FixFreeFormula.toMu φ'', w'', []⟩
        exact hNo
      obtain ⟨r, hlast', hterm⟩ := hσ.1 _ hseg hcomplete
      rw [hlast] at hlast'
      have hr : r = fragToPos ⟨FixFreeFormula.toMu φ, w, []⟩ (π (k - 1)) :=
        (Option.some.inj hlast').symm
      rw [hr, hq] at hterm
      exact hNotWin hterm
    · push Not at hLose
      have hpos : ∀ i, ∃ φ' w', π i = .pos φ' w' := by
        intro i
        cases hπi : π i with
        | pos φ' w' => exact ⟨φ', w', rfl⟩
        | win => exact absurd hπi (hNoWin i)
        | lose => exact absurd hπi (hLose i)
      have hplay0 : (fun i => fragToPos ⟨FixFreeFormula.toMu φ, w, []⟩ (π i)) 0 =
          ⟨FixFreeFormula.toMu φ, w, []⟩ := by
        show fragToPos ⟨FixFreeFormula.toMu φ, w, []⟩ (π 0) = _
        rw [h0]
        rfl
      have hsteps : ∀ n, Move M
          ((fun i => fragToPos ⟨FixFreeFormula.toMu φ, w, []⟩ (π i)) n)
          ((fun i => fragToPos ⟨FixFreeFormula.toMu φ, w, []⟩ (π i)) (n + 1)) := by
        intro n
        have hm : FragMove M env (π n) (π (n + 1)) := hplay n
        obtain ⟨φ', w', hp⟩ := hpos n
        obtain ⟨φ'', w'', hq⟩ := hpos (n + 1)
        rw [hp, hq] at hm
        have hmq : Move M ⟨FixFreeFormula.toMu φ', w', []⟩
            ⟨FixFreeFormula.toMu φ'', w'', []⟩ := FragMove.pos_move_iff hm
        show Move M (fragToPos ⟨FixFreeFormula.toMu φ, w, []⟩ (π n))
          (fragToPos ⟨FixFreeFormula.toMu φ, w, []⟩ (π (n + 1)))
        rw [hp, hq]
        exact hmq
      exact no_infinite_play_of_fixFree hplay0 hsteps
  obtain ⟨k, hkWin⟩ := hWinExists
  exact wonBy_even_of_eventually_win (fun n hn => fragPlay_eq_win_of_le hplay hkWin hn)

/-- **Moves of the totalized fragment game, by cases.** Let $M$ be a Kripke model and $e$ an
environment, and read each fixpoint-free formula $\varphi$ as a μ-calculus formula. Every move
from $a$ to $b$ in the totalized fragment game of $M$ and $e$ is of one of five kinds: $a$ and $b$
are embedded positions $(\varphi, w)$ and $(\varphi', w')$ and the model-checking game of $M$ has a
move from $(\varphi, w)$ to $(\varphi', w')$ with empty binder stacks; or $a = (\varphi, w)$, $b$ is
the winning state, and the game position $(\varphi, w)$ with empty stack has no moves and is won by
Verifier in environment $e$; or $a = (\varphi, w)$, $b$ is the losing state, and that game position
has no moves and is not won by Verifier; or $a$ and $b$ are both the winning state; or $a$ and $b$
are both the losing state. -/
theorem fragMove_cases {M : KripkeModel World Atom} {env : ℕ → World → Prop}
    {a b : FragPos Atom World} (h : FragMove M env a b) :
    (∃ φ w φ' w', a = .pos φ w ∧ b = .pos φ' w' ∧
      Move M ⟨FixFreeFormula.toMu φ, w, []⟩
        ⟨FixFreeFormula.toMu φ', w', []⟩) ∨
    (∃ φ w, a = .pos φ w ∧ b = .win ∧
      NoMoves M ⟨FixFreeFormula.toMu φ, w, []⟩ ∧
      TerminalWin M env ⟨FixFreeFormula.toMu φ, w, []⟩) ∨
    (∃ φ w, a = .pos φ w ∧ b = .lose ∧
      NoMoves M ⟨FixFreeFormula.toMu φ, w, []⟩ ∧
      ¬ TerminalWin M env ⟨FixFreeFormula.toMu φ, w, []⟩) ∨
    (a = .win ∧ b = .win) ∨ (a = .lose ∧ b = .lose) := by
  cases h with
  | pos_move h => exact Or.inl ⟨_, _, _, _, rfl, rfl, h⟩
  | toWin hNo hWin => exact Or.inr (Or.inl ⟨_, _, rfl, rfl, hNo, hWin⟩)
  | toLose hNo hLose => exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl, rfl, hNo, hLose⟩))
  | win_self => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  | lose_self => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))

/-- **Verifier's positional strategies make a game move at Verifier positions that have one.**
Let $M$ be a Kripke model, $\mathit{env}$ an environment, and $\sigma$ any positional strategy of
the even player (Verifier) in the fragment game of $M$ and $\mathit{env}$. Write
$\langle \psi, v \rangle$ for the game position with the embedding of a fixpoint-free formula
$\psi$, the world $v$ and the empty binder stack. Let $\varphi$ be a fixpoint-free formula and
$w$ a world such that the even player owns the fragment position $(\varphi, w)$ and, in the
model-checking game on $M$, $\langle \varphi, w \rangle$ has a move to some
$\langle \varphi'', w'' \rangle$. Then $\sigma$ sends $(\varphi, w)$ to a fragment position
$(\varphi', w')$ such that $\langle \varphi, w \rangle$ has a move to
$\langle \varphi', w' \rangle$; in particular $\sigma$ does not move to the absorbing state
$\mathrm{win}$ or $\mathrm{lose}$. -/
theorem canonical_next_pos {M : KripkeModel World Atom} {env : ℕ → World → Prop}
    {σ : (fragmentGame M env).PositionalStrategy Cslib.Games.Player.even}
    {φ : FixFreeFormula Atom} {w : World}
    (hown : (fragmentGame M env).owner (.pos φ w) = Cslib.Games.Player.even)
    (hExists : ∃ φ' w', Move M ⟨FixFreeFormula.toMu φ, w, []⟩
      ⟨FixFreeFormula.toMu φ', w', []⟩) :
    ∃ φ' w', σ.next (.pos φ w) = .pos φ' w' ∧
      Move M ⟨FixFreeFormula.toMu φ, w, []⟩
        ⟨FixFreeFormula.toMu φ', w', []⟩ := by
  have hmove : FragMove M env (.pos φ w) (σ.next (.pos φ w)) := σ.legal _ hown
  rcases fragMove_cases hmove with ⟨φ₁, w₁, φ₂, w₂, h1, h2, hMove⟩ |
    ⟨φ₁, w₁, h1, h2, hNo', hWin⟩ | ⟨φ₁, w₁, h1, h2, hNo', hLose'⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · injection h1 with hφ hw
    subst hφ
    subst hw
    exact ⟨φ₂, w₂, h2, hMove⟩
  · injection h1 with hφ hw
    subst hφ
    subst hw
    obtain ⟨φ', w', hq⟩ := hExists
    exact (hNo' ⟨FixFreeFormula.toMu φ', w', []⟩ hq).elim
  · injection h1 with hφ hw
    subst hφ
    subst hw
    obtain ⟨φ', w', hq⟩ := hExists
    exact (hNo' ⟨FixFreeFormula.toMu φ', w', []⟩ hq).elim
  · nomatch h1
  · nomatch h1

/-- **The lose play.** For a fixpoint-free formula $\varphi$ and a world $w$, the lose play is the
infinite sequence of positions of the fragment arena that is at the position $(\varphi, w)$ at
time $0$ and at the absorbing losing state at every later time. It is used for terminal losing
positions $(\varphi, w)$. -/
def losePlay (φ : FixFreeFormula Atom) (w : World) :
    ωSequence (FragPos Atom World) :=
  ⟨fun n => if n = 0 then FragPos.pos φ w else FragPos.lose⟩

/-- **The lose play starts at its fragment position.** For a fixpoint-free formula $\varphi$
and a world $w$, the lose play from $(\varphi, w)$ is at the fragment-arena position
$(\varphi, w)$ at time $0$. -/
theorem losePlay_zero (φ : FixFreeFormula Atom) (w : World) :
    losePlay φ w 0 = .pos φ w := rfl
/-- **The lose play stays at the losing state.** For every fixpoint-free formula $\varphi$,
world $w$ and natural number $n$, the lose play from $(\varphi, w)$ is at the losing state at
time $n + 1$. -/
theorem losePlay_succ (φ : FixFreeFormula Atom) (w : World) (n : ℕ) :
    losePlay φ w (n + 1) = .lose := by simp [losePlay]

/-- **Terminal losing positions are not won by the even player.** Let $M$ be a Kripke model,
$\mathit{env}$ an environment assigning a set of worlds to each free-variable index, $\varphi$ a
fixpoint-free formula and $w$ a world. If the model-checking game position $(\varphi, w, [])$,
with $\varphi$ embedded as a μ-calculus formula and the empty fixpoint stack, has no moves in $M$
and is not a terminal win for Verifier in $M$ under $\mathit{env}$, then the embedded position
$(\varphi, w)$ of the totalized fragment game of $M$ and $\mathit{env}$ is not in the winning
region of the even player.

The play that moves from $(\varphi, w)$ to the losing state and stays there conforms to every
strategy of the even player and is won by the odd player. -/
theorem fragPos_not_mem_winningRegion_of_terminal_lose {M : KripkeModel World Atom}
    {env : ℕ → World → Prop} {φ : FixFreeFormula Atom} {w : World}
    (hNo : NoMoves M ⟨FixFreeFormula.toMu φ, w, []⟩)
    (hLose : ¬ TerminalWin M env ⟨FixFreeFormula.toMu φ, w, []⟩) :
    (.pos φ w : FragPos Atom World) ∉
      (fragmentGame M env).WinningRegion Cslib.Games.Player.even := by
  rintro ⟨σ, hσ⟩
  have hPlay : (fragmentGame M env).IsPlay (losePlay φ w) := by
    intro i
    cases i with
    | zero =>
        have h1 : losePlay φ w 1 = .lose := losePlay_succ φ w 0
        show FragMove M env (losePlay φ w 0) (losePlay φ w 1)
        rw [losePlay_zero, h1]
        exact FragMove.toLose hNo hLose
    | succ n =>
        show FragMove M env (losePlay φ w (n + 1)) (losePlay φ w (n + 1 + 1))
        rw [losePlay_succ φ w n, losePlay_succ φ w (n + 1)]
        exact FragMove.lose_self
  have hConf : Cslib.Games.ParityGame.Conforms σ (losePlay φ w) := by
    intro i hi
    cases i with
    | zero =>
        rw [losePlay_zero] at hi ⊢
        have h1 : losePlay φ w 1 = .lose := losePlay_succ φ w 0
        rw [h1]
        have hmove := σ.legal _ hi
        rcases fragMove_cases hmove with ⟨φ₁, w₁, φ₂, w₂, h1', h2, hMove⟩ |
          ⟨φ₁, w₁, h1', h2, hNo', hWin⟩ | ⟨φ₁, w₁, h1', h2, hNo', hLose'⟩ |
          ⟨h1', h2⟩ | ⟨h1', h2⟩
        · injection h1' with hφ hw
          subst hφ
          subst hw
          exact (hNo ⟨FixFreeFormula.toMu φ₂, w₂, []⟩ hMove).elim
        · injection h1' with hφ hw
          subst hφ
          subst hw
          exact (hLose hWin).elim
        · exact h2.symm
        · nomatch h1'
        · nomatch h1'
    | succ n =>
        rw [losePlay_succ φ w n] at hi ⊢
        have h1 : losePlay φ w (n + 1 + 1) = .lose := losePlay_succ φ w (n + 1)
        rw [h1]
        have hmove := σ.legal _ (show (fragmentGame M env).owner
            (FragPos.lose : FragPos Atom World) = Cslib.Games.Player.even from rfl)
        rcases fragMove_cases hmove with ⟨φ₁, w₁, φ₂, w₂, h1', h2, hMove⟩ |
          ⟨φ₁, w₁, h1', h2, hNo', hWin⟩ | ⟨φ₁, w₁, h1', h2, hNo', hLose'⟩ |
          ⟨h1', h2⟩ | ⟨h1', h2⟩
        · nomatch h1'
        · nomatch h1'
        · nomatch h1'
        · nomatch h1'
        · exact h2.symm
  have hEven := hσ _ hPlay rfl hConf
  have hOdd : (fragmentGame M env).WonBy Cslib.Games.Player.odd (losePlay φ w) :=
    wonBy_odd_of_eventually_lose (π := losePlay φ w) (k0 := 1) (fun n hn => by
      cases n with
      | zero => exact absurd hn (by decide)
      | succ m => exact losePlay_succ φ w m)
  exact Cslib.Games.ParityGame.not_wonBy_and_wonBy_opponent
    Cslib.Games.Player.even (losePlay φ w) ⟨hEven, hOdd⟩

/-- **The fragment game's winning region is contained in Wins.** Let $M$ be a Kripke model,
$\rho$ an environment, $\varphi$ a fixpoint-free formula and $w$ a world. If the embedded
position $(\varphi, w)$ lies in the winning region of the even player in the fragment game of
$M$ and $\rho$, then the backward-induction winning condition $\mathrm{Wins}_M(\varphi, w)$
holds.

The proof is by induction on $\varphi$, using that the winning region is closed under the
opponent's moves and under the moves of a winning strategy, so no strategy composition is
needed. -/
theorem fragment_canonical_to_wins (M : KripkeModel World Atom)
    (env : ℕ → World → Prop) (φ : FixFreeFormula Atom) (w : World)
    (h : (.pos φ w : FragPos Atom World) ∈
      (fragmentGame M env).WinningRegion Cslib.Games.Player.even) :
    Wins M φ w := by
  revert h
  induction φ generalizing w with
  | atom a =>
      intro h
      by_cases hval : M.valuation w a
      · exact hval
      · have hNo : NoMoves M (⟨.atom a, w, []⟩ : GamePosition Atom World) := by
          intro q hq
          cases hq
        have hLose : ¬ TerminalWin M env (⟨.atom a, w, []⟩ : GamePosition Atom World) :=
          hval
        exact (fragPos_not_mem_winningRegion_of_terminal_lose hNo hLose h).elim
  | natom a =>
      intro h
      by_cases hval : M.valuation w a
      · have hNo : NoMoves M (⟨.natom a, w, []⟩ : GamePosition Atom World) := by
          intro q hq
          cases hq
        have hLose : ¬ TerminalWin M env (⟨.natom a, w, []⟩ : GamePosition Atom World) :=
          fun hn => hn hval
        exact (fragPos_not_mem_winningRegion_of_terminal_lose hNo hLose h).elim
      · exact hval
  | bot =>
      intro h
      have hNo : NoMoves M (⟨.bot, w, []⟩ : GamePosition Atom World) := by
        intro q hq
        cases hq
      have hLose : ¬ TerminalWin M env (⟨.bot, w, []⟩ : GamePosition Atom World) :=
        fun hn => hn
      exact (fragPos_not_mem_winningRegion_of_terminal_lose hNo hLose h).elim
  | top => intro _; trivial
  | and φ ψ ihφ ihψ =>
      intro h
      refine ⟨?_, ?_⟩
      · apply ihφ
        exact Cslib.Games.ParityGame.move_mem_winningRegion
          (G := fragmentGame M env) (p := Cslib.Games.Player.even) h rfl
          (FragMove.pos_move Move.andLeft)
      · apply ihψ
        exact Cslib.Games.ParityGame.move_mem_winningRegion
          (G := fragmentGame M env) (p := Cslib.Games.Player.even) h rfl
          (FragMove.pos_move Move.andRight)
  | or φ ψ ihφ ihψ =>
      intro h
      obtain ⟨σ, hσ⟩ := h
      have hown : (fragmentGame M env).owner
          (FragPos.pos (.or φ ψ) w) =
            Cslib.Games.Player.even := rfl
      have hmem := Cslib.Games.ParityGame.next_mem_winningRegion
        (G := fragmentGame M env) (p := Cslib.Games.Player.even) hσ hown
      obtain ⟨φ', w', hq, hMove⟩ := canonical_next_pos hown ⟨φ, w, Move.orLeft⟩
      rw [hq] at hmem
      obtain hEq | hEq := Move.or_cases hMove
      · have hToMu : FixFreeFormula.toMu φ' = FixFreeFormula.toMu φ := by
          simp only [Prod.mk.injEq] at hEq
          exact hEq.1
        have hφ : φ' = φ := FixFreeFormula.toMu_injective hToMu
        have hw : w' = w := by
          simp only [Prod.mk.injEq] at hEq
          exact hEq.2.1
        rw [hφ, hw] at hmem
        exact Or.inl (ihφ w hmem)
      · have hToMu : FixFreeFormula.toMu φ' = FixFreeFormula.toMu ψ := by
          simp only [Prod.mk.injEq] at hEq
          exact hEq.1
        have hφ : φ' = ψ := FixFreeFormula.toMu_injective hToMu
        have hw : w' = w := by
          simp only [Prod.mk.injEq] at hEq
          exact hEq.2.1
        rw [hφ, hw] at hmem
        exact Or.inr (ihψ w hmem)
  | box φ ih =>
      intro h v hv
      apply ih
      exact Cslib.Games.ParityGame.move_mem_winningRegion
        (G := fragmentGame M env) (p := Cslib.Games.Player.even) h rfl
        (FragMove.pos_move (Move.box hv))
  | dia φ ih =>
      intro h
      obtain ⟨v, hv⟩ : ∃ v, M.rel w v := by
        by_contra hnsucc
        push Not at hnsucc
        have hNo : NoMoves M (⟨FixFreeFormula.toMu (.dia φ), w, []⟩ :
            GamePosition Atom World) := by
          intro q hq
          simp only [FixFreeFormula.toMu] at hq
          cases hq with
          | dia hv => exact hnsucc _ hv
        have hLose : ¬ TerminalWin M env (⟨FixFreeFormula.toMu (.dia φ), w, []⟩ :
            GamePosition Atom World) := fun hn => hn
        exact fragPos_not_mem_winningRegion_of_terminal_lose hNo hLose h
      obtain ⟨σ, hσ⟩ := h
      have hown : (fragmentGame M env).owner
          (FragPos.pos (.dia φ) w) =
            Cslib.Games.Player.even := rfl
      have hmem := Cslib.Games.ParityGame.next_mem_winningRegion
        (G := fragmentGame M env) (p := Cslib.Games.Player.even) hσ hown
      obtain ⟨φ', w', hq, hMove⟩ := canonical_next_pos hown ⟨φ, v, Move.dia hv⟩
      rw [hq] at hmem
      obtain ⟨v', hv', hEq⟩ := Move.dia_cases hMove
      have hToMu : FixFreeFormula.toMu φ' = FixFreeFormula.toMu φ := by
        simp only [Prod.mk.injEq] at hEq
        exact hEq.1
      have hφ : φ' = φ := FixFreeFormula.toMu_injective hToMu
      have hw : w' = v' := by
        simp only [Prod.mk.injEq] at hEq
        exact hEq.2.1
      rw [hφ, hw] at hmem
      exact ⟨v', hv', ih v' hmem⟩

/-- **Wins is the winning region of the fragment game.** Let $M$ be a Kripke model, $\rho$ an
environment, $\varphi$ a fixpoint-free formula and $w$ a world. Then the backward-induction
winning condition $\mathrm{Wins}_M(\varphi, w)$ holds if and only if the embedded position
$(\varphi, w)$ lies in the winning region of the even player in the fragment game of $M$ and
$\rho$. -/
theorem fragmentWins_iff_winningRegion (M : KripkeModel World Atom)
    (env : ℕ → World → Prop) (φ : FixFreeFormula Atom) (w : World) :
    Wins M φ w ↔ (.pos φ w : FragPos Atom World) ∈
      (fragmentGame M env).WinningRegion Cslib.Games.Player.even := by
  constructor
  · intro hW
    obtain ⟨σ, hσ⟩ := wins_implies_verifierWins M env φ w hW
    exact ⟨fragStrategy M env σ, fragment_bespoke_to_canonical hσ⟩
  · intro h
    exact fragment_canonical_to_wins M env φ w h

end Game
end MuCalculus
end Modal
end Cslib
