/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Negligible
public import Mathlib.Tactic.DeriveFintype

/-!
# Emulation with one exchange of bits

A finite-register special case of the *shape* of Canetti's UC4SS definitions, not an
interpreter for all polynomial-time interactive machines. There are three wired roles: the
environment (0), intermediary (1) and sole main party (2). These labels identify endpoints in
the fixed schedule, not three external identities in the UC4SS sense. There an external identity
is absent from the protocol but has a subroutine in it. Here there is no sender-ID field or
choice of apparent sender. Each directed wire carries one bit. The environment chooses
its input to 2 and command to 1; 1 writes to the backdoor of 2; 2 returns an API output to 0
and a backdoor output to 1; 1 reports to 0, which outputs one bit. The two return handlers
are finite tables chosen during the respective first activations. There is no other schedule,
external ID translation, spawning, corruption or subroutine composition.

Programs below are uniform finite syntax, not one circuit or arbitrary oracle per security
parameter. The parameter is supplied in unary to a public loop controller. A fixed polynomial
in that parameter specifies a loop count or prefix-read length. Count *unrolled* table lookups,
coin draws and scanned cells, not the cost of a Lean evaluation. Copying fixed-width registers,
routing and loop indexing are wiring, not charged gates. This is a polynomial-size schedule
uniformly generated from fixed syntax; it does not identify gate counts with steps on a UC RAM.
An auxiliary string of any finite length is presented read-only to 0; it is not copied in its
entirety at unit cost. Each scan starts at the first cell and pads with an end marker. No gate
has an infinite table or receives the whole string, a clock function, or the parameter as advice.

Source: R. Canetti, *Universally Composable Security: A Tutorial*, UC/EasyUC Summer School,
Boston University, 2025, <https://www.bu.edu/riscs/files/2025/08/Canetti.pdf>, slides 15–24
(static execution, resources and emulation), 25–27 (ideal wrappers), 50–53 (dummy reduction).
The finite language, fixed schedule and gate accounting here are additional restrictions.
-/

@[expose] public section

namespace Cslib.Crypto.OneExchange

open Cslib.Crypto.Framework
open scoped Cslib.Probability.PMF

/-- A uniform finite-register program. A primitive table has fixed finite domain and codomain;
`coin` samples a fresh fair bit. Programs compose sequentially, can retain the input and can
iterate a body a fixed polynomial number of times in the unary security parameter. Only an open
program can scan the auxiliary tape; a closed subprogram can be embedded in an open one. -/
inductive Program : Bool → Type → Type → Type 1 where
  | table {v α β} [Fintype α] [Fintype β] (f : α → β) : Program v α β
  | coin {v} : Program v Unit Bool
  | seq {v α β γ} (first : Program v α β) (next : Program v β γ) : Program v α γ
  | keep {v α β} (body : Program v α β) : Program v α (α × β)
  | loop {v α} (count : Polynomial ℕ) (body : Program v α α) : Program v α α
  | scan {α} [Fintype α] (count : Polynomial ℕ) (step : α → Option Bool → α) : Program true α α
  | embed {α β} (body : Program false α β) : Program true α β

/-- The charged gate count of a program is a polynomial in the unary parameter. Tables and fresh
coins cost one, sequential costs add and iteration multiplies by the loop count. A scan spends
one lookup per cell including padding. Wire copies and embedding closed code are free. -/
noncomputable def Program.clock {v α β} : Program v α β → Polynomial ℕ
  | @Program.table _ _ _ _ _ _ | .coin => 1
  | .seq f g => f.clock + g.clock
  | .keep f | .embed f => f.clock
  | .loop p f => p * f.clock
  | @Program.scan _ _ p _ => p

/-- A read-only scan makes exactly the specified number of updates, supplying the next bit or
an end marker if there is none. In particular, a zero budget does not inspect the string. -/
def scanPrefix {α : Type} (step : α → Option Bool → α) : ℕ → List Bool → α → α
  | 0, _, a => a
  | k + 1, z, a => scanPrefix step k z.tail (step a z.head?)

/-- The output law of a finite-register program on parameter $k$, auxiliary bit string $z$ and
register input $a$. Sequential subprograms and successive iterations sample fresh coins. Closed
programs cannot scan $z$; embedding one supplies the empty tape. -/
noncomputable def Program.eval {v α β} (k : ℕ) (z : List Bool) : Program v α β → α → PMF β
  | @Program.table _ _ _ _ _ f, a => PMF.pure (f a)
  | .coin, _ => fairCoin
  | .seq f g, a => (f.eval k z a).bind (g.eval k z)
  | .keep f, a => (f.eval k z a).map (a, ·)
  | .loop p f, a => (fun μ : PMF _ => μ.bind (f.eval k z))^[p.eval k] (PMF.pure a)
  | @Program.scan _ _ p step, a => PMF.pure (scanPrefix step (p.eval k) z a)
  | .embed f, a => f.eval k [] a
termination_by structural c => c

/-- A first activation of the environment supplies one API input bit, one command bit for the
intermediary, and a private output table taking the API reply and the intermediary's report. -/
structure Plan where
  input : Bool
  command : Bool
  observe : Bool → Bool → Bool
  deriving Fintype

abbrev Environment := Program true Unit Plan
abbrev Intermediary := Program false Bool (Bool × (Bool → Bool))
abbrev Protocol := Program false (Bool × Bool) (Bool × Bool)

/-- **One-exchange execution law.** There are three wired roles, labelled 0 (environment),
1 (intermediary) and 2 (main party). Messages contain no address or apparent-sender field.
The environment chooses an API input to party 2, a command to intermediary 1 and a private
table on the two return bits. Only it reads
$z$. The intermediary's closed program turns the command into a backdoor input and a private
return table. The party's closed program takes the API and backdoor inputs and replies on both
ports. Apply the intermediary's return table to the backdoor reply and the environment's table
to the API reply and that report. The result is a probability mass function on the final bit;
all three programs draw independent coins.

Source: one-exchange specialization of R. Canetti, *Universally Composable Security: A Tutorial*,
UC/EasyUC Summer School (2025), slides 17 and 20–21. -/
noncomputable def exec (π : Protocol) (E : Environment) (A : Intermediary) (k : ℕ)
    (z : List Bool) : PMF Bool :=
  (E.eval k z ()).bind fun e => (A.eval k [] e.command).bind fun a =>
    (π.eval k [] (e.input, a.1)).map fun r => e.observe r.1 (a.2 r.2)

/-- Two bit ensembles are close if the supremum over *all* finite auxiliary strings of their
absolute difference in probabilities of true is negligible as a function of the parameter.
This compares only the output, not the entire view or the messages. -/
def Close (X Y : ℕ → List Bool → PMF Bool) : Prop :=
  NegligibleAdv (fun k => ⨆ z, advantage (X k z) (Y k z))

/-- For bit laws $X(k,z)$ and $Y(k,z)$ let $a(k,z)$ be the absolute difference in their
probabilities of true. The function $k\mapsto\sup_{z\in\{0,1\}^*}a(k,z)$ is negligible if and
only if for each exponent $c\in\mathbb N$ there exists a threshold $K\in\mathbb N$ such that
$a(k,z)\le 1/k^c$ for every $k\ge K$ and every finite bit string $z$.
The same $K$ works for all $z$; it may be increased to at least one. -/
theorem close_iff {X Y : ℕ → List Bool → PMF Bool} : Close X Y ↔
    ∀ c : ℕ, ∃ K : ℕ, ∀ k ≥ K, ∀ z, advantage (X k z) (Y k z) ≤ 1 / (k : ℝ) ^ c := by
  rw [Close, negligibleAdv_iff_eventually_le]
  constructor
  · intro h c
    obtain ⟨K, hK⟩ := h c
    refine ⟨K, fun k hk z => (le_ciSup (f := fun w => advantage (X k w) (Y k w)) ?_ z).trans
      (hK k hk)⟩
    exact ⟨1, by rintro _ ⟨w, rfl⟩; exact advantage_le_one _ _⟩
  · intro h c
    obtain ⟨K, hK⟩ := h c
    exact ⟨K, fun k hk => ciSup_le (hK k hk)⟩

/-- **Qualitative one-exchange emulation.** For each fixed closed intermediary program there is
one fixed closed simulator program such that every fixed open environment yields close final
bit ensembles. All programs have polynomial gate clocks. Neither the environment, the parameter
nor the auxiliary string is an argument to the choice of simulator.

Source: one-exchange specialization of R. Canetti, *Universally Composable Security: A Tutorial*,
UC/EasyUC Summer School (2025), slides 22–23. -/
def Emulates (π φ : Protocol) : Prop :=
  ∀ A : Intermediary, ∃ S : Intermediary, ∀ E : Environment, Close (exec π E A) (exec φ E S)

/-- **Quantitative one-exchange emulation.** In charged gates, for each intermediary and upper clock
$t_A(k)$ for its whole run (including the return lookup), choose one simulator whose whole clock
is at most $\delta(t_A(k))$ at every parameter. For every environment, parameter, upper budget
$t_E$ for that environment (including the output lookup), and auxiliary string, the statistical
distance of the final **bit** laws must be strictly less than $\varepsilon(t_E)$. No monotonicity
of the two resource functions is assumed; the budget witnesses are not fed to any program.

Source: one-exchange specialization of R. Canetti, *Universally Composable Security: A Tutorial*,
UC/EasyUC Summer School (2025), slide 24. -/
def EmulatesWithin (δ : ℕ → ℕ) (ε : ℕ → ℝ) (π φ : Protocol) : Prop :=
  ∀ (A : Intermediary) (tA : ℕ → ℕ), (∀ k, A.clock.eval k + 1 ≤ tA k) →
    ∃ S : Intermediary, (∀ k, S.clock.eval k + 1 ≤ δ (tA k)) ∧
      ∀ (E : Environment) (k tE : ℕ), E.clock.eval k + 1 ≤ tE → ∀ z,
        dist (exec π E A k z) (exec φ E S k z) < ε tE

/-- **One-exchange quantitative transitivity.** Suppose $\pi$ emulates $\phi$ with overhead
$\delta_1$ and slack $\varepsilon_1$, and $\phi$ emulates $\psi$ with overhead $\delta_2$ and
slack $\varepsilon_2$. Then $\pi$ emulates $\psi$: for every intermediary with upper clock
$t_A$, the final simulator costs at most $\delta_2(\delta_1(t_A(k)))$ at each parameter $k$.
For every environment with budget $t_E$ at $k$ and every auxiliary input, the output-bit total
variation distance is strictly less than $\varepsilon_1(t_E)+\varepsilon_2(t_E)$. This chains
comparisons of bit laws; it is not a theorem about replacing a subroutine inside a protocol. -/
theorem EmulatesWithin.trans {δ₁ δ₂ : ℕ → ℕ} {ε₁ ε₂ : ℕ → ℝ} {π φ ψ : Protocol}
    (h₁ : EmulatesWithin δ₁ ε₁ π φ) (h₂ : EmulatesWithin δ₂ ε₂ φ ψ) :
    EmulatesWithin (δ₂ ∘ δ₁) (ε₁ + ε₂) π ψ := by
  intro A tA hA
  obtain ⟨S, hS, hπ⟩ := h₁ A tA hA
  obtain ⟨T, hT, hφ⟩ := h₂ S (δ₁ ∘ tA) hS
  exact ⟨T, hT, fun E k tE hE z => (dist_triangle _ (exec φ E S k z) _).trans_lt
    (add_lt_add (hπ E k tE hE z) (hφ E k tE hE z))⟩

/-- **One-exchange ideal protocol.** The trusted transition takes the API and backdoor inputs and
returns an API reply and a backdoor reply. The sole main party (role 2) forwards its API input
to the trusted box and its API output back to ID 0. The peer wire connects ID 1 directly to the
box. At the level of pairs of port values these are two identity tables, one on each side of
the transition. They cost two table lookups in the protocol, not in the simulator.

Source: single-party specialization of R. Canetti, *Universally Composable Security: A Tutorial*,
UC/EasyUC Summer School (2025), slides 25–26. -/
def idealProtocol (box : Program false (Bool × Bool) (Bool × Bool)) : Protocol :=
  ((Program.table id).seq box).seq (.table id)

/-- Fix a box $B$ in the one-exchange model. For every environment $E$, intermediary $S$,
parameter $k$ and auxiliary string $z$, the final-bit law with $B$ between the two identity
relay tables of its ideal protocol equals the law with the same box run bare:
$X_{I_B,E,S}(k,z)=X_{B,E,S}(k,z)$. This is a wiring identity, not a claim that an arbitrary
protocol realizes $B$. -/
theorem exec_idealProtocol (box : Protocol) (E : Environment) (S : Intermediary) (k : ℕ)
    (z : List Bool) : exec (idealProtocol box) E S k z = exec box E S k z := by
  simp [exec, idealProtocol, Program.eval, PMF.bind_pure]

/-- **One-exchange realization.** A protocol realizes a central bit functionality when it
qualitatively emulates the ideal protocol with the forwarding party, not an environment given
access to the functionality's internal state.

Source: one-exchange specialization of R. Canetti, *Universally Composable Security: A Tutorial*,
UC/EasyUC Summer School (2025), slides 26–27. -/
def Realizes (π : Protocol) (box : Program false (Bool × Bool) (Bool × Bool)) : Prop :=
  Emulates π (idealProtocol box)

/-- On the one-party wiring, the dummy sends the command bit to the sole backdoor and returns
the backdoor reply unchanged. Both peer identities are implicit in these fixed wires. -/
def dummy : Intermediary := .table fun m => (m, id)

-- Put A in the environment. Its return table becomes part of the environment's observation.
private def absorb (E : Environment) (A : Intermediary) : Environment :=
  E.seq <| (Program.keep ((Program.table Plan.command).seq (.embed A))).seq <|
    .table fun (e, a) => ⟨e.input, a.1, fun y v => e.observe y (a.2 v)⟩

-- Put A outside the dummy's simulator. The two return tables compose in reverse order.
private def wrap (A D : Intermediary) : Intermediary :=
  A.seq <| (Program.keep ((Program.table Prod.fst).seq D)).seq <|
    .table fun (a, s) => (s.1, a.2 ∘ s.2)

private theorem exec_absorb (π : Protocol) (E : Environment) (A D : Intermediary)
    (k : ℕ) (z : List Bool) : exec π (absorb E A) D k z = exec π E (wrap A D) k z := by
  simp [exec, absorb, wrap, Program.eval, PMF.bind_bind, PMF.bind_map, Function.comp_def]

private theorem exec_absorb_dummy (π : Protocol) (E : Environment) (A : Intermediary)
    (k : ℕ) (z : List Bool) : exec π (absorb E A) dummy k z = exec π E A k z := by
  simp [exec, absorb, dummy, Program.eval, PMF.bind_bind, PMF.bind_map]

/-- **Dummy sufficiency for one exchange.** Testing the two-way forwarding intermediary against
every environment is equivalent to testing all intermediaries. The enlarged environment runs the
real intermediary internally; the new simulator composes that intermediary with the dummy's
simulator. Both are programs of the same uniform polynomial-clock language. This equivalence is
qualitative; the extra gates need not preserve numerical overhead or slack.

Source: fixed-schedule instance of the reduction in R. Canetti, *Universally Composable Security:
A Tutorial*, UC/EasyUC Summer School (2025), slides 50–53. -/
theorem emulates_iff_dummy (π φ : Protocol) : Emulates π φ ↔
    ∃ D : Intermediary, ∀ E : Environment, Close (exec π E dummy) (exec φ E D) := by
  refine ⟨fun h => h dummy, ?_⟩
  rintro ⟨D, hD⟩ A
  refine ⟨wrap A D, fun E => ?_⟩
  have h := hD (absorb E A)
  simpa only [close_iff, exec_absorb_dummy, exec_absorb (D := D)] using h

end Cslib.Crypto.OneExchange
