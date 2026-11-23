/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EQUILIBRIUM POINT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [AN15] EQUILIBRIUM
POINT;
S. Sahni, "Computationally related problems", SIAM Journal on Computing 3 (1974),
262-279, doi:10.1137/0203021, Section 2.4, Theorem 2.4.1 (existence of an
equilibrium point of an n-person game with polynomial payoffs is NP-complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.MvPolynomial.Eval
public import MathlibExt.GameTheory.StrategicGame

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EquilibriumPoint

/-!
# EQUILIBRIUM POINT is NP-complete

INSTANCE: a set `X = {x₁, ..., xₙ}` of variables, a collection `{Fᵢ : 1 ≤ i ≤ n}` of product
polynomials over `X` and the integers, and a finite range-set `Mᵢ ⊆ ℤ` for `1 ≤ i ≤ n`.
QUESTION: is there a sequence `y₁, ..., yₙ` of integers, with `yᵢ ∈ Mᵢ`, such that for
`1 ≤ i ≤ n` and all `y ∈ Mᵢ`,
`Fᵢ(y₁, ..., yᵢ₋₁, yᵢ, yᵢ₊₁, ..., yₙ) ≥ Fᵢ(y₁, ..., yᵢ₋₁, y, yᵢ₊₁, ..., yₙ)`?

This is the existence of a pure Nash equilibrium of the `n`-player game `game` in which player
`i` chooses `xᵢ ∈ Mᵢ` and receives payoff `Fᵢ`. The question is stated with the repository's
`MathlibExt.GameTheory.StrategicGame.IsNash`, which by `isNash_iff_update_le` says exactly that
no unilateral deviation `Function.update σ i t` raises the deviator's payoff. Payoffs are the
integer values of the `Fᵢ`, cast to `ℝ` as `StrategicGame` requires (the cast preserves `≤`).

Players and variables are indexed `0, ..., n - 1`. A product polynomial is a polynomial given
as a product of polynomials (Garey and Johnson use the term the same way in [AN11] NUMBER OF
ROOTS FOR A PRODUCT POLYNOMIAL), here `productPoly`, a product of factors `factorPoly`, each a
sum of integer multiples of monomials. A monomial is given by the list of its variables, each
listed as often as its exponent, so exponents are written in unary and a payoff is evaluated in
polynomial time; Sahni's reduction uses range-sets `{0, 1}`, on which exponents are immaterial.
Polynomials and their evaluation are Mathlib's `MvPolynomial ℕ ℤ` and `MvPolynomial.eval`; a
strategy profile `σ` assigns to player `i : Fin n` an element of `Mᵢ` and is evaluated at
`xᵢ = σ i` (`assignment`; no variable has an index `≥ n`). Integers are given as pairs of
naturals `(positive part, negative part)` and each range-set as a finite list of integers. A
profile exists only when every `Mᵢ` is nonempty; an empty `Mᵢ` leaves no sequence `y` with
`yᵢ ∈ Mᵢ`, so such instances are no-instances, as in the source.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open MvPolynomial

/-- A monomial term: an integer coefficient `(positive part, negative part)` and the list of
variables of the monomial, each repeated as often as its exponent. -/
abbrev MonomialTerm := (ℕ × ℕ) × List ℕ

/-- The polynomial `∑ (cₖ⁺ - cₖ⁻) · ∏ x_v` of a list of monomial terms. -/
noncomputable def factorPoly (f : List MonomialTerm) : MvPolynomial ℕ ℤ :=
  (f.map fun t => C ((t.1.1 : ℤ) - t.1.2) * (t.2.map X).prod).sum

/-- The product polynomial of a list of factors: the product of their polynomials. -/
noncomputable def productPoly (F : List (List MonomialTerm)) : MvPolynomial ℕ ℤ :=
  (F.map factorPoly).prod

/-- An instance: the number `n` of variables (and players), the product polynomials
`F₀, ..., Fₙ₋₁` as lists of factors, and the range-sets `M₀, ..., Mₙ₋₁` as lists of integers
`(positive part, negative part)`. -/
abbrev EquilibriumPointInstance := ℕ × List (List (List MonomialTerm)) × List (List (ℕ × ℕ))

/-- The payoff polynomial `Fᵢ`. -/
noncomputable def payoffPoly (inst : EquilibriumPointInstance) (i : ℕ) : MvPolynomial ℕ ℤ :=
  productPoly (inst.2.1.getD i [])

/-- The range-set `Mᵢ`, as a list of integers. -/
def rangeSet (inst : EquilibriumPointInstance) (i : ℕ) : List ℤ :=
  (inst.2.2.getD i []).map fun q => (q.1 : ℤ) - q.2

/-- Well-formedness of an instance: there are exactly `n` product polynomials and `n`
range-sets, and every variable occurring in a monomial is one of `x₀, ..., xₙ₋₁`. -/
def WellFormed (inst : EquilibriumPointInstance) : Prop :=
  inst.2.1.length = inst.1 ∧ inst.2.2.length = inst.1 ∧
    ∀ F ∈ inst.2.1, ∀ f ∈ F, ∀ t ∈ f, ∀ v ∈ t.2, v < inst.1

/-- The strategies of player `i`: the elements of the range-set `Mᵢ`. -/
abbrev Strategy (inst : EquilibriumPointInstance) (i : Fin inst.1) : Type :=
  {z : ℤ // z ∈ rangeSet inst i}

/-- The values of the variables at a strategy profile: `xᵢ = σ i` for `i < n` (larger indices
do not occur in a well-formed instance and get `0`). -/
def assignment (inst : EquilibriumPointInstance) (σ : ∀ i, Strategy inst i) : ℕ → ℤ :=
  fun v => if h : v < inst.1 then (σ ⟨v, h⟩).1 else 0

/-- The game of the instance: players `Fin n`, strategies of player `i` the elements of `Mᵢ`,
and payoff of player `i` the value of `Fᵢ` at the profile. Building it needs every `Mᵢ`
nonempty (`hne`), as `StrategicGame` requires. -/
noncomputable def game (inst : EquilibriumPointInstance)
    (hne : ∀ i, Nonempty (Strategy inst i)) :
    MathlibExt.GameTheory.StrategicGame (Fin inst.1) (Strategy inst) where
  payoff i σ := (eval (assignment inst σ) (payoffPoly inst i) : ℝ)
  strategy_nonempty := hne

/-- An equilibrium point exists: some profile `σ` (`σ i ∈ Mᵢ` for every player `i`) is a pure
Nash equilibrium of the game of the instance; the game is built with the nonemptiness of the
range-sets that `σ` itself witnesses. -/
def EquilibriumPointFeasible (inst : EquilibriumPointInstance) : Prop :=
  ∃ σ : ∀ i, Strategy inst i, (game inst fun i => ⟨σ i⟩).IsNash σ

open Classical in
/-- EQUILIBRIUM POINT as a decision problem over bitstrings. -/
noncomputable def equilibriumPointDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EquilibriumPointInstance) x with
  | some i => decide (WellFormed i ∧ EquilibriumPointFeasible i)
  | none => false

/-- **EQUILIBRIUM POINT is NP-complete.** Source: Garey and Johnson (1979), [AN15];
Sahni (1974), Theorem 2.4.1. -/
public theorem_wanted equilibriumPoint_npComplete :
    equilibriumPointDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L equilibriumPointDec

end MetaMathlibExt.Complexity.NPComplete.EquilibriumPoint
