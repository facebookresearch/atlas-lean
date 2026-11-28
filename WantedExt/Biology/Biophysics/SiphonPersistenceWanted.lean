/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Siphons, semiflows and persistence of chemical reaction networks

A chemical reaction network on a finite set `S` of species has reactions `r` (indexed by `ρ`)
`∑_j α_{rj} S_j → ∑_j β_{rj} S_j` with natural-number stoichiometric coefficients, and
stoichiometry matrix `Γ_{jr} = β_{rj} - α_{rj}`. Its concentrations evolve by `Ṡ = Γ R(S)` in the
closed nonnegative orthant `𝒪₊`, for reaction rates `R(S)` such that each `R_r` is real analytic
on an open set containing `𝒪₊`, depends only on the concentrations of the reactants of `r`, is
nondecreasing in each reactant concentration, vanishes when some reactant concentration is zero
and is positive when all reactant concentrations are positive (mass-action kinetics is a special
case). The network is **persistent** if for every initial state in the interior of `𝒪₊` the
`ω`-limit set of its solution does not meet the boundary of `𝒪₊`.

In the species-reaction Petri net, `r` is an output reaction of species `j` if `α_{rj} > 0` and an
input reaction of `j` if `β_{rj} > 0`. A **siphon** is a nonempty set `Σ` of species such that
every input reaction of a species in `Σ` is an output reaction of some species in `Σ`. A
**P-semiflow** is a nonzero nonnegative row vector `c` with `c Γ = 0`; its support is
`{j : c_j > 0}`. The Petri net is **conservative** if there is a P-semiflow with all entries
positive, and **consistent** if there is a vector `v` with all entries positive and `Γ v = 0`.

**Theorem 1** (Angeli–De Leenheer–Sontag 2007). A conservative and persistent network has a
consistent associated Petri net.

**Theorem 2** (Angeli–De Leenheer–Sontag 2007). If the associated Petri net is conservative and
each siphon contains the support of a P-semiflow, then the network is persistent.

Solutions are taken on `[0, ∞)` and in `𝒪₊`, as in the source (where `ω(S₀)` is only considered
for solutions defined for all `t ≥ 0`); conservativity makes them bounded. The orthant `𝒪₊` is
`Set.Ici 0` in `S → ℝ`. The network structure is that of
`MathlibExt.Dynamics.PolynomialNetworks.Deficiency`, and siphons are the finite sets of species of
`WantedExt.Biology.Biophysics.SiphonPrimeDecompositionWanted.IsSiphon`.

Sources: D. Angeli, P. De Leenheer, E. D. Sontag, "A Petri net approach to the study of
persistence in chemical reaction networks", Math. Biosci. 210 (2007) 598–618, Sections 2–5,
Definitions of persistence, P-semiflow, T-semiflow and siphon, Theorems 1 and 2
(arXiv:q-bio/0608019).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Dynamics.PolynomialNetworks.Deficiency
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import WantedExt.Biology.Biophysics.SiphonPrimeDecompositionWanted

@[expose] public section

namespace WantedExt.Biology.Biophysics.SiphonPersistenceWanted

open MathlibExt.Biology.Dynamics.ComplexBalanced Filter Topology

variable {S ρ : Type*} (N : ReactionNetwork S ρ)

/-- The stoichiometry matrix entry `Γ_{jr} = β_{rj} - α_{rj}`, where `α_{rj} = src r j` and
`β_{rj} = prod r j` are the coefficients of the species `j` in the reactant and product complexes
of the reaction `r` of `N`. -/
def stoich (j : S) (r : ρ) : ℝ :=
  (N.prod r j : ℝ) - N.src r j

/-- Admissible reaction rates `R : ℝ^S → ℝ^ρ` in the sense of the source: each `R_r` is real
analytic on an open set containing the closed nonnegative orthant `𝒪₊ = Set.Ici 0`, depends only
on the reactants of `r`, is nondecreasing
in each reactant concentration on `𝒪₊`, vanishes on `𝒪₊` when a reactant concentration is zero
and is positive on `𝒪₊` when all reactant concentrations are positive. -/
structure IsAdmissibleRate [Fintype S] [DecidableEq S] (R : (S → ℝ) → ρ → ℝ) : Prop where
  analytic : ∃ U : Set (S → ℝ), IsOpen U ∧ Set.Ici 0 ⊆ U ∧
    ∀ r, AnalyticOnNhd ℝ (fun x => R x r) U
  reactants : ∀ r x y, (∀ j, 0 < N.src r j → x j = y j) → R x r = R y r
  monotone : ∀ r, ∀ x ∈ Set.Ici (0 : S → ℝ), ∀ j, 0 < N.src r j →
    0 ≤ fderiv ℝ (fun z => R z r) x (Pi.single j 1)
  zero_of_reactant_zero : ∀ r, ∀ x ∈ Set.Ici (0 : S → ℝ), (∃ j, 0 < N.src r j ∧ x j = 0) →
    R x r = 0
  pos_of_reactants_pos : ∀ r, ∀ x ∈ Set.Ici (0 : S → ℝ), (∀ j, 0 < N.src r j → 0 < x j) →
    0 < R x r

/-- For finitely many reactions (`[Fintype ρ]`), the vector field `S ↦ Γ R(S)`, whose `j`-th
coordinate is `∑_{r : ρ} Γ_{jr} R_r(S)`. -/
noncomputable def field [Fintype ρ] (R : (S → ℝ) → ρ → ℝ) (x : S → ℝ) : S → ℝ :=
  fun j => ∑ r, stoich N j r * R x r

/-- For finitely many reactions (`[Fintype ρ]`), `φ` is a solution of `Ṡ = Γ R(S)` on `[0, ∞)`
in `𝒪₊` starting at `x₀`. -/
def IsSolution [Fintype ρ] (R : (S → ℝ) → ρ → ℝ) (x₀ : S → ℝ) (φ : ℝ → S → ℝ) : Prop :=
  φ 0 = x₀ ∧ ∀ t, 0 ≤ t → φ t ∈ Set.Ici 0 ∧
    HasDerivWithinAt φ (field N R (φ t)) (Set.Ici 0) t

/-- The network with rates `R` is persistent: for every initial state with all concentrations
positive, every `ω`-limit point of its solution (a limit of `φ t_n` along some `t_n → ∞`) has all
concentrations positive, that is, lies off the boundary of `𝒪₊`. -/
def IsPersistent [Fintype ρ] (R : (S → ℝ) → ρ → ℝ) : Prop :=
  ∀ x₀ : S → ℝ, (∀ j, 0 < x₀ j) → ∀ φ, IsSolution N R x₀ φ →
    ∀ y, MapClusterPt y atTop φ → ∀ j, 0 < y j

/-- For finitely many species (`[Fintype S]`), a P-semiflow: a nonzero nonnegative vector `c`
with `c Γ = 0`, that is, `∑_{j : S} c_j Γ_{jr} = 0` for every reaction `r`. -/
def IsPSemiflow [Fintype S] (c : S → ℝ) : Prop :=
  (∀ j, 0 ≤ c j) ∧ c ≠ 0 ∧ ∀ r, ∑ j, c j * stoich N j r = 0

/-- For finitely many species (`[Fintype S]`), the associated Petri net is conservative: there
is a P-semiflow with all entries positive. -/
def IsConservative [Fintype S] : Prop :=
  ∃ c : S → ℝ, (∀ j, 0 < c j) ∧ ∀ r, ∑ j, c j * stoich N j r = 0

/-- For finitely many reactions (`[Fintype ρ]`), the associated Petri net is consistent: there
is a vector `v` with all entries positive and `Γ v = 0`, that is, `∑_{r : ρ} Γ_{jr} v_r = 0` for
every species `j`. -/
def IsConsistent [Fintype ρ] : Prop :=
  ∃ v : ρ → ℝ, (∀ r, 0 < v r) ∧ ∀ j, ∑ r, stoich N j r * v r = 0

/-- **Necessary condition for persistence** (Angeli–De Leenheer–Sontag 2007, Theorem 1). For
admissible rates `R`, a conservative and persistent network has a consistent associated Petri
net.

Source: D. Angeli, P. De Leenheer, E. D. Sontag, Math. Biosci. 210 (2007) 598–618,
Theorem 1. -/
theorem_wanted isConsistent_of_isPersistent [Fintype S] [DecidableEq S] [Fintype ρ]
    {R : (S → ℝ) → ρ → ℝ} (hR : IsAdmissibleRate N R) (hcons : IsConservative N)
    (hpers : IsPersistent N R) :
    IsConsistent N

/-- **Siphon criterion for persistence** (Angeli–De Leenheer–Sontag 2007, Theorem 2). For
admissible rates `R`, if the associated Petri net is conservative and each siphon contains the
support of a P-semiflow, then the network is persistent.

Source: D. Angeli, P. De Leenheer, E. D. Sontag, Math. Biosci. 210 (2007) 598–618,
Theorem 2. -/
theorem_wanted isPersistent_of_siphon [Fintype S] [DecidableEq S] [Fintype ρ]
    {R : (S → ℝ) → ρ → ℝ} (hR : IsAdmissibleRate N R) (hcons : IsConservative N)
    (hsiph : ∀ Z : Finset S, SiphonPrimeDecompositionWanted.IsSiphon N Z →
      ∃ c : S → ℝ, IsPSemiflow N c ∧ ∀ j, 0 < c j → j ∈ Z) :
    IsPersistent N R

end WantedExt.Biology.Biophysics.SiphonPersistenceWanted
