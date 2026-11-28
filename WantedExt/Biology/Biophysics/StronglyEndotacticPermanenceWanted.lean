/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Strongly endotactic reaction networks are permanent

A reaction network on a finite set `S` of species has finitely many reactions `r : y → y'` with
real complexes `y, y' ∈ ℝ^S` and reaction vectors `y' - y`; its stoichiometric subspace `H` is
the span of the reaction vectors. For `w ∈ ℝ^S` write `y ≤_w y'` when `⟨w, y⟩ ≤ ⟨w, y'⟩`. A
reaction is `w`-essential if `⟨w, y' - y⟩ ≠ 0`, and the `w`-support is the set of
`≤_w`-maximal reactants of `w`-essential reactions. The network is **endotactic** if for every
`w`, every `w`-essential reaction whose reactant lies in the `w`-support has `⟨w, y' - y⟩ < 0`.
It is **strongly endotactic** if moreover for every `w` not orthogonal to `H` there is a reaction
`y → y'` with `⟨w, y' - y⟩ < 0` whose reactant `y` is `≤_w`-maximal among all reactants.

A tempering assigns to each reaction `r` a compact interval `[a_r, b_r] ⊆ (0, ∞)`. For a positive
`x₀`, the invariant polyhedron is `(x₀ + H) ∩ ℝ_{≥0}^S`; its relative interior is
`(x₀ + H) ∩ ℝ_{>0}^S`. The mass-action differential inclusion has, over a point `x` of the
relative interior, the fiber `{∑_r k_r x^{y_r} (y'_r - y_r) : k_r ∈ [a_r, b_r]}` (real powers),
and is empty elsewhere. A trajectory is a differentiable curve on an interval `I ⊆ [0, ∞)`
containing its left endpoint whose tangent vectors lie in the inclusion. The inclusion is
**persistent** if the closure of every trajectory in `[0, ∞]^S` avoids the boundary, that is,
every trajectory stays in a compact subset of `ℝ_{>0}^S`, and **permanent** if moreover there is
a compact `Ω ⊆ ℝ_{>0}^S` that every trajectory defined on a ray eventually enters and stays in. A
network is permanent if the inclusion is permanent for every tempering and every invariant
polyhedron.

**Theorem 1.1** (Gopalkrishnan–Miller–Shiu 2014). Every strongly endotactic reaction network is
permanent.

**Theorem 1.3** (Gopalkrishnan–Miller–Shiu 2014). Every weakly reversible reaction network with
exactly one linkage class is permanent.

Theorem 1.2 of the source (the global attractor conjecture for strongly endotactic
complex-balanced systems) is not stated here. Reactions are indexed, so parallel reactions are
allowed; their temperings add and give the same inclusion as a single reaction, and neither the
endotactic conditions nor the linkage classes change. Complexes are the reactants and products,
so the source's isolated complexes (which do not affect the dynamics) are not represented. The
network, its reaction vectors, stoichiometric subspace, complexes, reaction relation, weak
reversibility and mass-action field are the shared definitions of
`MathlibExt.Dynamics.PolynomialNetworks.RealExponent`, also used by Boros's existence theorem in
`WantedExt.Biology.Biophysics.WeaklyReversiblePositiveSteadyStateWanted`.

Sources: M. Gopalkrishnan, E. Miller, A. Shiu, "A geometric approach to the global attractor
conjecture", SIAM J. Appl. Dyn. Syst. 13 (2014) 758–797, Section 3, Definitions 4.1–4.2,
Theorems 1.1 and 1.3 (arXiv:1305.5303).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Dynamics.PolynomialNetworks.RealExponent
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Logic.Relation
public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Topology.Compactness.Compact

@[expose] public section

namespace WantedExt.Biology.Biophysics.StronglyEndotacticPermanenceWanted

open MathlibExt.Biology.Dynamics

variable {S ρ : Type*} [Fintype S] (N : RealExponentNetwork S ρ)

/-- For finite species `S` (`[Fintype S]`), reaction `r` is `w`-essential: its reaction vector
is not orthogonal to `w`, that is, `⟨w, y' - y⟩ ≠ 0` for `r : y → y'`, where
`⟨w, y⟩ = ∑_{s : S} w_s y_s` is the dot product. -/
def IsEssential (w : S → ℝ) (r : ρ) : Prop :=
  w ⬝ᵥ N.reactionVector r ≠ 0

/-- For finite species `S` (`[Fintype S]`), the reactant of `r` is `≤_w`-maximal among the
reactants of `w`-essential reactions, where `y ≤_w y'` means `⟨w, y⟩ ≤ ⟨w, y'⟩` for the dot
product `⟨w, y⟩ = ∑_{s : S} w_s y_s`. For a `w`-essential reaction `r` this says that its
reactant lies in the `w`-support; the predicate itself does not require `r` to be
`w`-essential. -/
def InSupport (w : S → ℝ) (r : ρ) : Prop :=
  ∀ r', IsEssential N w r' → w ⬝ᵥ N.src r' ≤ w ⬝ᵥ N.src r

/-- For finite species `S` (`[Fintype S]`), the network is endotactic: for every `w`, every
`w`-essential reaction whose reactant lies in the `w`-support has `⟨w, y' - y⟩ < 0`, where
`⟨w, y⟩ = ∑_{s : S} w_s y_s`. -/
def IsEndotactic : Prop :=
  ∀ w r, IsEssential N w r → InSupport N w r → w ⬝ᵥ N.reactionVector r < 0

/-- For finite species `S` (`[Fintype S]`), the network is strongly endotactic: it is endotactic,
and for every `w` not orthogonal to the stoichiometric subspace some reaction `y → y'` has
`⟨w, y' - y⟩ < 0` and a reactant `y` that is `≤_w`-maximal among all reactants, where
`⟨w, y⟩ = ∑_{s : S} w_s y_s`. -/
def IsStronglyEndotactic : Prop :=
  IsEndotactic N ∧ ∀ w, (∃ r, w ⬝ᵥ N.reactionVector r ≠ 0) →
    ∃ r, w ⬝ᵥ N.reactionVector r < 0 ∧ ∀ r', w ⬝ᵥ N.src r' ≤ w ⬝ᵥ N.src r

/-- The network has exactly one linkage class: it has a complex, and any two complexes are joined
by an undirected path of reactions. -/
def HasOneLinkageClass : Prop :=
  N.complexes.Nonempty ∧ ∀ y ∈ N.complexes, ∀ y' ∈ N.complexes, Relation.EqvGen N.Reacts y y'

/-- For finite species (`[Fintype S]`) and finite reactions (`[Fintype ρ]`), the fiber of the
mass-action differential inclusion over `x`, for the tempering `[lo r, hi r]` and the invariant
polyhedron of `x₀`: empty unless `x` lies in the relative interior `(x₀ + H) ∩ ℝ_{>0}^S`, and
otherwise the set of mass-action vectors `∑_{r : ρ} k_r x^{src r} (prod r - src r)`, where
`x^{src r} = ∏_{s : S} x_s ^ (src r s)` with real powers, for `k_r ∈ [lo r, hi r]`. -/
def fiber [Fintype ρ] (lo hi : ρ → ℝ) (x₀ x : S → ℝ) : Set (S → ℝ) :=
  {v | (∀ s, 0 < x s) ∧ x - x₀ ∈ N.stoichiometricSubspace ∧
    ∃ k : ρ → ℝ, (∀ r, lo r ≤ k r ∧ k r ≤ hi r) ∧ v = N.massActionField k x}

/-- `f` is a trajectory of the mass-action differential inclusion on the interval `I`: `I` is a
nonempty interval in `[0, ∞)` containing its left endpoint `a`, and `f` is differentiable along
`I` with tangent vectors in the fiber. -/
def IsTrajectory [Fintype ρ] (lo hi : ρ → ℝ) (x₀ : S → ℝ) (I : Set ℝ) (a : ℝ)
    (f : ℝ → S → ℝ) : Prop :=
  0 ≤ a ∧ a ∈ I ∧ I.OrdConnected ∧ (∀ t ∈ I, a ≤ t) ∧
    ∀ t ∈ I, ∃ v ∈ fiber N lo hi x₀ (f t), HasDerivWithinAt f v I t

/-- The network is permanent: for every tempering `[lo r, hi r] ⊆ (0, ∞)` and every positive
`x₀`, every trajectory stays in a compact subset of `ℝ_{>0}^S` (persistence), and there is a
compact `Ω ⊆ ℝ_{>0}^S` such that every trajectory on a ray is eventually in `Ω`. -/
def IsPermanent [Fintype ρ] : Prop :=
  ∀ lo hi : ρ → ℝ, (∀ r, 0 < lo r ∧ lo r ≤ hi r) → ∀ x₀ : S → ℝ, (∀ s, 0 < x₀ s) →
    (∀ I a f, IsTrajectory N lo hi x₀ I a f →
      ∃ K : Set (S → ℝ), IsCompact K ∧ (∀ y ∈ K, ∀ s, 0 < y s) ∧ f '' I ⊆ K) ∧
    ∃ Ω : Set (S → ℝ), IsCompact Ω ∧ (∀ y ∈ Ω, ∀ s, 0 < y s) ∧
      ∀ a f, IsTrajectory N lo hi x₀ (Set.Ici a) a f → ∃ T, ∀ t ≥ T, f t ∈ Ω

/-- **Strongly endotactic networks are permanent** (Gopalkrishnan–Miller–Shiu 2014,
Theorem 1.1). Every strongly endotactic reaction network with real complexes and finitely many
species and reactions is permanent: for every tempering by compact intervals in `(0, ∞)` and every
positive `x₀`, every trajectory of the mass-action differential inclusion stays in a compact
subset of the positive orthant, and some compact subset of the positive orthant eventually
contains every trajectory defined on a ray.

Source: M. Gopalkrishnan, E. Miller, A. Shiu, SIAM J. Appl. Dyn. Syst. 13 (2014) 758–797,
Theorem 1.1. -/
theorem_wanted isPermanent_of_isStronglyEndotactic {S ρ : Type*} [Fintype S] [Fintype ρ]
    (N : RealExponentNetwork S ρ) (h : IsStronglyEndotactic N) :
    IsPermanent N

/-- **Weakly reversible networks with one linkage class are permanent** (Gopalkrishnan–Miller–
Shiu 2014, Theorem 1.3). Every weakly reversible reaction network with real complexes, finitely
many species and reactions, and exactly one linkage class is permanent: for every tempering by
compact intervals in `(0, ∞)` and every positive `x₀`, every trajectory of the mass-action
differential inclusion stays in a compact subset of the positive orthant, and some compact subset
of the positive orthant eventually contains every trajectory defined on a ray.

Source: M. Gopalkrishnan, E. Miller, A. Shiu, SIAM J. Appl. Dyn. Syst. 13 (2014) 758–797,
Theorem 1.3. -/
theorem_wanted isPermanent_of_isWeaklyReversible_of_hasOneLinkageClass {S ρ : Type*}
    [Fintype S] [Fintype ρ] (N : RealExponentNetwork S ρ) (hwr : N.IsWeaklyReversible)
    (hone : HasOneLinkageClass N) :
    IsPermanent N

end WantedExt.Biology.Biophysics.StronglyEndotacticPermanenceWanted
