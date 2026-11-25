/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.DirichletForm.Brownian
public import MathlibExt.Probability.DirichletForm.RegularToQuasiRegular

/-!
# Dirichlet forms: wanted theorems

Central theorems of the theory of Dirichlet forms whose proofs are deferred.

* `unitContractionOperates_iff_resolvent`: the Beurling–Deny correspondence between Markovian
  closed forms
  and Markovian resolvents (Fukushima, Oshima and Takeda, *Dirichlet Forms and Symmetric Markov
  Processes*, 2nd revised and extended ed., de Gruyter, 2011, Theorem 1.4.1, (b) ⇔ (d)).

Fukushima's theorem (a regular Dirichlet form is the Dirichlet form of an `m`-symmetric Hunt
process, FOT Theorem 7.2.1) and the Albeverio–Ma–Röckner characterisation of quasi-regular forms
by right processes are not stated: Mathlib has no Hunt or right processes, and a statement about
an undefined process predicate would not be a faithful proposition.
-/

@[expose] public section

open MeasureTheory Filter Topology Matrix
open scoped RealInnerProductSpace

open MathlibExt.Probability.DirichletForm

namespace MathlibExt.Probability.DirichletFormWanted

/-- **Beurling–Deny: the unit contraction operates on a closed form iff its resolvent is
Markovian.** Let `E` be a closed symmetric form on `L²(X; m)`, `m` σ-finite. For `α > 0` and
`f ∈ L²`, the resolvent `G_α f` is the element `u ∈ D[E]` with `E(u, v) + α (u, v) = (f, v)` for
all `v ∈ D[E]` (FOT, equation (1.3.7)). Then the unit contraction operates on `E` (condition
(E.4)′, equivalent for closed forms to FOT's Markov condition (E.4)) if and only if every
`α G_α` is Markovian: `0 ≤ f ≤ 1` a.e. implies `0 ≤ α G_α f ≤ 1` a.e. (Fukushima, Oshima and
Takeda, *Dirichlet Forms and Symmetric Markov Processes*, 2nd ed., 2011, Theorem 1.4.1, (b) ⇔
(d)). FOT prove (b) ⇒ (e) under their topological assumption (1.1.7) and note (footnote 10) that
it holds without it, referring to Ma–Röckner (1992) and Bouleau–Hirsch (1991); the statement
here has no topological assumption. -/
theorem_wanted unitContractionOperates_iff_resolvent {X : Type*} [MeasurableSpace X] {m : Measure X}
    [SigmaFinite m] (E : SymmetricForm m) (hE : E.IsClosed) :
    E.UnitContractionOperates ↔ ∀ α : ℝ, 0 < α → ∀ f u : Lp ℝ 2 m, u ∈ E.domain →
      (∀ v ∈ E.domain, E.form u v + α * ⟪u, v⟫ = ⟪f, v⟫) →
      (∀ᵐ x ∂m, 0 ≤ f x ∧ f x ≤ 1) → ∀ᵐ x ∂m, 0 ≤ α * u x ∧ α * u x ≤ 1

end MathlibExt.Probability.DirichletFormWanted
