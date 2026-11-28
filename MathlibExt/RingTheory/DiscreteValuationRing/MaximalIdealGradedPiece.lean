/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-!
# Maximal-ideal graded pieces of a discrete valuation ring

Let `R` be a discrete valuation ring with maximal ideal `𝔪` and residue field
`κ = R ⧸ 𝔪`. This file identifies every graded piece `𝔪 ^ i ⧸ 𝔪 ^ (i + 1)` as a
one-dimensional vector space over `κ`.

This module is a prerequisite stage for the corrected ATLAS NumberTheoryI N261
upper different-exponent bound (Theorem 12.27), not the full N261 target. It
proves only the residue-field-linear description and finrank of the
maximal-ideal graded pieces; it does not prove a trace formula,
different-ideal containment, or either valuation bound.

ATLAS source: [`v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean`, lines
1237--1324, at revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean#L1237-L1324).
Those lines define the ramification/different valuations and state the target
bounds, but they do not state the graded-piece equivalence proved here.

Source-to-API map: `MaximalIdealGradedPiece`,
`residueFieldLinearEquivMaximalIdealGradedPiece`, and
`finrank_maximalIdealGradedPiece` are new supporting API for a future
maximal-ideal-filtration proof of the trace/different estimate; the upper bound
and the tame-equality characterization remain deferred.

The helper `different_valuation_exact` there is unfinished, and its exact equality
is false in wild ramification, so it is not formalized here.

## Main results

* `IsDiscreteValuationRing.MaximalIdealGradedPiece`: the `i`-th graded piece
  `𝔪 ^ i ⧸ 𝔪 ^ (i + 1)`, as a quotient of the ideal `𝔪 ^ i` by `𝔪 • ⊤`.
* `IsDiscreteValuationRing.residueFieldLinearEquivMaximalIdealGradedPiece`:
  a `κ`-linear equivalence `κ ≃ₗ[κ] MaximalIdealGradedPiece R i`.
* `IsDiscreteValuationRing.finrank_maximalIdealGradedPiece`: each graded piece has
  `κ`-finrank one.
-/

@[expose] public section

namespace IsDiscreteValuationRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **Graded pieces of the maximal-ideal filtration.** Let $R$ be a discrete valuation ring with
maximal ideal $\mathfrak{m}$. For $i \in \mathbb{N}$, the $i$-th graded piece is the $R$-module
$\mathfrak{m}^i/\mathfrak{m}^{i+1}$, realized as the quotient of the ideal $\mathfrak{m}^i$,
viewed as an $R$-module, by its submodule $\mathfrak{m} \cdot \mathfrak{m}^i$. -/
abbrev MaximalIdealGradedPiece (i : ℕ) :=
  ((IsLocalRing.maximalIdeal R) ^ i : Ideal R) ⧸
    (IsLocalRing.maximalIdeal R • ⊤ :
      Submodule R ((IsLocalRing.maximalIdeal R) ^ i : Ideal R))

/-- Residue-field scalar action on the graded piece, transported along the
definitional unfolding `ResidueField R = R ⧸ 𝔪` from the generic
`Module (R ⧸ 𝔪) (𝔪 ^ i ⧸ 𝔪 • ⊤)` instance (typeclass resolution does not unfold
the plain `ResidueField` def on its own). -/
instance (i : ℕ) :
    Module (IsLocalRing.ResidueField R) (MaximalIdealGradedPiece R i) :=
  inferInstanceAs
    (Module (R ⧸ IsLocalRing.maximalIdeal R) (MaximalIdealGradedPiece R i))

/-- **Graded pieces of a DVR as copies of the residue field.** Let $R$ be a discrete valuation
ring with maximal ideal $\mathfrak{m}$ and residue field $\kappa = R/\mathfrak{m}$, and let
$\varpi$ be a generator of $\mathfrak{m}$ chosen once and for all. For $i \in \mathbb{N}$, the
map $\kappa \to \mathfrak{m}^i/\mathfrak{m}^{i+1}$ sending the class of $r \in R$ to the class
of $r \varpi^i$ is a $\kappa$-linear isomorphism.

Here $\kappa$ acts on $\mathfrak{m}^i/\mathfrak{m}^{i+1}$ through $R$, which is well defined
because $\mathfrak{m}$ annihilates the graded piece. -/
noncomputable def residueFieldLinearEquivMaximalIdealGradedPiece (i : ℕ) :
    IsLocalRing.ResidueField R ≃ₗ[IsLocalRing.ResidueField R]
      MaximalIdealGradedPiece R i :=
  let e : (R ⧸ IsLocalRing.maximalIdeal R) ≃ₗ[R] MaximalIdealGradedPiece R i :=
    Ideal.quotEquivPowQuotPowSucc
      (IsPrincipalIdealRing.principal _) (not_a_field R) i
  { e with
    map_smul' := fun q x => by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
      exact e.map_smul r x }

/-- **Graded pieces of a DVR are one-dimensional.** Let $R$ be a discrete valuation ring with
maximal ideal $\mathfrak{m}$ and residue field $\kappa = R/\mathfrak{m}$. For every
$i \in \mathbb{N}$, the graded piece $\mathfrak{m}^i/\mathfrak{m}^{i+1}$ is a vector space of
dimension one over $\kappa$. -/
theorem finrank_maximalIdealGradedPiece (i : ℕ) :
    Module.finrank (IsLocalRing.ResidueField R)
      (MaximalIdealGradedPiece R i) = 1 := by
  rw [← (residueFieldLinearEquivMaximalIdealGradedPiece R i).finrank_eq]
  exact Module.finrank_self _

end IsDiscreteValuationRing
