/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Minimal siphons of a reaction network from a primary decomposition

Shiu and Sturmfels (2010): for a chemical reaction network `G` on species `c_1, …, c_s`, a nonempty
set `Z` of species is a siphon if for every `z ∈ Z` and every reaction `c^{y_i} → c^{y_j}` whose
product complex contains `c_z` there is `a ∈ Z` contained in the reactant complex `c^{y_i}`. With
the binomial and monomial ideals in `ℚ[c_1, …, c_s]`

* `I_G = ⟨c^{y_i} (c^{y_j} - c^{y_i}) : c^{y_i} → c^{y_j} a reaction⟩`,
* `J_G = ⟨c^{y_j} - c^{y_i} : c^{y_i} → c^{y_j} a reaction⟩`,
* `M_G = ⟨c^{y} : y a complex⟩`,

Theorem 3.1 states: the minimal siphons of `G` are the inclusion-minimal sets
`{i : c_i ∈ P}` as `P` runs over the minimal primes of `I_G`; if each connected component of `G` is
strongly connected, `I_G` can be replaced by `J_G`; and if `G` is strongly connected, by `M_G`.
The source proves the second clause from the first: when each connected component is strongly
connected, `I_G` and `J_G` have the same radical, hence the same minimal primes. That clause is
therefore not stated here as a separate wanted declaration.

The ideals are read in `R = ℚ[c_1, …, c_s] / ⟨c_1 ⋯ c_s⟩`, the ring the source fixes for the whole
of Section 3 ("All our ideals will live in this ring"; its Example 1.3 decomposes
`I_G + ⟨E F P S₀ X Y⟩`): the minimal primes taken are those of `I_G + ⟨c_1 ⋯ c_s⟩` in
`ℚ[c_1, …, c_s]`. (In `ℚ[c_1, …, c_s]` itself a minimal prime containing no variable would give the
empty set.) The network, its complexes, the reaction relation and weak reversibility are the shared
ones of `MathlibExt.Dynamics.PolynomialNetworks.Deficiency`, and every species is assumed to occur
in some complex, which is implicit in the source (an unused species `z` would be a siphon `{z}`
invisible to `M_G`); each connected component being strongly connected is weak reversibility.
Self-loops `src r = prod r` contribute `0` to `I_G` and `J_G`. Not recorded here: Theorem 3.2
(relevant siphons through the nine saturation ideals of the facets and vertex supports of the
invariant polyhedra) and Proposition 2.1.

Sources: A. Shiu and B. Sturmfels, "Siphons in chemical reaction networks", Bulletin of
Mathematical Biology 72 (2010) 1448–1463, arXiv:0904.4529, Theorem 3.1.
-/
module

public import Batteries.Util.ProofWanted
public import Domains.Biology.Biophysics.SiphonPrimeDecomposition
public import MathlibExt.Dynamics.PolynomialNetworks.Deficiency
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section

namespace WantedExt.Biology.Biophysics.SiphonPrimeDecompositionWanted

open MathlibExt.Biology.Dynamics.ComplexBalanced MvPolynomial

variable {S ρ : Type*} [Fintype S] [DecidableEq S]

/-- `I_G = ⟨c^{src r} (c^{prod r} - c^{src r})⟩`. -/
noncomputable def idealI (N : ReactionNetwork S ρ) : Ideal (MvPolynomial S ℚ) :=
  Ideal.span (Set.range fun r => mono (N.src r) * (mono (N.prod r) - mono (N.src r)))

/-- `J_G = ⟨c^{prod r} - c^{src r}⟩`. -/
noncomputable def idealJ (N : ReactionNetwork S ρ) : Ideal (MvPolynomial S ℚ) :=
  Ideal.span (Set.range fun r => mono (N.prod r) - mono (N.src r))

/-- **Minimal siphons from the binomial ideal `I_G`** (Shiu and Sturmfels 2010, Theorem 3.1, first
clause): for a network on finitely many species, each of which occurs in some complex, a finite set
`Z` of species is a minimal siphon iff it is inclusion-minimal among the sets `{i : c_i ∈ P}` for
`P` a minimal prime of `I_G + ⟨c_1 ⋯ c_s⟩`.

Source: Shiu and Sturmfels (2010), Theorem 3.1. -/
public theorem_wanted isMinimalSiphon_iff_idealI (N : ReactionNetwork S ρ)
    (hocc : AllSpeciesOccur N) (Z : Finset S) :
    IsMinimalSiphon N Z ↔ IsMinimalVarSet (idealI N) Z

end WantedExt.Biology.Biophysics.SiphonPrimeDecompositionWanted
