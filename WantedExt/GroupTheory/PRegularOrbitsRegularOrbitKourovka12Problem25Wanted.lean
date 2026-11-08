/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Regular orbits from `p`-regular orbits (Kourovka Notebook Problem 12.25)

Kourovka Notebook, Archive of Solved Problems, Problem 12.25 (Jiping Zhang): let a finite group `G`
act irreducibly on a vector space `V`; the orbit of `α ∈ V` is `p`-regular if the stabilizer of `α`
is a `p'`-subgroup. Does `G` have a regular orbit on `V` if it has a `p`-regular orbit for every
prime `p`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.PRegularOrbitsRegularOrbitKourovka12Problem25Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.25 (Jiping
Zhang). UnsolvedMath record UM-00700844 (`KOU-12.25`), dataset ulamai/UnsolvedMath v1.8.0.

The action is by linear maps (a `DistribMulAction` commuting with the scalars) on a nonzero
finite-dimensional space over a finite field, and it is faithful; irreducible means that `⊥` and `⊤`
are the only `G`-invariant subspaces. A `p'`-subgroup has order prime to `p`, and a regular orbit is
one with trivial stabilizer. Over an infinite field a faithful finite linear group always has a
regular orbit, so the finite-field case is the content; the extra hypotheses (faithful, finite
field) only weaken the claim, so its refutation is the stronger statement.
-/

/-- Kourovka 12.25 (Jiping Zhang): if a finite group `G` acts faithfully and irreducibly by linear
maps on a nonzero finite-dimensional vector space `V` over a finite field, and for every prime `p`
some vector has a stabilizer of order prime to `p` (a `p`-regular orbit), then some vector has
trivial stabilizer (a regular orbit). -/
def pRegularOrbitsImplyRegularOrbit : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Nontrivial V] (G : Type) [Group G] [Finite G]
    [DistribMulAction G V] [SMulCommClass G F V], FaithfulSMul G V →
    (∀ W : Submodule F V, (∀ g : G, ∀ v ∈ W, g • v ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∀ p : ℕ, p.Prime → ∃ v : V, (Nat.card (MulAction.stabilizer G v)).Coprime p) →
    ∃ v : V, MulAction.stabilizer G v = ⊥

/--
Resolved false: the Kourovka Archive answers 12.25 "No, not always" (V. I. Zenkov): for `H = A₄ ≀
ℤ₅`, `V = O₂(H) ≅ 𝔽₂¹⁰` and `G ≅ ℤ₃ ≀ ℤ₅` a complement to `V`, the faithful irreducible action of
`G` on `V` by conjugation has orbits with stabilizers of order 5 and of order 3, hence `p`-regular
orbits for every prime `p`, but no regular orbit, since `|G| = 1215 > 1024 = |V|`. Source: E. I.
Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.25 (Jiping Zhang);
resolution: V. I. Zenkov, letter of 11 February 1994, as recorded in the Kourovka Archive, Problem
12.25, Archive answer: No, not always; H = A_4 ≀ Z_5, V = O_2(H), G a complement to V acting by
conjugation, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted pRegularOrbitsImplyRegularOrbit_refuted : ¬ pRegularOrbitsImplyRegularOrbit

end MathlibExt.GroupTheory.PRegularOrbitsRegularOrbitKourovka12Problem25Wanted
