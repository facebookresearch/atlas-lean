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

/-- **Zhang's question on regular orbits from $p$-regular orbits.** The statement that for every
finite field $F$, every nonzero finite-dimensional vector space $V$ over $F$ and every finite group
$G$ acting faithfully on $V$ by $F$-linear maps, if the only $G$-invariant subspaces of $V$ are $0$
and $V$, and for every prime $p$ some vector of $V$ has a stabilizer in $G$ of order prime to $p$
(a $p$-regular orbit), then some vector of $V$ has trivial stabilizer in $G$ (a regular orbit).

This is Kourovka Notebook Problem 12.25 (Jiping Zhang). -/
def pRegularOrbitsImplyRegularOrbit : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [Nontrivial V] (G : Type) [Group G] [Finite G]
    [DistribMulAction G V] [SMulCommClass G F V], FaithfulSMul G V →
    (∀ W : Submodule F V, (∀ g : G, ∀ v ∈ W, g • v ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∀ p : ℕ, p.Prime → ∃ v : V, (Nat.card (MulAction.stabilizer G v)).Coprime p) →
    ∃ v : V, MulAction.stabilizer G v = ⊥

/--
**$p$-regular orbits for every prime do not force a regular orbit.** There exist a finite field $F$,
a nonzero finite-dimensional vector space $V$ over $F$ and a finite group $G$ acting faithfully on
$V$ by $F$-linear maps such that the only $G$-invariant subspaces of $V$ are $0$ and $V$ and, for
every prime $p$, some vector of $V$ has a stabilizer in $G$ of order prime to $p$, but no vector of
$V$ has trivial stabilizer in $G$.

Resolved false: the Kourovka Archive answers 12.25 "No, not always" (V. I. Zenkov). Write
$\mathbb{Z}_n$ for the cyclic group of order $n$, $A_4$ for the alternating group of degree $4$ and
$\mathbb{F}_2$ for the field with two elements. Let $H = A_4 \wr \mathbb{Z}_5$ be the wreath
product, let $V = O_2(H)$ be the largest normal $2$-subgroup of $H$, so $V \cong \mathbb{F}_2^{10}$,
and let $G \cong \mathbb{Z}_3 \wr \mathbb{Z}_5$ be a complement to $V$ in $H$. The faithful
irreducible action of $G$ on $V$ by conjugation has orbits with stabilizers of order $5$ and of
order $3$, hence $p$-regular orbits for every prime $p$, but no regular orbit, since
$|G| = 1215 > 1024 = |V|$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.25 (Jiping
Zhang); resolution: V. I. Zenkov, letter of 11 February 1994, as recorded in the Kourovka Archive,
Problem 12.25, Archive answer: No, not always; H = A_4 ≀ Z_5, V = O_2(H), G a complement to V acting
by conjugation, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted pRegularOrbitsImplyRegularOrbit_refuted : ¬ pRegularOrbitsImplyRegularOrbit

end MathlibExt.GroupTheory.PRegularOrbitsRegularOrbitKourovka12Problem25Wanted
