/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shafarevich's relation-rank bound

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.ShafarevichRelationRank` — shafarevich_relation_rank_bound (manifest `manifests/problems/shafarevich_relation_rank_bound.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.ShafarevichRelationRankWanted` namespace. Mathematical
statements are unchanged. Source: D. C. Mayer, *New number fields with known p-class tower*, Tatra Mt. Math. Publ. 64 (2015), 21–57 (Theorem 5.1, S=∅; arXiv:1510.00565); H. Koch, *Galois Theory of p-Extensions*, Springer 2002 (Theorems 11.5 and 11.8); I. R. Shafarevich, *Extensions with prescribed ramification points* (1963). Lean hypothesis: https://github.com/logical-intelligence/erdos-unit-distance (Hyp_ShafarevichRelationRankBound).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.NumberTheory.ShafarevichRelationRankWanted
namespace NumberTheory

/-!
# Shafarevich's relation-rank bound

`shafarevich_relation_rank_bound` bounds the relation rank of the Galois group
`G = Gal(F^{un,p}/F)` of the maximal unramified pro-`p` extension of a number
field `F`, for odd `p`:

```
r(G) ≤ d(G) + (r₁ + r₂ - 1) + δ_p(F),
```

where `d(G)` is the generator rank, `r(G) = dim_{𝔽_p} H²(G; 𝔽_p)` the relation
rank, `r₁`/`r₂` the number of real/complex places of `F`, and `δ_p(F) = 1` iff
`F` contains a primitive `p`-th root of unity. The bound also asserts that
`r(G)` is finite (`H2Finite`).

References: D. C. Mayer, *New number fields with known p-class tower*, Theorem
5.1 with `S = ∅`; H. Koch, *Galois Theory of p-Extensions*, Theorems 11.5 and
11.8; Shafarevich (1963).

This is the second of the two external inputs of Logical Intelligence's
formalization of the disproof of Erdős's unit-distance conjecture
(<https://github.com/logical-intelligence/erdos-unit-distance>,
`Hyp_ShafarevichRelationRankBound`), where it is taken as a hypothesis. It is
not currently available in Mathlib.

## Trusted scaffolding

Everything below the statement's data — `IsEverywhereUnramified`,
`maximalUnramifiedProPF`, `MaxUnramifiedProPGaloisGroup` (with its group and
topology instances), and the rank definitions `generatorRank`, `relationRank`,
`H2Finite` — are **trusted helper definitions** (they are not holes). They fix
the meaning of `Gal(F^{un,p}/F)`, `d(G)`, and `r(G)`, following
`ErdosUnitDistance.Defs.MaxUnramifiedProPGaloisGroup` and
`ErdosUnitDistance.Defs.ProPGroups`. A solver must prove the inequality *about
these definitions*; their correctness is part of the trusted statement.

`maximalUnramifiedProPF F p` is the compositum, inside `AlgebraicClosure F`, of
all finite Galois everywhere-unramified intermediate extensions with `p`-group
Galois group — the usual construction of the maximal unramified pro-`p`
extension.
-/

open NumberField CategoryTheory

/-- **Everywhere unramified extension.** Let $M/F$ be an extension of number fields, with rings
of integers $\mathcal{O}_F$ and $\mathcal{O}_M$. Then $M/F$ is everywhere unramified when every
prime ideal $\mathfrak{P}$ of $\mathcal{O}_M$ lying over a nonzero prime ideal $\mathfrak{p}$
of $\mathcal{O}_F$ has ramification index $1$ over $\mathcal{O}_F$, and every infinite place of
$M$ lying over a real place of $F$ is real. -/
def IsEverywhereUnramified
    (F M : Type) [Field F] [Field M] [NumberField F] [NumberField M]
    [Algebra F M] : Prop :=
  (∀ (𝔭 : Ideal (𝓞 F)) (𝔓 : Ideal (𝓞 M)),
      𝔭.IsPrime → 𝔭 ≠ ⊥ →
      𝔓 ∈ 𝔭.primesOver (𝓞 M) →
      𝔓.ramificationIdx (𝓞 F) = 1) ∧
  (∀ w : NumberField.InfinitePlace F, w.IsReal →
    ∀ w' : NumberField.InfinitePlace M,
      w'.comap (algebraMap F M) = w → w'.IsReal)

/-- **Maximal unramified pro-$p$ extension.** Let $F$ be a number field, $\overline{F}$ an
algebraic closure of $F$, and $p$ a prime. The maximal unramified pro-$p$ extension
$F^{\mathrm{un},p}$ of $F$ is the compositum in $\overline{F}$ of all intermediate fields
$F \subseteq M \subseteq \overline{F}$ such that $M/F$ is finite, Galois and everywhere
unramified, and its Galois group $\mathrm{Gal}(M/F)$ is a $p$-group (each such $M$ is a
number field). -/
noncomputable def maximalUnramifiedProPF
    (F : Type) [Field F] [NumberField F]
    (p : ℕ) [Fact (Nat.Prime p)] :
    IntermediateField F (AlgebraicClosure F) :=
  ⨆ (M : IntermediateField F (AlgebraicClosure F))
      (_ : FiniteDimensional F M)
      (_ : IsGalois F M)
      (_ : IsPGroup p (M ≃ₐ[F] M))
      (_ : NumberField M)
      (_ : IsEverywhereUnramified F M),
    M

/-- **Galois group of the maximal unramified pro-$p$ extension.** For a number field $F$ and a
prime $p$, this is the group $\mathrm{Gal}(F^{\mathrm{un},p}/F)$ of field automorphisms of the
maximal unramified pro-$p$ extension $F^{\mathrm{un},p}$ of $F$ that fix $F$, under
composition and with the Krull topology. -/
noncomputable def MaxUnramifiedProPGaloisGroup
    (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)] :
    Type :=
  (maximalUnramifiedProPF F p) ≃ₐ[F] (maximalUnramifiedProPF F p)

noncomputable instance MaxUnramifiedProPGaloisGroup.instGroup
    (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)] :
    Group (MaxUnramifiedProPGaloisGroup F p) :=
  inferInstanceAs (Group ((maximalUnramifiedProPF F p) ≃ₐ[F] _))

noncomputable instance MaxUnramifiedProPGaloisGroup.instTopologicalSpace
    (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)] :
    TopologicalSpace (MaxUnramifiedProPGaloisGroup F p) :=
  inferInstanceAs (TopologicalSpace ((maximalUnramifiedProPF F p) ≃ₐ[F] _))

instance MaxUnramifiedProPGaloisGroup.instIsTopologicalGroup
    (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact (Nat.Prime p)] :
    IsTopologicalGroup (MaxUnramifiedProPGaloisGroup F p) :=
  inferInstanceAs (IsTopologicalGroup ((maximalUnramifiedProPF F p) ≃ₐ[F] _))

/-- **Generator rank of a topological group.** For a topological group $G$, the generator
rank $d(G)$ is the least natural number $k$ such that some finite subset $S \subseteq G$ with
$k$ elements generates a dense subgroup of $G$. If no finite subset of $G$ generates a dense
subgroup, then $d(G) = 0$ by convention. -/
noncomputable def generatorRank
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : ℕ :=
  sInf {k : ℕ | ∃ S : Finset G, S.card = k ∧
    (Subgroup.closure (S : Set G)).topologicalClosure = ⊤}

/-- **Trivial representation on $\mathbb{Z}/p\mathbb{Z}$.** For a natural number $p$ and a
topological group $G$, this is $\mathbb{Z}/p\mathbb{Z}$ with the discrete topology, regarded as a
continuous representation of $G$ over $\mathbb{Z}/p\mathbb{Z}$ on which every element of $G$
acts as the identity. -/
noncomputable def trivialZModpRep
    (p : ℕ) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    TopRep (ZMod p) G :=
  TopRep.of (ContRepresentation.trivial (ZMod p) G (ZMod p))

/-- **Relation rank of a topological group.** For a prime $p$ and a topological group $G$, the
relation rank $r(G)$ is the dimension over $\mathbb{F}_p$ of the continuous cohomology group
$H^2(G, \mathbb{F}_p)$ of degree $2$, with coefficients in the trivial representation of $G$ on
$\mathbb{F}_p$. If this space is infinite-dimensional, then $r(G) = 0$ by convention. -/
noncomputable def relationRank
    (p : ℕ) [Fact p.Prime] (G : Type)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : ℕ :=
  Module.finrank (ZMod p)
    (continuousCohomology 2 (trivialZModpRep p G))

/-- **Finite-dimensional second cohomology mod $p$.** For a prime $p$ and a topological group
$G$, this is the statement that the continuous cohomology group $H^2(G, \mathbb{F}_p)$ of degree
$2$, with coefficients in the trivial representation of $G$ on $\mathbb{F}_p$, is
finite-dimensional over $\mathbb{F}_p$. -/
def H2Finite (p : ℕ) [Fact p.Prime] (G : Type)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Prop :=
  FiniteDimensional (ZMod p)
    (continuousCohomology 2 (trivialZModpRep p G))

/- **Shafarevich's relation-rank bound** (odd `p`, empty-`S` specialization).

For a number field `F` and an odd prime `p`, with `G = Gal(F^{un,p}/F)` the
Galois group of the maximal unramified pro-`p` extension, the relation rank is
finite and

```
r(G) ≤ d(G) + (r₁ + r₂ - 1) + δ_p(F),
```

where `r₁ = nrRealPlaces F`, `r₂ = nrComplexPlaces F`, and `δ_p(F) = 1` iff `F`
contains a primitive `p`-th root of unity.

References: Mayer, Theorem 5.1 (`S = ∅`); Koch, Theorems 11.5 and 11.8. -/
/-- **Shafarevich's relation-rank bound.** Let $F$ be a number field, let $p$ be an odd prime,
and let $G = \mathrm{Gal}(F^{\mathrm{un},p}/F)$ be the Galois group of the maximal unramified
pro-$p$ extension of $F$. Write $d(G)$ for the generator rank and $r(G)$ for the relation rank
of $G$, $r_1$ and $r_2$ for the numbers of real and complex places of $F$, and $\delta$ for $1$
if $F$ contains a primitive $p$-th root of unity and $0$ otherwise. Then the continuous
cohomology group $H^2(G, \mathbb{F}_p)$ with trivial coefficients is finite-dimensional over
$\mathbb{F}_p$, and
$$r(G) \le d(G) + (r_1 + r_2 - 1) + \delta.$$

Source: D. C. Mayer, *New number fields with known p-class tower*, Tatra Mt. Math. Publ. 64 (2015), 21–57 (Theorem 5.1, S=∅; arXiv:1510.00565); H. Koch, *Galois Theory of p-Extensions*, Springer 2002 (Theorems 11.5 and 11.8); I. R. Shafarevich, *Extensions with prescribed ramification points* (1963). Lean hypothesis: https://github.com/logical-intelligence/erdos-unit-distance (Hyp_ShafarevichRelationRankBound). Via leanprover/lean-eval@38361be, problem `shafarevich_relation_rank_bound`. -/
public theorem_wanted shafarevich_relation_rank_bound
    (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (_hpOdd : Odd p) :
    H2Finite p (MaxUnramifiedProPGaloisGroup F p) ∧
      (open Classical in
       relationRank p (MaxUnramifiedProPGaloisGroup F p) ≤
        generatorRank (MaxUnramifiedProPGaloisGroup F p) +
          (NumberField.InfinitePlace.nrRealPlaces F +
            NumberField.InfinitePlace.nrComplexPlaces F - 1) +
          (if ∃ ζ : F, IsPrimitiveRoot ζ p then 1 else 0))

end NumberTheory

end MathlibExt.NumberTheory.ShafarevichRelationRankWanted
