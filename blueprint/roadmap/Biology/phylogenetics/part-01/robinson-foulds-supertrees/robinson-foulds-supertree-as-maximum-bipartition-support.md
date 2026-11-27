# Robinson–Foulds supertree as maximum bipartition support

**Robinson–Foulds supertree.** Let $\mathcal{T}$ be a finite set of unrooted source trees (polytomies
allowed) with leafsets $L(t) \subseteq S = \bigcup_{t \in \mathcal{T}} L(t)$. Every unrooted tree $T$ is
determined by its set $\mathrm{Bip}(T)$ of bipartitions, and for trees on the same leafset the
Robinson–Foulds distance is $\mathrm{RF}(T, T') = |\mathrm{Bip}(T) \,\triangle\, \mathrm{Bip}(T')|$. For
nested leafsets $L(t) \subseteq L(T)$ set $\mathrm{RF}(T, t) = \mathrm{RF}(T|_{L(t)}, t)$, where
$T|_Q$ is the restriction of $T$ to $Q$ with degree-two nodes suppressed. A binary tree $T$ on $S$
minimizing

$$\mathrm{RF}(T, \mathcal{T}) = \sum_{t \in \mathcal{T}} \mathrm{RF}(T, t)$$

is a **Robinson–Foulds supertree**; finding one is NP-hard.

**Bipartition support.** A bipartition $[A', B']$ of a source tree $t$ with leafset $S'$ supports $T$
if $T$ has a bipartition $[A, B]$ with $A' = S' \cap A$ and $B' = S' \cap B$. The bipartition support
of $\mathcal{T}$ for $T$ is the total number of source-tree bipartitions that support $T$.

**Observation 1.** A binary tree on $S$ with maximum bipartition support from $\mathcal{T}$ is a
Robinson–Foulds supertree.

**Observation 2.** For a rooted binary tree $T$ on $S$, say $[A', B']$ supports $T$ if $T|_{S'}$ has
$A'$ or $B'$ as a clade; the support of $\mathcal{T}$ for $T$ then equals its support for the
unrooted version of $T$.

**Additive decomposition over nodes.** Each internal node $v$ of a rooted binary tree $T$ on
$Y \subseteq S$, with child clades $A_1, A_2$, defines a tripartition $(A_1, A_2, Y \setminus (A_1
\cup A_2))$. A supporting source bipartition $[U', V']$ is assigned to the unique node defining a
tripartition $(A_1, A_2, A_3)$ with

$$U' \subseteq A_1, \qquad V' \cap A_1 = \emptyset, \qquad V' \cap A_2 \neq \emptyset,$$

and to no node if it does not support $T$ (Lemma 1); the assignment depends only on $(A_1, A_2)$.
With $\mathrm{support}(A_1, A_2)$ the number of source bipartitions mapped to a tripartition of the
form $(A_1, A_2, Z)$, the bipartition support of $\mathcal{T}$ for $T$ is

$$\sum_{(A_1, A_2, A_3) \in \mathrm{Trip}(T)} \mathrm{support}(A_1, A_2).$$

## Depends on

- [Robinson–Foulds distance](../../splits-compatibility-ultrametrics-and-upgma/rf-dist.md)

## Expansion

Observation 1 holds because a fixed source tree $t$ restricted to a binary $T$ has
$\mathrm{RF}(T, t) = |\mathrm{Bip}(T|_{L(t)})| + |\mathrm{Bip}(t)| - 2\,|\text{shared}|$, and the
first two terms do not depend on which binary $T$ is chosen, so minimizing distance is maximizing the
number of shared, that is supporting, bipartitions. Rooting does not change which bipartitions are
displayed, giving Observation 2. The assignment rule in the decomposition sends a bipartition whose
side $U'$ is a clade of $T|_{S'}$ to the first ancestor of $U'$ that also sees a leaf of $V'$ (or to
the most recent common ancestor of $U' \cup V'$ when both sides are clades), so each supporting
bipartition is counted exactly once. Because $\mathrm{support}(A_1, A_2)$ depends only on the two
child clades, the support of a rooted tree is a sum of local terms, which is what makes a dynamic
program over clades possible.

## Sources

- P. Vachaspati, T. Warnow, "FastRFS: fast and accurate Robinson-Foulds Supertrees using constrained
  exact optimization", Bioinformatics 33 (2017), Section 2, Observations 1-2, Lemmas 1-2,
  Definition 1 and Theorem 1, <https://doi.org/10.1093/bioinformatics/btw600> (PMC5870905).
