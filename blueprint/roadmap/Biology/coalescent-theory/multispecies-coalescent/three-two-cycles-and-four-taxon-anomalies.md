# Three-cycles with a two-leaf hybrid are the source of four-taxon anomalies

Work under the network multispecies coalescent with correlated inheritance $\mathrm{NMSC}(\rho)$. In a
semidirected network, a **$k$-cycle** is an up-down cycle with $k$ edges after suppressing degree-$2$
nodes, and a **$3_2$-cycle** is a $3$-cycle containing a hybrid node and two of its parents such that the
hybrid node has at least two descendant leaves. A network **contains a $3_2$-cycle** when some displayed
subnetwork, obtained by deleting hybrid edges and recursively pruning unlabelled leaves, has a
$3_2$-cycle. A $4$-taxon network is of **class $k$** if its displayed trees induce exactly $k$ of the three
unrooted quartet topologies. A blob of a semidirected network $\mathcal{N}$ **traps the root** if the root
of every rooted LSA network inducing $\mathcal{N}$ (a rooted network whose root is the lowest stable
ancestor of all taxa) lies in the blob and not on its boundary; roots above the lowest stable ancestor
disappear in the semidirected network and are not counted.

Let $\mathcal{N}$ be a $4$-taxon binary semidirected metric network of class $1$ or $2$. (A class-$3$
network displays all three quartets, so no undisplayed quartet can outweigh a displayed one and it is
never hard-anomalous.)

1. If $\mathcal{N}$ contains a $3_2$-cycle, then for every $\rho < 1$ there are numerical parameters (edge
   lengths and inheritance probabilities) making $\mathcal{N}$ anomalous under $\mathrm{NMSC}(\rho)$.
2. Conversely, if $\mathcal{N}$ is anomalous and either has no non-trivial blob trapping the root, or has
   a root-trapping $2$-blob whose removal disconnects a single taxon from the other three, then
   $\mathcal{N}$ contains a $3_2$-cycle.

Under the common inheritance model $\rho = 1$, no $4$-taxon binary metric network is hard-anomalous, for
any edge lengths and inheritance probabilities, although soft anomalies remain possible.

For the explicit $3_2$-cycle of the source, with hybrid inheritance probabilities $\gamma_1$ and
$\gamma_2 = 1 - \gamma_1$, hybrid edge lengths $s_1, s_2$, the cycle's tree edge of length $s_0$ and the
edge below the hybrid of length $t$, the concordance factor of the displayed quartet $a_1a_2|b_1b_2$ is
minimized at $s_1 = s_2 = 0$, where

$$P_\rho(a_1a_2|b_1b_2 \mid \mathcal{N}) = \frac13 + \frac23\bigl(1 - e^{-t}\bigr) - \frac23 e^{-t}(1-\rho)\gamma_1\gamma_2\bigl(1 - e^{-s_0}\bigr).$$

At $s_1 = s_2 = 0$ this is below $1/3$, so the network is anomalous, exactly when
$e^{t} - 1 < (1-\rho)\gamma_1\gamma_2\bigl(1 - e^{-s_0}\bigr)$. The right-hand side is less than $1/4$, so an
anomaly needs $t < \log(5/4)$ even with zero hybrid edge lengths. Letting $t = 0$ and $s_0 \to \infty$ gives
the limit $1/3 - (2/3)(1-\rho)\gamma_1\gamma_2 < 1/3$, so for every fixed $\rho < 1$ and every
$\gamma_1 \in (0,1)$ the network is anomalous once the hybrid edges and the edge below the hybrid are short
enough and the cycle's tree edge is long enough.

## Depends on

- [Hard and soft anomalous networks under the network multispecies coalescent](anomalous-networks-under-correlated-inheritance.md)

## Proof depends on

- [A degree-2 sub-blob can be replaced by a single edge without changing quartet CFs](two-sub-blob-replacement-preserves-quartet-cfs.md)
- [Quartet concordance factors do not depend on the root of a network](quartet-cfs-independent-of-the-root.md)

## Expansion

Part 1 is the displayed computation: setting the inheritance probability of one hybrid edge in each
partner pair outside the $3_2$-cycle to $1$ reduces the network to a single $3_2$-cycle, where short
hybrid edges and a short edge below the hybrid keep the two sister leaves below the hybrid from
coalescing before they are separated by the reticulation, and a long tree edge in the cycle then makes the
displayed quartet less probable than $1/3$; by continuity the anomaly persists for inheritance
probabilities in $(0,1)$ close enough to those values. Part 2 uses the replacement of degree-$2$ sub-blobs by single
edges: a $4$-taxon network whose non-trivial blobs are all of degree at most $2$ reduces to a tree and so
is not anomalous, so an anomalous network under the stated restriction must carry a $3$-blob, and a case
analysis of the lowest hybrid node in that blob forces a $3_2$-cycle. The claim for $\rho = 1$ holds
because every gene tree then evolves within a single displayed tree chosen with probability $\gamma(T)$,
so the vector of quartet concordance factors is the convex combination
$\sum_{T} \gamma(T)\,\mathrm{qCF}(T)$ over displayed trees, and an entry that is maximal in every term of
a convex combination is maximal in the combination. The source conjectures that part 2 holds without the
root-trapping restriction.

## Sources

- C. Ané, J. Fogg, E. S. Allman, H. Baños and J. A. Rhodes, "Anomalous networks under the multispecies coalescent: theory and prevalence", Journal of Mathematical Biology 88 (2024), 29, <https://doi.org/10.1007/s00285-024-02050-7>. (Definition 3, Example 1, Definition 6, Conjecture 7, Theorem 8, Proposition 12.)
