# Three-cycles with a two-leaf hybrid are the source of four-taxon anomalies

Work under the network multispecies coalescent with correlated inheritance $\mathrm{NMSC}(\rho)$. In a
semidirected network, a **$k$-cycle** is an up-down cycle with $k$ edges after suppressing degree-$2$
nodes, and a **$3_2$-cycle** is a $3$-cycle containing a hybrid node and two of its parents such that the
hybrid node has at least two descendant leaves.

Let $\mathcal{N}$ be a $4$-taxon binary semidirected metric network.

1. If $\mathcal{N}$ contains a $3_2$-cycle, then for every $\rho < 1$ there are edge lengths making
   $\mathcal{N}$ anomalous under $\mathrm{NMSC}(\rho)$.
2. Conversely, if $\mathcal{N}$ is anomalous and either has no non-trivial blob trapping the root, or has
   a root-trapping $2$-blob whose removal disconnects a single taxon from the other three, then
   $\mathcal{N}$ contains a $3_2$-cycle as a subnetwork.

Under the common inheritance model $\rho = 1$, no $4$-taxon binary metric network is hard-anomalous, for
any edge lengths and inheritance probabilities, although soft anomalies remain possible.

For the explicit $3_2$-cycle of the source, with hybrid inheritance probabilities $\gamma_1$ and
$\gamma_2 = 1 - \gamma_1$, hybrid edge lengths $s_1, s_2$, the cycle's tree edge of length $s_0$ and the
edge below the hybrid of length $t$, the concordance factor of the displayed quartet $a_1a_2|b_1b_2$ is
minimized at $s_1 = s_2 = 0$, where
$$P_\rho(a_1a_2|b_1b_2 \mid \mathcal{N}) = \frac13 + \frac23\bigl(1 - e^{-t}\bigr) - \frac23 e^{-t}(1-\rho)\gamma_1\gamma_2\bigl(1 - e^{-s_0}\bigr).$$
Letting $t = 0$ and $s_0 \to \infty$ gives the limit $1/3 - (2/3)(1-\rho)\gamma_1\gamma_2 \le 1/3$, so the
network is anomalous for every fixed $\rho < 1$ and every $\gamma_1 \in (0,1)$ once the hybrid edges are
short enough and the cycle's tree edge long enough.

## Depends on

- [Hard and soft anomalous networks under the network multispecies coalescent](anomalous-networks-under-correlated-inheritance.md)
- [A degree-2 sub-blob can be replaced by a single edge without changing quartet CFs](two-sub-blob-replacement-preserves-quartet-cfs.md)

## Expansion

Part 1 is the displayed computation: short hybrid edges keep the two sister leaves below the hybrid from
coalescing before they are separated by the reticulation, and a long tree edge in the cycle then makes the
displayed quartet less probable than $1/3$. Part 2 uses the replacement of degree-$2$ sub-blobs by single
edges: a $4$-taxon network whose non-trivial blobs are all of degree at most $2$ reduces to a tree and so
is not anomalous, so an anomalous network under the stated restriction must carry a $3$-blob, and a case
analysis of the lowest hybrid node in that blob forces a $3_2$-cycle. The claim for $\rho = 1$ holds
because every gene tree then evolves within a single displayed tree chosen with probability $\gamma(T)$,
so the vector of quartet concordance factors is the convex combination
$\sum_{T} \gamma(T)\,\mathrm{qCF}(T)$ over displayed trees, and an entry that is maximal in every term of
a convex combination is maximal in the combination. The source conjectures that part 2 holds without the
root-trapping restriction.

## Sources

- C. Ané, J. Fogg, E. S. Allman, H. Baños and J. A. Rhodes, "Anomalous networks under the multispecies coalescent: theory and prevalence", Journal of Mathematical Biology 88 (2024), 29, <https://doi.org/10.1007/s00285-024-02050-7>. (Example 1, Conjecture 7, Theorem 8, Proposition 12.)
