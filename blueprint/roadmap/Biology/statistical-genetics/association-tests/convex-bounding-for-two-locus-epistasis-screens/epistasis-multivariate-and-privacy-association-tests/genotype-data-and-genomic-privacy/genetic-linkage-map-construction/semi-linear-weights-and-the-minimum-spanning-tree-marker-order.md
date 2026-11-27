# Semi-linear weights make the minimum spanning tree the true marker order

**Setting.** Let $M = \{l_1,\dots,l_m\}$ be biallelic markers on one linkage group of a doubled-haploid (or backcross, haploid, RIL) mapping population, and let $P_{i,j} \in [0, \tfrac12]$ be the probability that an individual is recombinant between $l_i$ and $l_j$. A pair $(l_i,l_j)$ is **enclosed** in $(l_p,l_q)$ if the chromosomal segment spanned by $l_i,l_j$ lies inside the segment spanned by $l_p,l_q$. The basic genetic law is

$$(l_i,l_j) \text{ enclosed in } (l_p,l_q) \;\Longrightarrow\; P_{i,j} \le P_{p,q}.$$

A pair weight $w : M\times M \to \mathbb{R}$ is **semi-linear** if $w(i,j) \le w(p,q)$ whenever $(l_i,l_j)$ is enclosed in $(l_p,l_q)$. Examples: $w(i,j) = P_{i,j}$, $w(i,j) = \log P_{i,j}$, and $w(i,j) = -[P_{i,j}\log P_{i,j} + (1-P_{i,j})\log(1-P_{i,j})]$, which is increasing on $[0,\tfrac12]$. Let $G$ be the complete graph on $M$ with edge weights $w$.

**Theorem.** If $w$ is semi-linear, then
1. the true chromosomal order of the markers is a minimum-weight traveling-salesman path of $G$;
2. if, in addition, the minimum spanning tree of $G$ is unique, it is that path, so the true order is recovered by any MST algorithm (e.g. Prim's) in polynomial time.

**Estimation.** In a doubled-haploid population genotyped on $n$ individuals, the number $d_{i,j}$ of recombinants is the Hamming distance between the genotype rows of $l_i$ and $l_j$, and $d_{i,j}/n$ is the maximum-likelihood estimate of $P_{i,j}$. Substituting it gives the approximate weights $d_{i,j}/n$ (equivalent to the SARF/COUNT criterion), $\log(d_{i,j}/n)$ (log PARF), and the binary-entropy weight (negative log-likelihood ML criterion); with clean, large samples these are semi-linear or nearly so.

## Depends on

- [Prim's algorithm returns a minimum spanning tree](../../../../../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/prim-s-algorithm/prim-minimum-spanning-tree.md)

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

In the true order $l_{\pi(1)},\dots,l_{\pi(m)}$, every non-adjacent pair encloses each adjacent pair lying between its endpoints, so its weight is at least theirs. Any spanning tree using a non-adjacent edge can therefore exchange it for an enclosed adjacent edge that reconnects the two components without increasing the weight; this exchange argument shows the path of adjacent pairs is a minimum spanning tree, and a fortiori a minimum Hamiltonian path (a Hamiltonian path is a spanning tree). When the MST is unique it must equal this path. Markers with $d_{i,j} = 0$ (co-segregating) are collapsed first so that all weights are positive. With noisy or missing genotypes the MST is used as a starting point and refined by local TSP heuristics (2-opt and related moves).

## Sources

- Y. Wu, P. R. Bhat, T. J. Close, S. Lonardi, "Efficient and accurate construction of genetic linkage maps from the minimum spanning tree of a graph", PLoS Genetics 4(10) (2008) e1000212, Materials and Methods (genotyping data and objective functions; ordering markers) and Lemma 1 of Supplementary Text S1, <https://doi.org/10.1371/journal.pgen.1000212>, PMCID PMC2556103.
