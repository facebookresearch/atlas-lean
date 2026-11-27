# Gomory-Hu trees in almost-linear time: all-pairs max-flow reduces to single-pair max-flow

There is a randomized (Monte Carlo) algorithm that, given an undirected graph $G = (V, E, w)$ with $n$ vertices, $m$ edges and integer weights in $\{1, \dots, W\}$ with $W \le n^{O(1)}$, computes a cut-equivalent tree of $G$ in $m^{1+o(1)}$ time with probability $1 - n^{-c}$. Consequently there is a data structure with randomized $m^{1+o(1)}$ preprocessing time that answers the maximum flow value (and a minimum cut) for any query pair $s, t$ in $\tilde O(1)$ time, and all-pairs max-flow has the same time complexity as single-pair max-flow up to a subpolynomial factor.

## Proof sketch

The algorithm reduces the construction to $\mathrm{polylog}(n)$ single-source minimum cut instances, each solved with polylogarithmically many max-flow calls on graphs of total size $m^{1+o(1)}$. Single-source minimum cuts in weighted graphs are found by combining isolating cuts on terminal sets sampled at geometric rates with guide trees obtained from $2$-respecting tree packings, so that each pivot splits off a constant fraction of the remaining terminals. Plugging in the almost-linear maximum-flow algorithm gives $m^{1+o(1)}$ time; the query data structure stores the tree with a minimum-on-path structure.

## Depends on

- [Flow-equivalent and cut-equivalent trees of weighted graphs](flow-equivalent-and-cut-equivalent-trees.md)
- [Maximum-flow oracles and the max-flow call model for cut problems](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/isolating-cuts-and-steiner-min-cuts/max-flow-oracle-call-model.md)

## Proof depends on

- [Gomory-Hu trees of weighted graphs in nearly quadratic time](gomory-hu-weighted-nearly-quadratic.md)
- [Isolating cut lemma with logarithmically many max-flow calls](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/isolating-cuts-and-steiner-min-cuts/isolating-cut-lemma.md)
- [Terminal subsampling isolates one side of a Steiner minimum cut](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/isolating-cuts-and-steiner-min-cuts/terminal-subsampling-isolates-steiner-cut.md)
- [Single-source minimum cut values](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/isolating-cuts-and-steiner-min-cuts/single-source-minimum-cut-values.md)

## Sources

- Amir Abboud, Jason Li, Debmalya Panigrahi, Thatchaphol Saranurak, "All-Pairs Max-Flow is no Harder than Single-Pair Max-Flow: Gomory-Hu Trees in Almost-Linear Time", FOCS (2023).
- Amir Abboud, Robert Krauthgamer, Jason Li, Debmalya Panigrahi, Thatchaphol Saranurak, Ohad Trabelsi, "Breaking the Cubic Barrier for All-Pairs Max-Flow: Gomory-Hu Tree in Nearly Quadratic Time", FOCS (2022), arXiv:2111.04958.
- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
- Amir Abboud, Robert Krauthgamer, Ohad Trabelsi, "Cut-Equivalent Trees are Optimal for Min-Cut Queries", FOCS (2020), arXiv:2009.06090.
