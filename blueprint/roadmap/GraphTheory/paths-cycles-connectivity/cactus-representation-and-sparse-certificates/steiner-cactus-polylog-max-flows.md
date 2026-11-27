# Steiner cactus and hypercactus with polylogarithmically many max-flows

There is a randomized (Monte Carlo) algorithm that, given an undirected weighted graph $G$ with $m$ edges and a terminal set $R \subseteq V$ with $|R| \ge 2$, computes an $R$-Steiner cactus of $G$ in $\tilde O(\mathrm{MaxFlow}(O(m)))$ time with probability $1 - n^{-c}$, where $\mathrm{MaxFlow}(m)$ is the time of maximum flow on a graph with $m$ edges. Analogously, for a weighted hypergraph of total size $p = \sum_e |e|$ and a terminal set, a Steiner hypercactus is computed in $\tilde O(\mathrm{MaxFlow}(O(p)))$ time. With almost-linear maximum flow both constructions run in almost-linear time.

## Proof sketch

The key tool is a maximal version of the isolating cut lemma: for a terminal set, the inclusion-wise maximal minimum isolating cuts are computed with polylogarithmically many max-flow calls by the same bit-cut regions argument applied to complements. Sampling terminals at geometric rates and recording maximal isolating minimum cuts that achieve the Steiner minimum value identifies the leaves and cycle structure of the Steiner cactus, after which contraction recurses on smaller instances. The hypergraph version uses the symmetric submodular generalization of isolating cuts.

## Depends on

- [Cactus representations of all minimum cuts](cactus-representation-of-minimum-cuts.md)
- [Steiner minimum cuts of a terminal set](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/isolating-cuts-and-steiner-min-cuts/steiner-minimum-cut.md)
- [Maximum-flow oracles and the max-flow call model for cut problems](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/isolating-cuts-and-steiner-min-cuts/max-flow-oracle-call-model.md)

## Proof depends on

- [Isolating cut lemma with logarithmically many max-flow calls](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/isolating-cuts-and-steiner-min-cuts/isolating-cut-lemma.md)
- [Isolating sets for symmetric submodular functions and hypergraph cuts (Chekuri-Quanrud)](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/isolating-cuts-and-steiner-min-cuts/isolating-sets-symmetric-submodular.md)
- [Terminal subsampling isolates one side of a Steiner minimum cut](../../../ComputerScience/graph-algorithms/spanning-trees-flows-matchings/almost-linear-flows-cuts-and-dynamic-matching/isolating-cuts-and-steiner-min-cuts/terminal-subsampling-isolates-steiner-cut.md)
- [Corner structure of two crossing minimum cuts](crossing-minimum-cuts-corners.md)

## Sources

- Zhongtian He, Shang-En Huang, Thatchaphol Saranurak, "Cactus Representations in Polylogarithmic Max-flow via Maximal Isolating Mincuts", SODA (2024), arXiv:2311.10706.
- Jason Li, Debmalya Panigrahi, "Deterministic Min-cut in Poly-logarithmic Max-flows", FOCS (2020), arXiv:2111.02008.
- Chandra Chekuri, Kent Quanrud, "Isolating Cuts, (Bi-)Submodularity, and Faster Algorithms for Connectivity", ICALP (2021), arXiv:2103.12908.
