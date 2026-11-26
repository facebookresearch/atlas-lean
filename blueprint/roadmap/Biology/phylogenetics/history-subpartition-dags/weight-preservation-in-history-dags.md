# Weight preservation in history DAGs

**Setting.** Let $f : E \to W$ assign a weight to every possible edge of the complete history sDAG on labels $Y$ (see the history subpartition DAG), with values in a set $W$ that has an addition with identity $0$. The weight of a history $t$ is $g_f(t) = \sum_{e \in E_t} f(e)$; with sequence labels and Hamming distance as $f$, $g_f$ is the parsimony score. Assume $W$ is **clade-ordered**: it carries a total order respecting addition on the sets of weights of subhistories below any node, on the sets of weights of augmented subhistories below any node-clade pair, and on the set of history weights.

**Theorem 1.** Let $T$ be a collection of histories with $g_f(t) = K$ for all $t \in T$, and let $D(T)$ be the histories contained in the history sDAG built from $T$. Then $D(T)$ contains a history of weight $< K$ if and only if it contains a history of weight $> K$.

**Corollary 1.1.** Every history sDAG $(V,E)$ has a trim $(V', E')$ (a sub-sDAG with $V' \subseteq V$, $E' \subseteq E$) whose histories are exactly the minimum-weight histories of $(V, E)$.

**Corollary (parsimony).** If every history in $T$ is maximally parsimonious for a fixed set of observed leaf sequences, then so is every history in $D(T)$, though $D(T)$ may be much larger than $T$.

## Depends on

- [History subpartition DAG](history-subpartition-dag.md)

## Expansion

Every history in $D(T)$ is reached from histories of $T$ by a finite sequence of subhistory swaps: replacing the subhistory below a node by another subhistory hanging below a node with the same label and subpartition in another member of $T$. Because edge weights depend only on the endpoint nodes, a swap changes the weight by the difference $\delta$ of the two exchanged augmented subhistories, and the reverse swap applied to the partner history changes its weight by $-\delta$; with a clade order this forces any decrease below $K$ to be matched by an increase above $K$. For the corollary, the minimum-weight histories $T'$ of $(V,E)$ cannot generate anything lighter, so by the theorem they generate nothing heavier, $D(T') = T'$, and the union of $T'$ is the desired trim. In practice the trim is computed by a bottom-up dynamic program that keeps, for each node-clade pair, only the child edges achieving the minimum subhistory weight.

## Sources

- W. Dumm, M. Barker, W. Howard-Snyder, W. S. DeWitt III, F. A. Matsen IV, "Representing and extending ensembles of parsimonious evolutionary histories with a directed acyclic graph", Journal of Mathematical Biology 87 (2023) 75, Definitions 11-12, Theorem 1 and Corollary 1.1, Appendix A, <https://doi.org/10.1007/s00285-023-02006-3>, PMCID PMC10600060.
