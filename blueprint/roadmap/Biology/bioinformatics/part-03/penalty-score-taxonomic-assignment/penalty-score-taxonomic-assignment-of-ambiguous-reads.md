# Penalty-score taxonomic assignment of ambiguous reads

**Setting.** A reference taxonomy is a rooted tree $T$ with leaf set $L$. A sequencing read $R_i$ that
matches several references has a hit set $M_i \subseteq L$, $|M_i| \ge 2$; let $T_i$ be the subtree rooted at
$\mathrm{LCA}(M_i)$ and, for a node $j$ of $T_i$, let $T_{i,j}$ be the subtree rooted at $j$. Assigning $R_i$ to
$j$ partitions the leaves of $T_i$ into

$$\mathrm{TP}_{i,j} = M_i \cap T_{i,j}, \quad \mathrm{FP}_{i,j} = T_{i,j} \setminus M_i, \quad
\mathrm{TN}_{i,j} = (T_i \setminus T_{i,j}) \setminus M_i, \quad \mathrm{FN}_{i,j} = M_i \setminus T_{i,j}.$$

**Penalty score.** For a user parameter $q \in [0, 1]$,

$$\mathrm{PS}_{i,j} = q\,\frac{|\mathrm{FN}_{i,j}|}{|\mathrm{TP}_{i,j}|} + (1 - q)\,\frac{|\mathrm{FP}_{i,j}|}{|\mathrm{TP}_{i,j}|}
= \frac{q\,(|M_i| - |M_{i,j}|) + (1 - q)\,|N_{i,j}|}{|M_{i,j}|},$$

with $M_{i,j}$ and $N_{i,j}$ the hit and non-hit leaves below $j$ ($\mathrm{PS} = \infty$ outside $T_i$ or when
$\mathrm{TP} = \emptyset$). The read is assigned to a node minimizing $\mathrm{PS}_{i,j}$.

**Properties.**

1. $q = 1$ always assigns to $\mathrm{LCA}(M_i)$ (the usual LCA rule), and $q = 0$ always admits an optimal
   assignment to a leaf.
2. For $q = 1/2$ the minimizers are exactly the maximizers of the F-measure
   $F_{i,j} = \frac{2|\mathrm{TP}_{i,j}|}{|\mathrm{FN}_{i,j}| + |\mathrm{FP}_{i,j}| + 2|\mathrm{TP}_{i,j}|}$.
3. Some minimizer is a **relevant** node: a hit leaf or the LCA of at least two hits.
4. A minimizer can be found in $O(|T_i|)$ time by two traversals; after $O(|T|)$ preprocessing (postorder
   numbering and constant-time LCA queries), in $O(|M_i|)$ time by building the topological restriction
   of $T_i$ to $M_i$, whose nodes are exactly the relevant nodes.
5. When the true source is among the hits, assignment to the LCA has zero expected-distance
   predictive power, which motivates choosing $q < 1$.

## Expansion

For property 2, $(|\mathrm{FN}| + |\mathrm{FP}|)/(2|\mathrm{TP}|) + 1$ is the reciprocal of the F-measure, so
minimizing one maximizes the other. For property 3, replacing a non-relevant $j$ by the LCA $j'$ of the
hits below it keeps $|M_{i,j}|$ and does not increase $|N_{i,j}|$, so $\mathrm{PS}$ cannot increase. The
restricted tree has $O(|M_i|)$ nodes: sort hits by postorder number, take the LCAs of consecutive hits,
and recover parent links from nested postorder intervals, then compute $|M_{i,j}|$ bottom-up with
precomputed leaf counts. The parameter $q$ slides assignments continuously from leaf level to the
conservative LCA level, trading recall of the hit set against precision of the assigned clade.

## Sources

- J. C. Clemente, J. Jansson, G. Valiente, "Flexible taxonomic assignment of ambiguous sequencing
  reads", BMC Bioinformatics 12 (2011) 8, Eqs. 1-2, Lemmas 1-3 and Theorems 1-2,
  <https://doi.org/10.1186/1471-2105-12-8> (PMC3024944).
