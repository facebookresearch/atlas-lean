# Support- and length-weighted quartet score

**Setting.** Let $\mathcal G$ be a set of $k$ unrooted gene trees on subsets of a taxon set of size $n$. For a gene tree $G$ and four of its leaves, $G{\restriction}Q$ is the induced quartet topology and $\delta_G(ab|cd) \in \{0, 1\}$ indicates that it is $ab|cd$. The *anchors* of $ab|cd$ in $G$ are the two internal nodes where the paths among $a, b, c$ and among $b, c, d$ meet; $P_G(\{a,b,c,d\})$ is the set of branches on the path between the anchors, $l_G(a, b)$ the path length (in substitutions per site) from $a$ to $b$, and $s_G(e) \in [0,1]$ the support of branch $e$.

**Score.** For a candidate species tree $S$ with quartet set $\mathcal Q(S)$,

$$W(S, \mathcal G) = \sum_{G \in \mathcal G} \sum_{Q \in \mathcal Q(S)} w_G(S{\restriction}Q),$$

with one of the per-quartet weights

- unweighted: $w_G(ab|cd) = \delta_G(ab|cd)$;
- support: $w_G(ab|cd) = \Big(1 - \prod_{e \in P_G(\{a,b,c,d\})} (1 - s_G(e))\Big)\,\delta_G(ab|cd)$;
- length: $w_G(ab|cd) = e^{-(l_G(a,b) + l_G(c,d))}\,\delta_G(ab|cd)$;
- hybrid: the product of the support and length factors times $\delta_G(ab|cd)$.

The support factor is the probability that at least one anchor-path branch is correct if supports are independent probabilities of correctness; the length factor down-weights "long" quartets, whose terminal paths are long and which are most prone to long-branch attraction.

**Decomposition over tripartitions.** Each internal node $v$ of a binary $S$ induces a tripartition $A|B|C$ of the taxa, and every quartet of $S$ is anchored at exactly two internal nodes. With $L_G$ the leaf set of $G$,

$$W(A|B|C, G) = \frac12 \sum_{\substack{a \in A \cap L_G\\ b \in B \cap L_G \\ c \in C \cap L_G}} \Big(\sum_{d \in A \cap L_G \setminus\{a\}} w_G(ad|bc) + \sum_{d \in B \cap L_G \setminus\{b\}} w_G(bd|ac) + \sum_{d \in C \cap L_G \setminus\{c\}} w_G(cd|ab)\Big),$$

$$W(S, \mathcal G) = \frac12 \sum_{A|B|C \in T_S}\ \sum_{G \in \mathcal G} W(A|B|C, G),$$

where $T_S$ is the set of tripartitions of $S$.

**Exact recovery condition (Theorem 4).** If a species tree $S^*$ satisfies, for each of its quartets $ab|cd$,

$$\sum_{G} w_G(ab|cd) > \max\Big(\sum_G w_G(ac|bd),\ \sum_G w_G(ad|bc)\Big),$$

then the greedy placement algorithm (which inserts taxa one at a time, each at the score-maximizing position, Theorem 3) outputs $S^*$; the divide-and-conquer version also outputs $S^*$ (Theorem 6) and runs in time $O(n^{1.5 + \epsilon} k H)$ with high probability, $H$ the average gene-tree height (Theorem 5).

## Depends on

- [Quartet score](../../../../quartet-support-and-determination-of-trees-by-qu/quartet-score.md)
- [The species quartet maximizes quartet support](../../../../../coalescent-theory/multispecies-coalescent/split-01-most-probable.md)

## Expansion

The unweighted score is the classical quartet support maximized by ASTRAL. With weights, the combinatorial shortcut that counts shared quartets at each gene-tree node no longer applies, so the optimization is reorganized around optimal single-taxon placement: by Theorem 3 inserting a new taxon into a fixed backbone at the best of all positions can be done exactly by a traversal with counters, and repeating this greedily gives a heuristic that is nevertheless exact under the condition of Theorem 4. That condition holds with probability tending to one as $k \to \infty$ whenever each per-quartet weighted score is a consistent estimator of the species quartet (a union bound over the $\binom n4$ quartets), which is how consistency of the score transfers to the algorithm. The factor $\frac12$ in the decomposition corrects for each quartet being anchored at two nodes of $S$.

## Sources

- C. Zhang, S. Mirarab, "Weighting by gene tree uncertainty improves accuracy of quartet-based species trees", Molecular Biology and Evolution (2022), Materials and Methods, Eqs. (1)–(5), "Optimization Algorithm" (tripartition score), Theorems 3–6 and Remarks 1–2, <https://doi.org/10.1093/molbev/msac215> (PMC9750496).
