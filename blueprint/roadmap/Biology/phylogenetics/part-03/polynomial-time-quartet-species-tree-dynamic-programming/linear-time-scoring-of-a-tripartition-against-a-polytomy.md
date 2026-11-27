# Linear-time scoring of a tripartition against a polytomy

Let $L$ be a set of $n$ taxa. A **partition** $M = M_1 \mid M_2 \mid \cdots \mid M_d$ is a collection of $d$ pairwise disjoint nonempty subsets of $L$; each internal node of degree $d$ of an unrooted gene tree defines one (a polytomy when $d \ge 4$). A **tripartition** $T = (A \mid B \mid C)$ is a partition of $L$ with three parts, corresponding to an internal node of a binary species tree. Write

$$a_i = |A \cap M_i|, \qquad b_i = |B \cap M_i|, \qquad c_i = |C \cap M_i| \qquad (i \in [d]).$$

The quartet-intersection score of $T$ and $M$ is

$$\mathrm{QI}(T, M) = \sum_{i \in [d]} \; \sum_{j \in [d]\setminus\{i\}} \; \sum_{k \in [d]\setminus\{i,j\}} \frac{a_i + b_j + c_k - 3}{2}\, a_i b_j c_k ,$$

which counts (twice) the quartet topologies shared by a tree whose only internal node is $T$ and a tree whose only internal node is $M$. Evaluated literally it costs $\Theta(d^3)$.

**Lemma.** Let $S_a = \sum_i a_i$ and $S_{a,b} = \sum_i a_i b_i$, and define $S_b, S_c, S_{a,c}, S_{b,c}$ analogously. Then

$$\mathrm{QI}(T, M) = \sum_{i \in [d]} \binom{a_i}{2}\Big[(S_b - b_i)(S_c - c_i) - S_{b,c} + b_i c_i\Big] + \sum_{i \in [d]} \binom{b_i}{2}\Big[(S_a - a_i)(S_c - c_i) - S_{a,c} + a_i c_i\Big] + \sum_{i \in [d]} \binom{c_i}{2}\Big[(S_a - a_i)(S_b - b_i) - S_{a,b} + a_i b_i\Big],$$

so $\mathrm{QI}(T, M)$ can be computed in $\Theta(d)$ time.

**Corollary.** Since the degrees of all internal nodes of $k$ gene trees on $n$ leaves sum to $O(nk)$, the weight $w(T) = \sum_{g} \sum_{M \in N(g)} \tfrac12 \mathrm{QI}(T, M)$ of a tripartition against all gene trees is computable in $O(nk)$ time, whether or not the gene trees are binary.

## Expansion

The summand factors as $\frac{a+b+c-3}{2}abc = \binom{a}{2}bc + a\binom{b}{2}c + ab\binom{c}{2}$: a shared quartet takes two leaves from one matched block and one from each of two others. Fixing the block $i$ that contributes the pair from $A$, the remaining factor is $\sum b_j c_k$ over ordered pairs $j \ne k$ with $j, k \ne i$, which equals $(S_b - b_i)(S_c - c_i)$ minus the diagonal $\sum_{j \ne i} b_j c_j = S_{b,c} - b_i c_i$. The six prefix sums take $\Theta(d)$ time, after which each of the three sums is a single pass. This removes the $d^3$ penalty that made earlier implementations slow on gene trees with contracted low-support branches.

## Sources

- C. Zhang, M. Rabiee, E. Sayyari, S. Mirarab, "ASTRAL-III: polynomial time species tree reconstruction from partially resolved gene trees", BMC Bioinformatics 19 (Suppl 6) (2018) 153, Eqs. 3–6, Lemma 1 and Corollary 2, <https://doi.org/10.1186/s12859-018-2129-y>, PMCID PMC5998893.
