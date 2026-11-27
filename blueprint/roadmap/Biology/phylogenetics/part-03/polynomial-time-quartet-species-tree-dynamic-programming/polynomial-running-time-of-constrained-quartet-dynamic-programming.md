# Polynomial running time of constrained quartet dynamic programming

Let $L$ be a set of $n$ taxa and $\mathcal G$ a set of $k$ unrooted gene trees on $L$. The **quartet species-tree problem** asks for an unrooted tree $t$ maximizing $\sum_{g \in \mathcal G} |Q(g) \cap Q(t)|$, where $Q(\cdot)$ is the set of induced quartet topologies; it is NP-hard. The **constrained** version fixes a family $X$ of clusters closed under complement ($A \in X \Rightarrow L \setminus A \in X$), allows only species-tree bipartitions from $X$, and considers the tripartitions

$$Y = \{(A' \mid A \setminus A' \mid L \setminus A) : A' \subset A,\ A, A', A \setminus A' \in X\}.$$

It is solved exactly by the recursion

$$V(A) = \max_{(A' \mid A \setminus A' \mid L \setminus A) \in Y} \Big[V(A') + V(A \setminus A') + w(A' \mid A \setminus A' \mid L \setminus A)\Big], \qquad V(A) = 0 \text{ if } |A| = 1,$$

with $w$ the tripartition weight against all gene-tree nodes.

Let $E$ be the multiset of distinct gene-tree node partitions with their multiplicities $c$, and $D = \sum_{(M, c) \in E} |M|$, the total degree of the distinct nodes; $D = O(nk)$.

**Lemma (shared-node scoring).** Representing all distinct gene-tree clusters as a polytree and computing $|W \cap A|$, $|W \cap B|$, $|W \cap C|$ for each cluster $W$ by the post-order recursion $|W \cap A| = \sum_{Z \in \mathrm{children}(W)} |Z \cap A|$, the weight $w(T) = \sum_{(M,c) \in E} c \cdot \mathrm{QI}(T, M)$ is computed in $\Theta(D)$ time.

**Theorem.** By the Kane–Tao bound $|Y| = O(|X|^{1.726})$ (exponent $3/\log_3(27/4) \approx 1.726$). If $X$ is built so that $|X| = O(nk)$, the constrained dynamic program runs in time

$$O\big(D\,(nk)^{1.726}\big)$$

for binary and multifurcating gene trees alike.

**Pruning bound.** For every cluster $A$, $V(A) \le U(A) = \tfrac12 w(A \mid A \mid L) - \tfrac13 w(A \mid A \mid A)$, a quantity computable without recursion; a resolution $A''$ need not be expanded once $U(A'') + U(A \setminus A'') + w(A'' \mid A \setminus A'' \mid L \setminus A) \le V(A, A')$ for an already scored resolution $A'$.

## Depends on

- [Linear-time scoring of a tripartition against a polytomy](linear-time-scoring-of-a-tripartition-against-a-polytomy.md)
- [Total quartet support of a tree](../../quartet-support-and-determination-of-trees-by-qu/quartet-score.md)

## Expansion

The running time is dominated by computing $w$ for each of the $|Y|$ tripartitions. Identical clusters recurring across gene trees are scored once, weighted by multiplicity; each node costs time linear in its degree by the polytomy lemma, so one tripartition costs $\Theta(D)$. Combining with $|Y| = O(|X|^{1.726})$ and capping the heuristic enlargement of $X$ (a constant number of consensus rounds, and a quadratic polytomy-resolution step limited so that $\sum d_i^2 \le cn$) gives the polynomial bound; earlier versions could let $|X|$ grow exponentially. The pruning bound and an $\alpha$-relaxed variant with $V_\alpha(A) \le V(A) \le \alpha V_\alpha(A)$ trim the search without affecting the worst case. Consistency under the multispecies coalescent rests on the fact that an unrooted quartet species tree always matches the most likely unrooted quartet gene tree.

## Sources

- C. Zhang, M. Rabiee, E. Sayyari, S. Mirarab, "ASTRAL-III: polynomial time species tree reconstruction from partially resolved gene trees", BMC Bioinformatics 19 (Suppl 6) (2018) 153, Eqs. 1–2 and 7–8, Corollary 1, Lemma 2, Theorem 1 and the trimming bound (Methods), <https://doi.org/10.1186/s12859-018-2129-y>, PMCID PMC5998893.
