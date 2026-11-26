# Gene tree probability as a sum over compact coalescent histories

Let $T_s$ be a rooted species tree with branches $b=1,\dots,m$ of lengths $\lambda_b$ in coalescent units, and $T_g$ a rooted bifurcating gene tree topology on $n$ sampled lineages, each assigned to a leaf population. A **coalescent history** $h$ assigns each internal node of $T_g$ to a species-tree branch compatibly with ancestry; it determines the lower and upper lineage counts $u_b(h)\ge v_b(h)$ of every branch and the set $C_b(h)$ of $c_b(h)=u_b(h)-v_b(h)$ coalescences on $b$. Degnan and Salter's formula is

$$P(T_g\mid T_s)=\sum_{h}\prod_{b=1}^{m}\frac{w_b(h)}{d_b(h)}\,p_{u_b(h)v_b(h)}(\lambda_b),\qquad d_b=\prod_{i=v_b+1}^{u_b}\binom i2,\qquad w_b(h)=c_b(h)!\prod_{x\in C_b(h)}\frac1{n_x(h,b)},$$

where $p_{uv}(T)$ is Tavaré's probability that $u$ lineages coalesce to $v$ within time $T$, $d_b$ counts all orders of pairwise mergers from $u_b$ to $v_b$ lineages, and $n_x(h,b)$ is the number of coalescences on $b$ in the subtree of $T_g$ below and including $x$ (so $w_b$ counts the merger orders consistent with $T_g$).

**Compact histories.** A **compact coalescent history** $ch$ records only the upper lineage counts $v_b$ of the non-root branches.

**Lemma.** A compact history determines all lower and upper lineage counts and all numbers of coalescences: leaf branches have $u_b$ equal to the sample size, $u_b=\sum_{x\in\mathrm{Desc}(b)}v_x$ for internal branches, $v_{\mathrm{root}}=1$, and $c_b=u_b-v_b$.

**Theorem.** With $H(ch)$ the histories mapping to $ch$,

$$P(T_g\mid T_s)=\sum_{ch}\prod_{b=1}^{m}\frac{p_{u_b(ch)v_b(ch)}(\lambda_b)}{d_b(ch)}\;C(ch),\qquad C(ch)=\prod_{b=1}^m c_b(ch)!\sum_{h\in H(ch)}\prod_{b}\prod_{x\in C_b(h)}\frac1{n_x(h)},$$

and the coalescent coefficient $C(ch)$ is computed by a recurrence over the nodes of $T_g$. The resulting CompactCH algorithm runs in $O(m^3n^{2m+1})$ time for bifurcating $T_g$, polynomial in $n$ when the number of species is fixed.

## Expansion

All histories in $H(ch)$ share the factors $p_{u_bv_b}(\lambda_b)/d_b$, which can be pulled out of the inner sum; only the combinatorial weights $w_b(h)$ differ. Their sum factorizes branch by branch once the counts of coalescences per branch are fixed, and a dynamic program over gene-tree nodes, tracking how many coalescences of each subtree fall on each candidate species branch, evaluates it. The number of compact histories is at most polynomial in $n$ for fixed $m$, whereas the number of coalescent histories grows exponentially, which explains the speedup for few populations with many lineages each; this makes exact likelihood-based inference of population trees from many haplotypes feasible.

## Depends on

- [The multispecies coalescent](../gene-tree-prob.md)
- [Tavaré's formula for the number of ancestral lineages](../../ancestral-lineage-counting-and-tavar-s-formula/tavare-prob.md)

## Sources

- Y. Wu, "An algorithm for computing the gene tree probability under the multispecies coalescent and its application in the inference of population tree", Bioinformatics 32(12) (2016) i225–i233, <https://doi.org/10.1093/bioinformatics/btw261>, PMCID PMC4908345. Eqs. (1)–(6), Lemma 3.1 and Theorem 3.2.
