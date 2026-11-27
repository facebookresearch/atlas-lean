# Tarone testability pruning for closed connected subgraphs

**Data.** There are $n$ samples $(x_i, y_i, c_i)$ with binary covariates $x_i \in \{0,1\}^p$ (presence of $p$ genomic units such as compacted de Bruijn graph nodes), a binary phenotype $y_i$ ($n_1$ and $n_2$ samples in the two classes) and a population label $c_i \in \{1, \dots, J\}$. The covariates are the vertices of a connected graph $G = (V, E)$. For $v \in V$ let $I(v) = \{i : x_{iv} = 1\}$, and for a connected subgraph $S$ let $I(S) = \bigcup_{v \in S} I(v)$ be the samples carrying at least one of its units (a disjunction; conjunctions follow by complementing $x$).

**Closed connected subgraphs.** A connected subgraph $S$ is *closed* if no edge $(v_1, v_2)$ with $v_1 \in S$, $v_2 \notin S$ satisfies $I(S \cup \{v_2\}) = I(S)$. Every connected subgraph $S$ has a unique closed connected subgraph $\mathrm{cl}(S) \supseteq S$ with $I(\mathrm{cl}(S)) = I(S)$. Let $\mathcal{C}$ be the set of closed connected subgraphs (CCSs). For each $S \in \mathcal{C}$ one tests $H_0(S) : I(S) \perp Y \mid C$ with the Cochran–Mantel–Haenszel (CMH) test, or with Fisher's exact test when $J = 1$, while controlling the family-wise error rate (FWER) at level $\alpha$.

**Minimal attainable p-values and Tarone's procedure.** A discrete test conditional on its margins has a smallest attainable p-value $p^\star(S) > 0$, which depends only on the margins. If $p^\star_i > \delta$, then $P(p_i \le \delta) = 0$. Let $m(k)$ be the number of *testable* hypotheses, those with $p^\star < \alpha/k$. Then FWER$(\alpha/k) \le m(k)\,\alpha/k$, so rejecting at threshold $\delta = \alpha/k$ controls the FWER at level $\alpha$ whenever $m(k) \le k$. Taking $k_0$ to be the smallest such $k$ maximizes rejections, and $k_0 \le N$ always, where $N = |\mathcal{C}|$ is the number of tested CCSs, so the procedure never rejects less than Bonferroni.

**Monotone pruning.** For Fisher's test, $p^\star$ is strictly increasing in $|I(S)|$ once $|I(S)| \ge \max(n_1, n_2)$, and $S \subseteq S'$ implies $I(S) \subseteq I(S')$. So once such an $S$ is untestable at the current threshold, so is every CCS containing it, and the search below $S$ can be cut. The CMH minimal p-value (computable in $O(J)$ from the margins $x_{S,j} = |I(S) \cap \{c = j\}|$, $n_{1,j}$, $n_{2,j}$) is not monotone. One prunes instead with the envelope

$$\tilde p^\star(S) = \min_{x' \ge x_S} p^\star(x'),$$

which is monotone because $S \subseteq S'$ implies $x_{S'} \ge x_S$ componentwise.

**Lemma (envelope optimum).** For any connected subgraph $S$, the envelope is attained at some $x^{*}_{S'}$ with

$$x^{*}_{S',j} \in \bigl\{\max(x_{S,j}, n_{1,j}),\ \max(x_{S,j}, n_{2,j}),\ n_j\bigr\} \qquad (j = 1, \dots, J),$$

where $n_j = n_{1,j} + n_{2,j}$. The envelope is therefore computable, and usable for pruning, for every subgraph, not only those with $x_{S,j} \ge \max(n_{1,j}, n_{2,j})$ in all strata, the earlier condition, which this result recovers as a special case.

## Depends on

- [De Bruijn multigraph of a string](../../../../../bioinformatics/de-bruijn-graph-genome-assembly/de-bruijn-edges.md)

## Expansion

Tarone's bound is the union bound restricted to hypotheses that can be rejected at all: untestable hypotheses contribute zero. The threshold $k_0$ is found in one pass. Grow the set $R$ of hypotheses testable at $\alpha/k$, increase $k$ whenever $|R| > k$, and drop hypotheses that become untestable. With monotone $p^\star$ or $\tilde p^\star$, that pass can skip every superset of an untestable CCS, so most of the exponentially large $\mathcal{C}$ is never visited. Breadth-first traversal prunes more than depth-first, because finishing a level raises $k$, which lowers the threshold for all CCSs at the next level, and the levels parallelize. On a bacterial dataset with a strongly imbalanced population, the relaxed envelope enumerates about an order of magnitude fewer CCSs when the class ratio is below $0.02$.

## Sources

- H. Roux de Bézieux, L. Lima, F. Perraudeau, A. Mary, S. Dudoit, L. Jacob, "CALDERA: finding all significant de Bruijn subgraphs for bacterial GWAS", Bioinformatics 38 (2022) i36–i44, Definition 1, Lemma 1, Sections 2.1–2.3, Algorithm 2, Section 3.5 and Lemma 4, <https://doi.org/10.1093/bioinformatics/btac238> (PMC9235473).
