# Target associated k-set problem

**Problem.** Let $J = \{j_1, \dots, j_m\}$ be tumour samples and $G = \{g_1, \dots, g_n\}$ genes, with $A_g \subseteq J$ the samples in which gene $g$ is altered. Each sample has a target value $w_j \in \mathbb{R}$ (a normalized functional phenotype) and a penalty $p_j > 0$ with $p_j \ge -w_j$, as the source\'s penalty convention gives. For $S \subseteq G$ let $c_S(j) = |\{g \in S : j \in A_g\}|$ and $U_S = \bigcup_{g \in S} A_g$. The weight of $S$ is

$$W(S) = \sum_{j \in U_S} w_j - \sum_{j \in U_S} \big(c_S(j) - 1\big)\, p_j ,$$

rewarding coverage of high-target samples and penalizing samples covered more than once. The **target associated $k$-set problem** asks for $S$ with $|S| \le k$ maximizing $W(S)$.

**Theorem 1.** The target associated $k$-set problem is NP-hard.

**Greedy algorithm.** For $k$ stages, add the gene $g$ whose current weight $\sum_{j \in A_g} w_j$ is maximal and positive (stop early if none is positive), then reset $w_j \leftarrow -p_j$ for every $j \in A_g$.

**Proposition 1.** If $S^*$ is optimal and $\hat S$ is the greedy solution, then $W(\hat S) \ge W(S^*)/k$.

**Proposition 2.** The bound is tight: some instances have $W(\hat S) = W(S^*)/k$.

**Proposition 3 (planted recovery).** Suppose a set $H$ of $k$ genes has mutually exclusive alterations associated with the target, every other gene $g$ is altered in each sample independently with probability $p_g$, the targets satisfy $\sum_j w_j = 0$ and $|w_j| \le 1$, and the genes of $H$ satisfy the paper's separation assumptions. If $m \in \Omega(k^2 \ln(n/\delta))$ samples are given, the greedy algorithm returns $H$ with the high probability stated in the paper (failure probability controlled by $\delta$).

## Expansion

NP-hardness follows by reduction from the maximum weight submatrix problem: with $w_j = p_j = 1$, $W(S) = |U_S| - \sum_{g \in S} |A_g| + |U_S|$ coincides with that problem's objective of coverage minus overlap. The greedy stage weight is exactly the marginal gain of $W$, since after the reset a previously covered sample contributes $-p_j$, the penalty for covering it again; the first greedy pick alone is worth at least $W(S^*)/k$ because $W(S^*) \le \sum_{g \in S^*} \sum_{j \in A_g} w_j$ and later stages never decrease $W$, giving the $1/k$ guarantee. The planted-model result is a concentration argument: with enough samples, the empirical weights of planted genes exceed those of independently altered genes, uniformly over the $n$ genes and $k$ stages. Significance is assessed by permuting target values across samples while keeping the alteration sets fixed.

## Sources

- R. Sarto Basso, D. S. Hochbaum, F. Vandin, "Efficient algorithms to discover alterations with complementary functional association in cancer", PLoS Computational Biology 15 (2019) e1006802, Theorem 1, Propositions 1–3, Algorithm 1, <https://doi.org/10.1371/journal.pcbi.1006802> (PMC6550413).
