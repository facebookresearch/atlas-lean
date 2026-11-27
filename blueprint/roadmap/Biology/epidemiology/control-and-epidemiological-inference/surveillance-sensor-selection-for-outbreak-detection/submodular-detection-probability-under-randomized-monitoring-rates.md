# Submodular detection probability under randomized monitoring rates

Let $V = P \cup L$ be the agents (people $P$ and locations $L$) of a contact network, $n = |V|$, and let $I$ be a finite set of simulated outbreak cascades. In cascade $i$, agent $v$ is infected (or contaminated) on $\tau(v,i) \in \mathbb{Z}_{\ge 0}$ days. A **monitoring-rate vector** $r \in [0,1]^n$ tests agent $v$ independently each day with probability $r[v]$, at cost $c[v] > 0$ per unit rate. Then $v$ is detected in cascade $i$ with probability $1 - (1-r[v])^{\tau(v,i)}$, and the probability that cascade $i$ is detected by at least one agent is

$$P(i \mid r) = 1 - \prod_{v \in V} (1 - r[v])^{\tau(v,i)}.$$

**Detection problem.** Maximize $R(r) := \sum_{i \in I} P(i \mid r)$ subject to the budget $\sum_v r[v]\,c[v] \le B$, with $r$ on a discrete lattice of allowed rates.

**Theorem.**
1. The detection problem is NP-hard (set cover is a special case), and so is the analogous problem of maximizing $\sum_{i}[T_{\max} - D(i \mid r)]$ for the expected first detection day $D$.
2. $R$ is a monotone submodular lattice function: raising one coordinate of $r$ yields a smaller marginal gain at a componentwise larger $r$.
3. The algorithm that, for each feasible initial vector $r_0$, starts from $r = r_0$, repeatedly sets the (agent, rate) pair with the largest average marginal gain among the pairs still feasible until the budget is spent, and returns the best of the resulting vectors (the source\'s Algorithm 1, HaiDetect) achieves $R(\hat r) \ge (1 - 1/e)\,R(r^*)$ (Lemma 4). Plain greedy from $r_0 = 0$ alone does not: with unequal costs it can end at an arbitrarily small fraction of the optimum.
4. (Online bound.) For each agent let $\Delta_v = \max_{a \in [0,1]} [R(\hat r \vee a\chi_{\{v\}}) - R(\hat r)]$ with maximizer $\sigma_v$, order agents $s_1, s_2, \dots$ by decreasing $\Delta_v / (c[v]\sigma_v)$, and let $K$ be the first index with $\sum_{i \le K} c[s_i]\sigma_{s_i} > B$ and $\theta = \sum_{i < K} c[s_i]\sigma_{s_i}$. Then

$$R(r^*) \le R(\hat r) + \sum_{i=1}^{K-1} \Delta_{s_i} + \frac{B - \theta}{c[s_K]\,\sigma_{s_K}}\,\Delta_{s_K}.$$

The expected-detection-time objective is not submodular, so the greedy guarantee does not extend to it.

## Proof depends on

- [SET COVER is NP-complete](../../../../TheoryOfComputation/np-completeness/set-systems-and-location/set-cover/set-cover-np-complete.md)

## Expansion

Each $P(i \mid r)$ is one minus a product of factors $(1-r[v])^{\tau(v,i)}$ that are decreasing and log-concave in each coordinate, which makes the marginal gain of increasing $r[v]$ shrink as other coordinates grow; summing over cascades preserves monotone submodularity. The $(1 - 1/e)$ guarantee is the classical Nemhauser–Wolsey–Fisher bound transferred to lattice functions. The online bound uses submodularity to dominate the gain from moving $\hat r$ to $r^*$ by the best fractional-knapsack packing of single-coordinate improvements, which in practice is much tighter than $1-1/e$ and certifies when the greedy solution is optimal. The model treats hospital patients, staff and rooms as agents of a temporal bipartite contact network simulated for *C. difficile*.

## Sources

- B. Adhikari, B. Lewis, A. Vullikanti, J. M. Jiménez, B. A. Prakash, "Fast and near-optimal monitoring for healthcare acquired infection outbreaks", PLoS Computational Biology (2019), Eqs. (1)–(7), Problems 1–2 and Lemmas 1–6, <https://doi.org/10.1371/journal.pcbi.1007284>, PMCID PMC6762212.
