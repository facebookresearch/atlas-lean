# treeSeg active-node estimation with multiscale likelihood-ratio control

Let $T$ be a fixed rooted binary tree with leaves $1,\dots,n$ (ordered consistently with $T$, independently of the data) and let $\mathrm{Off}(v)$ be the leaves below node $v$. At each leaf one observes an independent trait $Y_i \sim \mathrm{Bern}(p_i)$, where

$$p \in \mathcal{S}(T) = \Big\{ \big(p_0 + \textstyle\sum_{j=1}^{k} c_j \mathbb{1}\{i \in \mathrm{Off}(v_j)\}\big)_{i=1}^n \in [0,1]^n \Big\};$$

the nodes $v_1,\dots,v_k$ are **active nodes** (clades where the success probability shifts), each assumed to have at least one descendant leaf attaining its own probability, and $k(p)$ is their number.

For a candidate $p$, let $T_i^j$ be the local log-likelihood-ratio statistic for "all $p_i, \dots, p_j$ equal the candidate's constant value" on each run of leaves $[i,j]$ inside a subtree where the candidate is constant, and define the multiscale statistic

$$T_n(p, Y) = \max_{[i,j]} \Big( \sqrt{2T_i^j} - \mathrm{pen}\big(\tfrac{j-i+1}{n}\big) \Big), \qquad \mathrm{pen}(x) = \sqrt{2\log(e/x)} .$$

Over signals with segments of length at least $n\lambda$, $T_n$ is asymptotically dominated by $M = \sup_{0 \le s < t \le 1} \big( |B(t)-B(s)|/\sqrt{t-s} - \sqrt{2\log(e/(t-s))} \big)$ for Brownian motion $B$, whose quantile $q_{1-\alpha}$ is signal-free. **treeSeg** estimates

$$\hat k = \min\{k(p) : p \in \mathcal{S},\ T_n(p,Y) \le q_{1-\alpha}\},$$

and then $\hat p$ as the maximum-likelihood vector among those with $k(p) = \hat k$ and $T_n(p,Y) \le q_{1-\alpha}$ (the set $H(q_{1-\alpha})$).

**Theorem 1 (overestimation control).** For fixed minimal scale $\lambda > 0$, $\limsup_{n\to\infty} \sup_{p \in \mathcal{S}_\lambda} \Pr\big(\hat k > k(p)\big) \le \alpha$.

**Theorem 2 (underestimation).** If in addition distinct segment probabilities differ by more than $\delta > 0$, then $\sup_{p \in \mathcal{S}_{\lambda,\delta}} \Pr(\hat k < k(p)) \le C_1 e^{-C_2 n}$ with constants depending only on $\alpha, \lambda, \delta$.

Consequently $H(q_{1-\alpha})$ is an asymptotically honest $(1-\alpha)$ confidence set for the whole segmentation, yielding simultaneous confidence bands for $p$; the localization of active nodes is optimal up to a set of order $\log n$ leaves.

## Expansion

Because a node could shift its clade's probability by an arbitrarily small amount, the existence of an extra active node can never be excluded; the method therefore reports the fewest active nodes compatible with the data at level $\alpha$, so that every reported clade is present with probability at least $1-\alpha$. The scale penalty balances short and long segments so that the maximum is equally likely to occur at every scale, which makes the limit distribution independent of the unknown signal. The construction extends the SMUCE multiscale change-point estimator from totally ordered sequences to tree-indexed data and generalizes to other exponential-family traits.

## Sources

- M. Behr, M. A. Ansari, A. Munk and C. Holmes, "Testing for dependence on tree structures", Proceedings of the National Academy of Sciences 117 (2020), Methods, Model 1, Eqs. (1)–(12) and Theorems 1–4, <https://doi.org/10.1073/pnas.1912957117>, PMCID: PMC7211961.
- K. Frick, A. Munk and H. Sieling, "Multiscale change point inference", Journal of the Royal Statistical Society, Series B 76 (2014), 495–580, <https://doi.org/10.1111/rssb.12047>.
