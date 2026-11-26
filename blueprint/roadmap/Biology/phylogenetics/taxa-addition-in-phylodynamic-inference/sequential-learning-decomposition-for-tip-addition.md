# Sequential learning decomposition for tip addition

**Setting.** Parameters $\Theta \sim \pi$ generate a genealogy $\mathcal G \mid \Theta \sim P_\Theta$ (a Markov genealogy process, e.g. a birth–death or coalescent model) with $f(\mathcal G)$ sampled tips $\{(x_i, t_i)\}$; a uniform random permutation $\Lambda$ orders the tips, and $\mathcal F_n$ is the $\sigma$-algebra of the sequence data on the first $n$ tips in this order. An *estimand* $K$ is *permutation-invariant* if it does not depend on $\Lambda$. A *sequential estimand* is a family $(K_n)_{n \le f(\mathcal G)}$, $K_n$ defined on the first $n$ tips (e.g. the tree of the sampled tips), with limit $K_\infty$ defined on the full genealogy.

**Theorem.**
1. *(Standard learning.)* $(\mathcal F_n)$ is a filtration, and for any square-integrable permutation-invariant $K$, $\mathrm{Var}(K \mid \mathcal F_n) \ge \mathbb E[\mathrm{Var}(K \mid \mathcal F_{n+1}) \mid \mathcal F_n]$ a.s.; more generally, for $K$ valued in a separable (pseudo)metric space, the conditional Fréchet variance $\inf_s \mathbb E[d^2(K, s) \mid \mathcal F_n]$ is a supermartingale.
2. *(Sequential decomposition.)* If $K_\infty$, $K_\infty - K_n$ and $K_\infty - K_{n+1}$ are square integrable, then a.s.

$$\begin{aligned}0 \le\ & \mathrm{Var}(K_n \mid \mathcal F_n) - \mathbb E[\mathrm{Var}(K_{n+1} \mid \mathcal F_{n+1}) \mid \mathcal F_n] + \mathrm{Var}(K_\infty - K_n \mid \mathcal F_n) - \mathbb E[\mathrm{Var}(K_\infty - K_{n+1} \mid \mathcal F_{n+1}) \mid \mathcal F_n]\\ &+ 2\bigl(\mathrm{Cov}(K_n, K_\infty - K_n \mid \mathcal F_n) - \mathbb E[\mathrm{Cov}(K_{n+1}, K_\infty - K_{n+1} \mid \mathcal F_{n+1}) \mid \mathcal F_n]\bigr),\end{aligned}$$

so the change in posterior variance of the moving target $K_n$ is offset by the change in uncertainty about its gap to the full-genealogy target; variance about $K_n$ itself can increase when the estimand changes structurally with $n$.
3. *(Event conditioning.)* For an event $E$ with $\mathbb P(E) > 0$, $V_k = \mathrm{Var}(K \mid \mathcal F_k)$ and $Z_k = \mathbb P(E \mid \mathcal F_k)$,

$$\mathbb E[V_n - V_{n+1} \mid E] = \mathbb E[V_n - V_{n+1}] + \frac{\mathrm{Cov}(V_n, Z_n) - \mathrm{Cov}(V_{n+1}, Z_{n+1})}{\mathbb P(E)},$$

so expected variance reduction can fail conditionally on informative events.
4. *(Irreducible oracle gap.)* Let $(K_n)$ be a scalar absorbing monotone sequential estimand (it stops changing after a random absorption time $\tau$) with $K_\infty - K_n$ of constant sign. If absorption is uncertain given all data, $0 < \mathbb P(\tau < \infty \mid \mathcal F_{f(\mathcal G)}) < 1$ on a set of positive probability, and the data alone do not separate the two cases in the conditional mean of $K_{f(\mathcal G)}$, then $\mathbb E\bigl[\mathrm{Var}(\mathbb E[K_\infty \mid \mathcal F'_{f(\mathcal G)}] \mid \mathcal F_{f(\mathcal G)})\bigr] > 0$, where $\mathcal F'$ is the oracle filtration that also reveals $\tau$: the analyst carries strictly positive excess uncertainty relative to the oracle.

## Expansion

Item 1 is the law of total variance applied along a filtration: conditioning on more data cannot increase expected posterior variance of a fixed target. Phylodynamic estimands such as the tree of the sampled tips, the time of the most recent common ancestor of the sample or the number of lineages are not fixed: they change as tips are added. Writing $K_{n+1} = K_\infty - (K_\infty - K_{n+1})$ and applying item 1 to $K_\infty$ produces the decomposition, and classifying sequential estimands by whether they are absorbing, monotone or mixed gives "learning classes" with different guarantees.

## Sources

- D. J. Pascall, "Sequential learning theory for Markov genealogy processes", arXiv:2603.09033 (2026), Propositions 1 and 2, Theorems 1, 2 and 3, Corollaries 1 and 2, <https://doi.org/10.48550/arXiv.2603.09033>.
