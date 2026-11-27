# Poisson-mixture limits for the longest edges of a Galton–Watson genealogical tree

**Setting.** A continuous-time Galton–Watson process starts from one particle; each particle lives an $\mathrm{Exp}(\beta)$ time and is then replaced by $\xi$ offspring with $\mathbb{P}(\xi = k) = p_k$, independently. Assume $m = \mathbb{E}\xi > 1$ and $\mathbb{E}[\xi\log\xi] < \infty$. Let $N_t$ be the population size, so $M_t = e^{-(m-1)\beta t}N_t$ is a martingale with limit $M_\infty$, positive exactly on survival. The genealogical tree $\mathcal{T}_t$ has one edge per particle born by time $t$; *pendant* edges belong to particles alive at $t$ and *interior* edges to the others. For a length $l$, let $N_t^l$, $\hat N_t^l$, $\tilde N_t^l$ count pendant, interior and all edges of $\mathcal{T}_t$ longer than $l$, and let $L_t^{(k)}$, $\hat L_t^{(k)}$, $\tilde L_t^{(k)}$ be the $k$-th longest pendant, interior and overall edge lengths. Put

$$\alpha^* = 1 - \frac1m.$$

**Theorem.** Fix $x \in \mathbb{R}$ and let $l = \alpha^* t + x$. Conditionally on survival, as $t \to \infty$,

$$N_t^l \Rightarrow V_x, \qquad \hat N_t^l \Rightarrow \hat V_x, \qquad \tilde N_t^l \Rightarrow \tilde V_x,$$

where $V_x$, $\hat V_x$, $\tilde V_x$ are Poisson variables with random means

$$e^{-m\beta x}M_\infty, \qquad \frac{1}{m-1}e^{-m\beta x}M_\infty, \qquad \frac{m}{m-1}e^{-m\beta x}M_\infty,$$

mixed over the law of $M_\infty$ given $M_\infty > 0$. Consequently, for every $k \ge 1$, $L_t^{(k)} - \alpha^* t \Rightarrow W^{(k)}$ with

$$\mathbb{P}\big(W^{(k)} \le x \mid \text{survival}\big) = \mathbb{E}\Big[\sum_{j=0}^{k-1}\frac{\big(e^{-m\beta x}M_\infty\big)^j}{j!}\,e^{-e^{-m\beta x}M_\infty}\ \Big|\ M_\infty > 0\Big],$$

and likewise for interior and overall edges with $M_\infty$ replaced by $M_\infty/(m-1)$ and $mM_\infty/(m-1)$. Almost surely on survival, $L_t^{(k)}/t$, $\hat L_t^{(k)}/t$ and $\tilde L_t^{(k)}/t$ all converge to $\alpha^*$.

## Proof sketch

A pendant edge longer than $l$ is a particle alive at $t$ that has not branched since time $t - l$. At time $t - l$ there are about $M_\infty e^{(m-1)\beta(t-l)}$ particles, each surviving unbranched with probability $e^{-\beta l}$, so the mean count is $M_\infty e^{(m-1)\beta t - m\beta l}$, which is of order one exactly when $l = (1 - 1/m)t + x$, giving the mean $e^{-m\beta x}M_\infty$. These rare events are nearly independent, hence the Poisson limit given $M_\infty$. Interior edges longer than $l$ come from particles that branched between $t - \cdot$ and $t$ after a long life; summing over branching times contributes the extra factor $1/(m-1)$, and all edges give the sum $1 + 1/(m-1) = m/(m-1)$. For a birth–death process with birth rate $\lambda$ and death rate $\mu$ this recovers the earlier centring $\frac12(1 - \mu/\lambda)t$ for long pendant edges of phylogenetic trees.

## Sources

- Sergey Bocharov and Simon C. Harris, "Long edges in Galton–Watson trees", *Journal of Applied Probability* 62 (2025), 1053–1068, <https://doi.org/10.1017/jpr.2024.110>. Preprint version: arXiv:2308.16168 (2023), Section 1 (model, $M_t$, $\alpha^*$), Theorem 1.2, Corollary 1.4 and Theorem 1.6, Propositions 3.1 and 3.2, <https://doi.org/10.48550/arXiv.2308.16168>.
