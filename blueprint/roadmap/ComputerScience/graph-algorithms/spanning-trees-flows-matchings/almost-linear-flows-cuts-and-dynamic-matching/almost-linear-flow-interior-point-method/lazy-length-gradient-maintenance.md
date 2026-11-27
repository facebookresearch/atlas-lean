# Lazy maintenance of IPM lengths and gradients with few coordinate changes

Let $\mathbf{f}^{(0)}, \mathbf{f}^{(1)}, \ldots, \mathbf{f}^{(\tau)}$ be flows in the domain of the potential with circulation steps $\mathbf{\Delta}^{(t)} = \mathbf{f}^{(t)} - \mathbf{f}^{(t-1)}$, and suppose every step changes the residual cost by a factor in $[1 - 1/(800m), 1 + 1/(800m)]$, that is $|\mathbf{c}^{\top}\mathbf{\Delta}^{(t)}| \le (\mathbf{c}^{\top}\mathbf{f}^{(t-1)} - F^*)/(800m)$. Fix $\varepsilon \in (0, 1/100]$ and maintain a scalar $r$ and vectors $\widetilde{\boldsymbol{\ell}}, \widetilde{\mathbf{g}}$ lazily as follows. Let $N = \max\{1, \lfloor\varepsilon m\rfloor\}$, so that $N = 1$, a refresh at every iteration, when $\varepsilon m < 1$. At iteration $0$ and at every $N$-th iteration after it set $r = \mathbf{c}^{\top}\mathbf{f}^{(t)} - F^*$ and recompute every coordinate; between these refreshes, recompute coordinate $e$ at iteration $t$ exactly when

$$
\widetilde{\boldsymbol{\ell}}_e \sum_{t' = \mathrm{last}_e + 1}^{t} |\mathbf{\Delta}^{(t')}_e| \ge \varepsilon,
$$

where $\mathrm{last}_e$ is the previous recomputation of $e$. Recomputing $e$ at a flow $\mathbf{f}$ sets $\widetilde{\boldsymbol{\ell}}_e = \boldsymbol{\ell}(\mathbf{f})_e$ and

$$
\widetilde{\mathbf{g}}_e = \frac{20m\,\mathbf{c}_e}{r} + \alpha(\mathbf{u}^+_e - \mathbf{f}_e)^{-1-\alpha} - \alpha(\mathbf{f}_e - \mathbf{u}^-_e)^{-1-\alpha}.
$$

Then at every iteration $t$, with $\mathbf{f} = \mathbf{f}^{(t)}$,

$$
\widetilde{\boldsymbol{\ell}} \approx_{1+3\varepsilon} \boldsymbol{\ell}(\mathbf{f}), \qquad r \approx_{1+\varepsilon} \mathbf{c}^{\top}\mathbf{f} - F^*, \qquad \Bigl\|\mathbf{L}(\mathbf{f})^{-1}\Bigl(\widetilde{\mathbf{g}} - \frac{\mathbf{c}^{\top}\mathbf{f} - F^*}{r}\,\mathbf{g}(\mathbf{f})\Bigr)\Bigr\|_\infty \le 6\alpha\varepsilon,
$$

where $\mathbf{a} \approx_\gamma \mathbf{b}$ means $\mathbf{b}/\gamma \le \mathbf{a} \le \gamma\mathbf{b}$ coordinatewise. Hence the rescaled gradient $(r/(\mathbf{c}^{\top}\mathbf{f} - F^*))\,\widetilde{\mathbf{g}}$ is within $6(1+\varepsilon)\alpha\varepsilon$ of $\mathbf{g}(\mathbf{f})$ in the $\mathbf{L}(\mathbf{f})^{-1}$-weighted $\ell_\infty$ norm. The number of threshold-triggered recomputations is at most $\varepsilon^{-1}\sum_{t=1}^{\tau}\|\widetilde{\mathbf{L}}^{(t-1)}\mathbf{\Delta}^{(t)}\|_1$, where $\widetilde{\mathbf{L}}^{(t-1)}$ is the diagonal matrix of the maintained lengths when step $t$ is taken, and there are $\lfloor\tau/N\rfloor + 1$ full refreshes, counting the one at iteration $0$.

## Proof sketch

Let $\overline{\mathbf{f}}$ be the flow at which coordinate $e$ was last recomputed. The threshold rule gives $\boldsymbol{\ell}(\overline{\mathbf{f}})_e|\mathbf{f}_e - \overline{\mathbf{f}}_e| < \varepsilon$; since residual capacities are at most $2U$ and $(2U)^{\alpha} \le 2$, this moves each residual capacity of $e$ by at most a factor $\exp(\pm 2\varepsilon)$, so the length changes by a factor at most $1 + 3\varepsilon$. Between a refresh and any later iteration before the next refresh at most $N - 1 \le \varepsilon m$ steps are taken (none when $N = 1$), so the residual cost changes by a factor at most $(1 + 1/(800m))^{\varepsilon m} \le e^{\varepsilon/800} \le 1 + \varepsilon$, giving $r \approx_{1+\varepsilon} \mathbf{c}^{\top}\mathbf{f} - F^*$. Comparing $\widetilde{\mathbf{g}}_e$ with $(\mathbf{c}^{\top}\mathbf{f} - F^*)/r$ times the exact gradient leaves an error from the factor $1 - (\mathbf{c}^{\top}\mathbf{f} - F^*)/r$ times the barrier gradient and an error from moving the barrier gradient from $\overline{\mathbf{f}}$ to $\mathbf{f}$; each is at most $3\alpha\varepsilon\boldsymbol{\ell}(\mathbf{f})_e$. Each threshold-triggered recomputation of $e$ consumes at least $\varepsilon$ of the accumulated $\widetilde{\boldsymbol{\ell}}$-weighted movement of $e$, which bounds their number.

## Depends on

- [Lengths and gradients induced by the l1 IPM potential](ipm-lengths-and-gradients.md)

## Sources

- Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, "Maximum Flow and Minimum-Cost Flow in Almost-Linear Time", FOCS (2022), arXiv:2203.00671.
- Jan van den Brand, Li Chen, Rasmus Kyng, Yang P. Liu, Richard Peng, Maximilian Probst Gutenberg, Sushant Sachdeva, Aaron Sidford, "A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow", FOCS (2023), arXiv:2309.16629.
