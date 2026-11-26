# Threshold optimality for ergodic harvesting with biomass-dependent quotas

Let the uncontrolled biomass follow the diffusion

$$dX_t = \mu(X_t)\,dt + \sigma(X_t)\,dW_t, \qquad X_0 = x > 0,$$

with $\mu, \sigma$ locally Lipschitz and $\sigma^2 > 0$ on $(0,\infty)$. Assume: $\infty$ is a natural boundary and $0$ is natural or entrance-not-exit; $\mu$ is unimodal, increasing on $[0,x^*)$ and decreasing on $(x^*,\infty)$, with $\mu(0) \ge 0$ and $\lim_{x\to\infty}\mu(x) < 0$; the speed measure $m$ has finite total mass; and the scale density satisfies $S'(\infty) = \infty$. Let the **quota** $k : [0,\infty) \to [0,\infty)$ be non-decreasing with $k(x) > 0$ for $x > 0$.

An admissible harvesting strategy is a continuous, nondecreasing, adapted process $\nu$ with $\nu_0 = 0$ and

$$d\nu_t \le k(X^\nu_t)\,\mathbf 1_{\{t \le \tau^\nu\}}\,dt, \qquad dX^\nu_t = \mu(X^\nu_t)\,dt - d\nu_t + \sigma(X^\nu_t)\,dW_t,$$

where $\tau^\nu$ is the extinction time. The payoff is the long-run average yield $J(x;\nu) = \liminf_{T\to\infty} T^{-1}\,\mathbb E_x[\nu_T]$.

Let $m_0$ be the speed measure of the fully harvested diffusion (drift $\mu - k$), and define

$$G(x) = \frac{\int_0^x \mu(y)\,m(dy)}{\int_0^x m(dy)}, \qquad H(x) = \frac{\int_x^\infty \mu(y)\,m_0(dy)}{\int_x^\infty m_0(dy)}, \qquad \overline\mu = \frac{\int_0^\infty \mu(y)\,m_0(dy)}{\int_0^\infty m_0(dy)}.$$

**Theorem.**

1. (Always harvest at the cap.) If the fully harvested diffusion cannot reach $0$, $m_0$ is finite, $S_0'(0+) = \infty$, and $\overline\mu \le \mu(0)$, then the strategy $d\nu^0_t = k(X_t)\,dt$ of harvesting at the maximal rate at all times is optimal, with value $\sup_\nu J(x;\nu) = \overline\mu$.
2. (Threshold strategy.) If $m_0$ is finite and $\mu(0) < \overline\mu$, then $G$ is increasing below and decreasing above the unique point $x'$ with $G(x') = \mu(x')$, there is a unique $b^* \in (0, x')$ with $G(b^*) = H(b^*)$, and with $\beta^* := G(b^*) = H(b^*)$,

$$\sup_\nu \liminf_{T\to\infty} \frac1T\,\mathbb E_x\Big[\int_0^T d\nu_t\Big] = \beta^*,$$

attained by the threshold strategy that does nothing on $(0,b^*)$ and harvests at rate $k(X_t)$ on $[b^*,\infty)$.

So, unlike the unconstrained singular problem, the optimal threshold may be $b^* = 0$.

## Expansion

Item 1 is a verification argument: the function $u$ with $u' = 1 + S_0'(x)\int_x^\infty(\mu - \overline\mu)\,dm_0$ satisfies $0 \le u' \le 1$, and Itô's formula with localization gives $\mathbb E_x[\nu_T] \le \overline\mu T + O(1)$ for every admissible $\nu$. For item 2 one solves the free-boundary problem $\mathcal A u = \beta$ with $u' \ge 1$ on $(0,b)$ and $\mathcal A_0 u = \beta - k$ with $u' \le 1$ on $[b,\infty)$; $C^1$ fit at $b$ forces $G(b) = \beta = H(b)$. The shapes of $G$ and $H$ (each crossing $\mu$ once) give uniqueness, and approximate solutions $u_\beta$ for $\beta \downarrow \beta^*$ supply the upper bound.

## Sources

- Erik Ekström, Dante Mata, Harto Saarinen, "Resource Extraction from a Stochastic Population with Harvesting Quotas", arXiv (2026). Theorem 4.4, Lemmas 5.2–5.4, Proposition 5.6, Theorem 5.7. <https://doi.org/10.48550/arXiv.2608.17778>
