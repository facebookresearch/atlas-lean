# Piecewise-deterministic waning-boosting process and its renewal equation

**Model.** The immune level $Y(a) \in (0, \infty)$ of an individual of age $a$ evolves as follows.

- *Waning*: between exposures $dY/da = g(Y)$ with $g : (0, \infty) \to (-\infty, 0)$ such that the flow $\pi(t, y)$ is defined for all $t \in \mathbb R$, with $\pi(t, y) \to 0$ as $t \to \infty$ and $\pi(t, y) \to \infty$ as $t \to -\infty$. Equivalently $T(y) = \int_{y_c}^{y} d\eta / g(\eta)$ satisfies $\pi(t, y) = T^{-1}(t + T(y))$. Example: $g(y) = -w y$, $\pi(t, y) = e^{-wt} y$.
- *Exposure*: exposures occur as a Poisson process of constant rate $\Lambda > 0$, independent of $Y$.
- *Boosting*: at an exposure the level jumps from $y$ to $f(y)$, where $f$ is $C^1$, $f(y) > y$, $f$ decreases on $(0, y_c)$ and increases on $(y_c, \infty)$, $f(y) \to \infty$ as $y \downarrow 0$, and $f(y) = y + \delta + o(1)$, $f'(y) = 1 + o(1)$ as $y \to \infty$. Low levels ($y < y_c$, symptomatic infection) give a large boost; high levels give a small one.

**Renewal equation.** The transition kernel $Q_t(y, \Gamma) = \mathbb P(Y(a + t) \in \Gamma \mid Y(a) = y)$ is independent of $a$ and satisfies

$$Q = Q^0 + B^1 \otimes Q,$$

where $Q^0_t(y, \Gamma) = e^{-\Lambda t}\, \delta_{\pi(t, y)}(\Gamma)$ (no exposure in $[a, a+t]$), $B^1_t(y, \Gamma) = \int_0^t \Lambda e^{-\Lambda \sigma}\, \delta_{f(\pi(\sigma, y))}(\Gamma)\, d\sigma$ (first exposure in $[a, a+t]$, recorded just after boosting), and $(\Phi \otimes \Psi)_t(y, \Gamma) = \int_{[0,t] \times (0,\infty)} \Phi_{ds}(y, dz)\, \Psi_{t-s}(z, \Gamma)$.

**Generation expansion.** Iterating gives $Q = \sum_{k \ge 0} Q^k$ with $Q^{k+1} = B^1 \otimes Q^k$, where $Q^k$ accounts for exactly $k$ exposures, and

$$Q^k_t\bigl(y, (0, \infty)\bigr) = \frac{(\Lambda t)^k}{k!}\, e^{-\Lambda t}, \qquad Q_t\bigl(y, (0, \infty)\bigr) = 1 .$$

## Expansion

Conditioning on whether the first exposure after age $a$ happens before $a + t$ gives the renewal equation directly: either there is none (probability $e^{-\Lambda t}$, level $\pi(t, y)$), or it happens at time $\sigma$ with density $\Lambda e^{-\Lambda \sigma}$, the level becomes $f(\pi(\sigma, y))$, and the process restarts. The mass identity follows by induction, since each generation integrates $\Lambda e^{-\Lambda s}$ against the previous Poisson weight, so the kernels are exactly the Poisson probabilities of $k$ events and sum to one. Under the extra condition $f'(y) g(y) / g(f(y)) < 1$ the kernels $Q^k$ with $k \ge 1$ have densities, which makes the induced semigroup on $L^1$ partially integral. For $g(y) = -wy$ and $f(y) = y(1 + \sigma_2 y^{-\sigma_1})$ ($\sigma_1 > 1$, $\sigma_2 > 0$) this condition holds.

## Sources

- O. Diekmann, W. F. de Graaf, M. E. E. Kretzschmar, P. F. M. Teunis, "Waning and boosting: on the dynamics of immune status", Journal of Mathematical Biology (2018), Section 2, hypotheses $H_\Lambda$, $H_f$, $H_g$ and Eqs. (2.1)–(2.7), Definitions 2.1–2.3 and renewal equation (2.12)–(2.13); Section 4, Lemma 4.3 (Eq. 4.4), condition (4.6), Lemmas 4.6–4.9. <https://doi.org/10.1007/s00285-018-1239-5> (PMC6280846).
