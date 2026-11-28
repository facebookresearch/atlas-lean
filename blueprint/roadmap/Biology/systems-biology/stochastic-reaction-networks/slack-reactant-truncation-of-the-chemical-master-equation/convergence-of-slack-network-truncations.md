# Convergence of slack-network truncations of the chemical master equation

**Slack network.** Let $(\mathcal{S}, \mathcal{C}, \mathcal{R}, \Lambda)$ be a stochastic reaction network on $d$ species with complex matrix $C$ ($|\mathcal{S}| \times |\mathcal{C}|$), connectivity matrix $S$ ($|\mathcal{C}| \times |\mathcal{R}|$, with $-S_{ir} = S_{jr} = 1$ when reaction $r$ goes from complex $i$ to complex $j$) and intensities $\lambda_{\nu\to\nu'}$. To impose a conservation bound $\vec w \cdot \vec x \le N$ with $\vec w \in \mathbb{Z}_{\ge 0}^d$, add a *slack reactant* $Y$ with stoichiometric row $D = u\mathbf{1}^\top - \vec w^\top C$ for a positive integer $u$; since $\mathbf{1}^\top S = 0$, the enlarged network $\widetilde C = \binom{C}{D}$ conserves $\vec w \cdot X + Y = N$. Its intensities are

$$\lambda^N_{\tilde\nu\to\tilde\nu'}(\vec x) = \lambda_{\nu\to\nu'}(\vec x)\,\mathbf{1}\{y \ge \tilde\nu_{d+1}\}, \qquad y = N - \vec w \cdot \vec x,$$

so rates are unchanged except at the boundary where $Y$ would become negative. Let $X$ and $X_N$ be the original and slack processes, both irreducible, started at the same $\vec x_0$ with $\vec w \cdot \vec x_0 < N$, on state spaces $\mathbb{S}$ and $\mathbb{S}_N \subset \mathbb{S}_{N+1}$; let $p(\vec x, t)$, $p_N(\vec x, t)$ be their laws.

**Theorem.**
1. For every $\vec x$ and $t \ge 0$, $\lim_{N\to\infty} |p(\vec x, t) - p_N(\vec x, t)| = 0$.
2. If $X$ has a stationary distribution $\pi$ and there is $h(t) \to 0$, independent of $N$, with $\|p_N(\cdot, t) - \pi_N\|_1 \le h(t)$, then $\|\pi - \pi_N\|_1 \to 0$.
3. Let $\tau$ and $\tau_N$ be the first passage times of $X$ to $K$ and of $X_N$ to $K \cap \mathbb{S}_N$. If $X$ has a stationary distribution $\pi$ and $\|\pi - \pi_N\|_1 \to 0$, then $|P(\tau > t) - P(\tau_N > t)| \to 0$ for every $t \ge 0$. If moreover $E\tau < \infty$ and $P(\tau_N > t) \le g(t)$ for all $N$ with $\int_0^\infty g < \infty$, then $E\tau_N \to E\tau$.
4. The hypotheses of item 3 hold if there are $V \ge 1$ on $\mathbb{S}$ and constants $C, D > 0$ with $V$ non-decreasing across the layers $\mathbb{S}_{N+1} \setminus \mathbb{S}_N$ and

$$\sum_{\nu\to\nu' \in \mathcal{R}} \lambda_{\nu\to\nu'}(\vec x)\big(V(\vec x + \nu' - \nu) - V(\vec x)\big) \le -C\,V(\vec x) + D.$$

## Proof sketch

Item 1 is a Hart–Tweedie type truncation argument: on any finite time horizon the slack process agrees with the original one until it first reaches the boundary $\{y < \tilde\nu_{d+1}\}$, and that boundary recedes to infinity as $N$ grows. Item 2 then exchanges $N \to \infty$ and $t \to \infty$ using the uniform mixing bound $h$. The Foster–Lyapunov drift condition in item 4 gives exponential ergodicity uniformly in $N$ and integrable tails of $\tau_N$. Unlike finite-state projection, the slack construction does not create extra absorbing states, so first-passage times remain meaningful.

## Sources

- Jinsu Kim, Jason Dark, German Enciso and Suzanne Sindi, "Slack reactants: A state-space truncation framework to estimate quantitative behavior of the chemical master equation", *The Journal of Chemical Physics* 153 (2020), 054117, <https://doi.org/10.1063/5.0013457>. Preprint version: arXiv:2005.05503 (2020), Section 3 (construction and intensities, Equations for $D = U - WC$ and the slack intensity), Theorems 5.1–5.4 (Section 5), <https://doi.org/10.48550/arXiv.2005.05503>.
