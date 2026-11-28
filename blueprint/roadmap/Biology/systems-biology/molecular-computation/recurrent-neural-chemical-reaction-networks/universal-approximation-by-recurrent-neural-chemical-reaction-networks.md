# Universal approximation by recurrent neural chemical reaction networks

**Setting.** Target dynamics $\dot{\bar x}_i = f_i(\bar x)$, $i = 1, \dots, N$, with $f$ Lipschitz on a compact box $\mathbb K = \prod_i \mathbb K_i \subset \mathbb R^N_{>0}$. A single-layer *recurrent neural chemical reaction network* (RNCRN) has executive species $X_1, \dots, X_N$ and neural species $Y_1, \dots, Y_M$ with mass-action rate equations

$$\dot x_i = \beta_i + x_i \sum_{j=1}^M \alpha_{i,j} y_j, \qquad \dot y_j = \frac{1}{\mu}\Bigl(\gamma + \theta_j y_j + \Bigl(\sum_{i=1}^N \omega_{j,i} x_i\Bigr) y_j - y_j^2\Bigr),$$

realised by reactions such as $\varnothing \to X_i$, $X_i + Y_j \to 2X_i + Y_j$ or $X_i + Y_j \to Y_j$ (according to the sign of $\alpha_{i,j}$), $\varnothing \to Y_j$, $2Y_j \to Y_j$, with $0 < \mu \ll 1$. The neural species relax quickly to the positive root $y_j = \sigma_\gamma\bigl(\sum_k \omega_{j,k} x_k + \theta_j\bigr)$ of the quadratic, where $\sigma_\gamma(z) = \frac12\bigl(z + \sqrt{z^2 + 4\gamma}\bigr)$ is a smooth rectifier, giving the reduced field

$$g_i(x) = \beta_i + x_i \sum_{j=1}^M \alpha_{i,j}\, \sigma_\gamma\Bigl(\sum_k \omega_{j,k} x_k + \theta_j\Bigr).$$

**Theorem.** Fix any $\beta \ge 0$ and $\gamma > 0$.
1. *(Quasi-static approximation.)* For every $\varepsilon > 0$ and every sufficiently large $M$ there are $\alpha^*, \omega^*, \theta^*$ with $\max_{x \in \mathbb K} |g_i(x) - f_i(x)| \le \varepsilon$ for all $i$.
2. *(Dynamical approximation.)* If the target solution $\bar x(t)$ stays in $\mathbb K$ on $[0, T]$, then for every sufficiently small fixed $\varepsilon^*$ there is $\mu_0 > 0$ such that for all $\mu \in (0, \mu_0)$ the RNCRN has a unique solution with $x(t) \in \mathbb K$ on $[0, T]$ and

$$\max_{t \in [0,T]} |x_i(t) - \bar x_i(t)| \le c_1 \varepsilon^* + c_2 \mu,$$

with $c_1, c_2$ independent of $\mu$.

## Expansion

Since $x_i > 0$ on $\mathbb K$, approximating $f_i$ amounts to approximating $(f_i - \beta_i)/x_i$, a continuous function, by a one-hidden-layer network with activation $\sigma_\gamma$, which is possible by the universal approximation theorem for non-polynomial activations. Tikhonov's theorem on singularly perturbed systems then shows that for small $\mu$ the fast neural species track their quasi-static values and the executive species follow the reduced field, so the full chemical system shadows the target trajectory. This gives a constructive route to designing synthetic biochemical circuits with prescribed dynamics, including oscillations and chaos.

## Sources

- A. Dack, B. Qureshi, T. E. Ouldridge, T. Plesa, "Recurrent neural chemical reaction networks that approximate arbitrary dynamics", *Cell Systems* 17(5) (2026), 101572, Theorem A.1 and the single-layer RNCRN construction, <https://doi.org/10.1016/j.cels.2026.101572> (preprint arXiv:2406.03456).
