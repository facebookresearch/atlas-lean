# Optimality of $\beta$–$\gamma$ impulse harvesting strategies

**Setting.** A population (or other stock) follows a one-dimensional diffusion $dX_t = b(X_t)\,dt + \sigma(X_t)\,dW_t$ on $]0,\infty[$, with $b,\sigma$ locally Lipschitz, $\sigma > 0$, $0$ inaccessible and $\infty$ natural. A harvester chooses an increasing piecewise-constant càdlàg process $\zeta$ (impulsive harvests), so $dX^\zeta_t = b(X^\zeta_t)\,dt - d\zeta_t + \sigma(X^\zeta_t)\,dW_t$, and maximizes

$$J_x(\zeta) = \mathbb E_x\Big[\int_0^\infty e^{-\Lambda^\zeta_t}h(X^\zeta_t)\,dt + \sum_{t\ge0} e^{-\Lambda^\zeta_t}\Big(\int_0^{\Delta\zeta_t} k(X^\zeta_{t-} - u)\,du - c\,\mathbf 1_{\{\Delta\zeta_t > 0\}}\Big)\Big], \qquad \Lambda^\zeta_t = \int_0^t r(X^\zeta_u)\,du,$$

where $h$ is a running payoff (e.g. the value of a standing stock), $k$ the marginal revenue of harvested units, $c > 0$ a fixed cost per intervention and $r \ge r_0 > 0$ a state-dependent discount rate. A **$\beta$–$\gamma$ strategy** with $0 < \gamma < \beta$ takes no action while $X < \beta$ and, whenever $X \ge \beta$, harvests impulsively down to $\gamma$.

**Theorem (Theorem 10).** Under Assumptions 1–4 on the data, let $\Theta = h + \mathcal L\big(\int_0^\cdot k(s)\,ds\big)$, where $\mathcal L u = \frac12\sigma^2u'' + bu' - ru$ is the discounted generator (so $\mathcal L\varphi = \mathcal L\psi = 0$ for the fundamental solutions $\varphi, \psi$), assumed to make $\Theta/r$ unimodal, and let $\underline x$ be the critical point of Lemma 4 at which $\frac{d}{dx}\frac{R'_\Theta}{\psi'}$ changes sign ($R_\Theta$ the expected discounted integral of $\Theta$ along the uncontrolled diffusion, $\psi$ the increasing fundamental solution). The value function $\sup_\zeta J_x(\zeta)$ is given explicitly in terms of $R_h$, $R_\Theta$ and $\psi$, and:
1. if $\underline x < \infty$ and $c < c^\star$ (an explicit threshold), the $\beta^\star$–$\gamma^\star$ strategy is optimal, where $\gamma^\star(c)$ is strictly decreasing and $\beta^\star(c)$ strictly increasing in $c$ and both solve an explicit free-boundary system (Lemma 6);
2. if $\underline x < \infty$, $c \ge c^\star$ and the problem data are as in Lemma 8, no optimal strategy exists, but $\beta^\circ$–$\varepsilon_n$ strategies with $\varepsilon_n \downarrow 0$ are $\varepsilon$-optimal (harvest everything when the stock reaches $\beta^\circ$);
3. in the remaining cases of Lemma 9 (including $\underline x = \infty$, or a fixed cost above the relevant threshold), never harvesting, $\zeta^\star = 0$, is optimal when a limiting constant $K_\infty = 0$, while for $K_\infty > 0$ no optimal strategy exists and only $\varepsilon$-optimal strategies do.

For a strategy with $0 < \gamma < \beta$ and $x < \beta$ (Theorem 5), the payoff is $R_h(x) + \frac{\psi(x)}{\psi(\beta) - \psi(\gamma)}\big(R_h(\gamma) - R_h(\beta)\big)$ plus the analogous discounted revenue term, which reduces the optimization over strategies to a two-variable optimization over $(\beta,\gamma)$.

## Expansion

Between interventions the state is an uncontrolled diffusion, and each cycle from $\gamma$ up to $\beta$ restarts the process, so the payoff of a $\beta$–$\gamma$ strategy is a renewal sum whose discount factor is $\psi(\gamma)/\psi(\beta)$, the Laplace transform of the hitting time of $\beta$. Optimizing over $(\beta,\gamma)$ yields smooth-fit conditions at $\beta$ and a first-order condition at $\gamma$, which together with the fixed cost form the free-boundary system; existence of a solution requires that holding stock eventually becomes less profitable than harvesting, which is what a finite $\underline x$ encodes. The fixed cost $c$ makes the problem one of impulse rather than singular control: small $c$ gives a nondegenerate harvesting band, large $c$ pushes the optimal behaviour toward rare complete harvests that can only be approached, not attained.

## Sources

- Zhesheng Liu and Mihail Zervos, "The solution to an impulse control problem motivated by optimal harvesting", arXiv:2403.17875 (2024), Sections 1–5, Assumptions 1–4, Definition 1, Lemmas 4, 6, 8 and 9, Theorems 5 and 10, <https://doi.org/10.48550/arXiv.2403.17875>. Published version: Journal of Mathematical Analysis and Applications 542 (2025) 128809, <https://doi.org/10.1016/j.jmaa.2024.128809>.
