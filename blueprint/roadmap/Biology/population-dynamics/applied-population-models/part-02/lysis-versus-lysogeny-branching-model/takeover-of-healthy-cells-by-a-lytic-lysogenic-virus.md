# Takeover of healthy cells by a lytic–lysogenic virus

**Model.** In the healthy/infected cell process $(X(t), Y(t))$ of the lysis–lysogeny branching model, healthy cells are replaced by $k$ healthy cells at rate $p_k$, infected cells by $k \ge 1$ infected cells at rate $p_k$, and an infected cell dies at rate $p_0 + \lambda$ ($\lambda \ge 0$), bursting and converting $\min(X, \Gamma)$ healthy cells into infected cells, where $\Gamma \sim (\gamma_k)_{k \ge 0}$ independently. Let $\xi \sim (p_k)$ and

$$\alpha = E(\xi) - 1$$

be the Malthusian parameter of the healthy population in the absence of virus; the infected population, while healthy cells are abundant, has Malthusian parameter

$$\beta = \alpha + p_0 E(\Gamma) + \lambda\big(E(\Gamma) - 1\big),$$

and after healthy cells vanish it is a branching process with Malthusian parameter $\alpha - \lambda$. Let $T_X = \inf\{t \ge 0 : X(t) = 0\}$.

**Proposition.** Suppose $p_0 > 0$ or $\lambda > 0$, and $X(0), Y(0) \ge 1$. Then

$$P(T_X < \infty) = 1 \iff \alpha \le 0 \ \text{ or } \ \gamma_0 = 0.$$

So when every lysis infects at least one available healthy cell, the virus eliminates the healthy population almost surely; otherwise a supercritical healthy population survives with positive probability.

## Expansion

If $\alpha \le 0$ the healthy cells form a (sub)critical branching process even before any infection and die out almost surely. If $\alpha > 0$ and $\gamma_0 = 0$, then $E(\Gamma) \ge 1$ and $\beta > \alpha$ when $p_0 > 0$ or $\lambda > 0$: on survival the infected population grows strictly faster, and each lysis removes healthy cells, so $X$ is eventually driven to $0$. If $\gamma_0 > 0$, with positive probability every infected cell dies by lysis without infecting anyone before the healthy population takes off.

## Depends on

- [Extinction probability of a virus is increasing in its lytic aggressiveness](extinction-probability-of-a-virus-is-increasing-in-its-lytic-aggressiveness.md)

## Sources

- J. E. Björnberg, T. Britton, E. I. Broman and E. Natan, "A stochastic model for virus growth in a cell population", arXiv:1112.4694 (2011), Proposition 3.1, Proposition 3.2 and the Malthusian parameters in Section 3, <https://doi.org/10.48550/arXiv.1112.4694>.
