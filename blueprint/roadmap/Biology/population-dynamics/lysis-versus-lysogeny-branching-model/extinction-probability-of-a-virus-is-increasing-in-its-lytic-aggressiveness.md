# Extinction probability of a virus is increasing in its lytic aggressiveness

**Model.** Let $(p_k)_{k \ge 0}$ and $(\gamma_k)_{k \ge 0}$ be probability distributions on $\{0,1,2,\dots\}$ with finite means, $p_1 \ne 1$, and let $\lambda \ge 0$. The continuous-time Markov chain $(X(t), Y(t))$ on $\mathbb{Z}_+^2$ counts healthy cells $X$ and virus-infected cells $Y$, with transitions from $(x,y)$:

- $(x,y) \to (x+k-1, y)$ at rate $x p_k$ for $k \ge 0$ (a healthy cell is replaced by $k$ healthy cells);
- $(x,y) \to (x, y+k-1)$ at rate $y p_k$ for $k \ge 1$ (an infected cell divides, passing the virus to all daughters: lysogeny);
- $(x,y) \to (x - (x \wedge k), \; y - 1 + (x \wedge k))$ at rate $y (p_0 + \lambda)\gamma_k$ for $k \ge 0$ (an infected cell dies, at the elevated rate $p_0 + \lambda$, bursts, and infects $\min(x,k)$ healthy cells: lysis).

The parameter $\lambda$ measures how aggressively the virus shortens its host's life. Let $\eta = \eta(\lambda, (\gamma_k)) = P(Y(t) \to 0)$ be the extinction probability of the infected population. Write $\gamma \preceq \gamma'$ if $\sum_{j \ge k} \gamma_j \le \sum_{j \ge k} \gamma'_j$ for all $k$ (stochastic order).

**Theorem.** Assume $\gamma_0 = 0$ (every lysis infects at least one healthy cell when one is available) and $X(0), Y(0) \ge 1$. Then $\eta$ is monotonically increasing in $\lambda \ge 0$ and in $(\gamma_k)$ with respect to $\preceq$. In particular the virus maximizes its long-run survival probability at $\lambda = 0$, i.e. by not shortening its host's life-cycle at all.

**Coupling.** For $0 \le \lambda_1 \le \lambda_2$ and $\gamma^{(1)} \preceq \gamma^{(2)}$ with $\gamma^{(1)}_0 = \gamma^{(2)}_0 = 0$, the processes $Z_i = (X_i, Y_i)$ with parameters $(\lambda_i, \gamma^{(i)})$ can be coupled so that, almost surely, with $T_i$ the time healthy cells run out in process $i$:

1. $T_2 \le T_1$;
2. $Y_2(t) \ge Y_1(t)$ for $t < T_2$;
3. $X_2(t) \le X_1(t)$ for $t \le T_2$;
4. $X_1(t) + Y_1(t) \ge X_2(t) + Y_2(t)$ for all $t \ge 0$.

After healthy cells are gone, infected cells form a Markov branching process with the extra death rate $\lambda$, so the more aggressive virus is left with a smaller total population and a worse branching law.

## Expansion

A more aggressive virus converts healthy cells faster (items 2–3), but every conversion is paid for by killing a host, and the total cell count is pathwise smaller (item 4). Once $X$ hits $0$ the infected population is a branching process with Malthusian parameter $\alpha - \lambda$, where $\alpha = E(\xi) - 1$ is the healthy-cell Malthusian parameter, so its extinction probability is increasing in both the starting size deficit and in $\lambda$. Without the hypothesis $\gamma_0 = 0$ monotonicity can fail: there are parameter choices with $\gamma^{(1)} \preceq \gamma^{(2)}$ but $\eta(\lambda, \gamma^{(1)}) > \eta(\lambda, \gamma^{(2)})$, and with $\lambda_1 < \lambda_2$ but $\eta(\lambda_1) > \eta(\lambda_2)$.

## Sources

- J. E. Björnberg, T. Britton, E. I. Broman and E. Natan, "A stochastic model for virus growth in a cell population", arXiv:1112.4694 (2011), Section 2.1 (Table of transition rates), Theorem 1.1, Proposition 3.3 and Theorem 4.1, <https://doi.org/10.48550/arXiv.1112.4694>.
