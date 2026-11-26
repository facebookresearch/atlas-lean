# Global weak solutions of porous-medium chemotaxis with logistic source on the whole space

**Model.** On $\mathbb R^N$, cells $u$ with porous-medium diffusion and logistic growth respond to a chemical $v$ that they produce linearly:
$$u_t = \Delta u^m - \chi\,\nabla\cdot(u\nabla v) + u(a - bu), \qquad \tau v_t = \Delta v - \lambda v + \mu u,$$
with $m>1$, $a,b,\lambda,\mu>0$, $\chi \in \mathbb R$ (attraction or repulsion), $\tau \in \{0,1\}$ (parabolic–elliptic or fully parabolic), and non-negative initial data $u_0 \in L^\infty(\mathbb R^N)$, $\tau v_0 \in W^{1,\infty}(\mathbb R^N)$ that need not be integrable.

**Theorem (global existence).** For every $T>0$ there is at least one non-negative global weak solution with $u \in L^\infty$ locally in space–time.

**Theorem (global boundedness).** Suppose $b > b_m$, where for $\tau = 0$
$$b_m = \frac{\mu|\chi|\big((2-m)N - 2\big)_+}{(2-m)N} \ \ \text{if } 1 < m \le 2 - \tfrac2N, \qquad b_m = 0 \ \ \text{if } m > 2 - \tfrac2N,$$
and for $\tau = 1$, $b_m = 0$ when $m > \frac{2N}{N+2}$ and $b_m$ is an explicit multiple of $|\chi|\mu$ (involving Gagliardo–Nirenberg-type constants) when $1 < m \le \frac{2N}{N+2}$. Then the system has a globally bounded non-negative weak solution, with
$$\|u\|_{L^\infty(\mathbb R^N\times(0,T))} + \|v\|_{W^{1,\infty}(\mathbb R^N\times(0,T))} \le C$$
for a constant $C$ independent of $T$, local bounds $u(t) \in L^p_{\rm loc}$ and $\nabla u^{(p+m)/2} \in L^2_{\rm loc}$ for every $p \ge m$, and $u \in C((0,T);L^2_{\rm loc})$. In particular, strong enough diffusion ($m > 2 - \tfrac2N$, resp. $m > \tfrac{2N}{N+2}$) prevents blow-up for any logistic strength $b>0$.

**Theorem (regularity and uniqueness).** Globally bounded non-negative weak solutions satisfying a mild time-continuity of $u^m$ are locally Hölder continuous, and are unique under the additional hypotheses stated in the paper.

## Expansion

Weak solutions are obtained as limits of classical solutions of a non-degenerate approximation (diffusion $\nabla\cdot((u+\varepsilon)^{m-1}\nabla u)$-type) with uniform local $L^p$ estimates. Since the data are not integrable, the estimates are localized with cut-off functions on balls, and the logistic term $-bu^2$ compensates the chemotactic production term $\chi\mu u^2$ in the $L^p$ energy inequality whenever $b > b_m$.

## Sources

- Zulaihat Hassan, "Global existence of weak solutions to chemotaxis models with porous medium diffusion, linear production, and logistic source on $\mathbb{R}^N$", arXiv:2608.18416 (2026), Theorem 1.1 (global existence), Theorem 1.2 (global existence and boundedness), Theorem 1.3 (Hölder regularity and uniqueness), Proposition 3.1, <https://doi.org/10.48550/arXiv.2608.18416>.
