# Global boundedness under weakly singular sensitivity and nonlocal logistic damping

**Model.** Let $\Omega \subset \mathbb{R}^N$ ($N \ge 1$) be a smooth bounded domain, $\chi, r, \mu, \gamma > 0$, $k \in (0,1)$ and $\alpha, \beta \ge 1$. Population density $u$ and signal $v$ satisfy, with homogeneous Neumann conditions,
$$u_t = \Delta u - \chi\nabla\cdot\Big(\frac{u}{v^k}\nabla v\Big) + u^\alpha\Big(r - \mu\int_\Omega u^\beta\Big), \qquad 0 = \Delta v - v + u^\gamma,$$
with $u_0 \in C^0(\overline\Omega)$, $u_0 \ge 0$, $m_0 = \int_\Omega u_0 > 0$.

**Hypothesis $\mathcal{H}$.** One of the following holds:
- $(H_1)$ $\beta > 1$ and $\gamma = 1$, with $1 \le \alpha < 1 + 2\beta$ if $N = 1$, and, if $N \ge 2$, either $1 \le \alpha < 2$ and $\alpha + \beta > 2 + N/2$, or $2 \le \alpha < 1 + 2\beta/N$;
- $(H_2)$ $\beta = 1$, with $\gamma = 1$ if $N = 1$ and $0 < \gamma < 2/N$ if $N \ge 2$; moreover $1 \le \alpha < 1 + 2/N$ if $m_0 < r/\mu$, while any $\alpha \ge 1$ is allowed if $m_0 \ge r/\mu$.

**Theorem.** Under $\mathcal{H}$, for every $p \ge 2$ there is $C_p$ independent of $t$ with $\sup_{0<t<T_{\max}}\int_\Omega u^p \le C_p$. Consequently the classical solution exists globally and is uniformly bounded: $\|u(\cdot,t)\|_{L^\infty(\Omega)} \le C_\infty$ for all $t > 0$.

## Expansion

For $\beta > 1$ the higher-order growth terms are absorbed by the nonlocal dissipation $-\mu u^\alpha\int u^\beta$; for $\beta = 1$ the total mass obeys $\frac{d}{dt}\int u = (r - \mu\int u)\int u^\alpha$, so it stays below $\max\{m_0, r/\mu\}$, and above $r/\mu$ it is nonincreasing, which is why larger $\alpha$ is allowed when $m_0 \ge r/\mu$. Energy and interpolation estimates then bound $\int u^p$. Unlike the usual approach, the $L^\infty$ bound is obtained by elliptic regularity and Moser iteration before any positive lower bound for $v$; that bound then yields time-uniform lower bounds for $\int u$ and $v$, which control the singular sensitivity $v^{-k}$ in the extensibility criterion.

## Sources

- Y. Cao, Q. Li and J. Zhang, "Global boundedness of the chemotaxis system with weakly singular sensitivity and nonlocal term in any dimension", arXiv:2609.14443 (2026), Theorems 1.1 and 1.2 under hypothesis $\mathcal{H}$, proved in Sections 3 and 4, <https://doi.org/10.48550/arXiv.2609.14443>.
