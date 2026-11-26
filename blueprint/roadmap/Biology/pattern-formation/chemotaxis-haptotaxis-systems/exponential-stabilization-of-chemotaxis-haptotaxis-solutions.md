# Exponential stabilization of chemotaxis–haptotaxis solutions

Consider the [chemo-repulsion–haptotaxis system](global-boundedness-in-a-chemo-repulsion-haptotaxis-system.md) on a bounded smooth $\Omega\subset\mathbb{R}^n$, $n\ge2$, with $\bar u_0=\frac{1}{|\Omega|}\int_\Omega u_0$ and $\lambda_1$ the first positive Neumann eigenvalue of $-\Delta$.

**Theorem (bounded solutions stabilize).** For any globally bounded classical solution, the matrix component decays: for every $\gamma\in(0,v_*)$, where $v_*>0$ is an eventual uniform positive lower bound for $v$, there is $C$ with $\|w(t)\|_{W^{1,\infty}}\le Ce^{-\gamma t}$; and for $p>n$ there are $C,\delta>0$ with
$$\|u(t)-\bar u_0\|_{L^\infty}+\|v(t)-\bar u_0\|_{W^{1,\infty}}\le Ce^{-\min\{\delta/(2p),\,1\}t}.$$

**Theorem (small data, any sign of $\chi,\xi$).** Let $\chi,\xi\in\mathbb{R}$ and $\theta\le1$. There is $\eta_0>0$ such that if
$$\|u_0\|_{L^{n/2}}<\eta_0,\qquad \tau\|\nabla v_0\|_{L^n}<\eta_0,\qquad \|\nabla w_0\|_{L^\infty}<\eta_0,$$
then the classical solution is global, bounded, and for any $0<\mu<\min\{\lambda_1,\bar u_0\}$,
$$\|u(t)-\bar u_0\|_{L^\infty}+\|v(t)-\bar u_0\|_{W^{1,\infty}}+\|w(t)\|_{W^{1,\infty}}\le Ce^{-\min\{\mu,1\}t}.$$

**Theorem (3D weak solutions).** For $n=3$, $\tau=1$, $\chi,\xi\ge0$ and $\theta<\tfrac76$ there is a global weak solution with $u\in L^{5/3}(\Omega\times(0,T))$. If moreover $\theta\le\tfrac12$, $S'$ is bounded and $\inf_\Omega v_0>0$, the weak solution becomes Hölder regular and bounded after some $t_0$ and converges exponentially to $(\bar u_0,\bar u_0,0)$.

The smallness thresholds are in the scaling-invariant norms $L^{n/2}$ for $u$ and $L^n$ for $\nabla v$, which allows attractive chemotaxis ($\chi<0$) in this regime.

## Depends on

- [Global boundedness in a chemo-repulsion–haptotaxis system](global-boundedness-in-a-chemo-repulsion-haptotaxis-system.md)

## Expansion

Mass $\int u$ is conserved, so $\bar u_0$ is the only candidate limit for $u$; once $u$ is bounded, the $v$-equation yields a positive lower bound $v_*$ after a finite time, and $w_t=-vw$ gives $w\le\|w_0\|_\infty e^{-v_*t}$. The gradient $\nabla w$ is then controlled through $\nabla w=e^{-\int v}(\nabla w_0-w_0\int\nabla v)$. With the haptotactic forcing decaying exponentially, the linearized Neumann heat semigroup with spectral gap $\lambda_1$ drives $(u,v)$ to $(\bar u_0,\bar u_0)$. For small data, a continuation argument in the scaling-critical norms closes using $L^p$–$L^q$ estimates of the Neumann heat semigroup.

## Sources

- Y. Chen, T. Xiang, "Global solvability, regularity and exponential convergence in a quasilinear chemotaxis-haptotaxis system with mostly repulsive signal production", arXiv:2611.22930 (2026), Theorem 1.1 (B3), Theorem 1.3, Definition 6.1 and Theorem 1.5, Sections 4–6, <https://doi.org/10.48550/arXiv.2611.22930>.
