# Steady-state correspondence between sigmoidal ODEs and multistate networks

**Setting.** A continuous model is an ODE $\bar x'=D(\bar f(\bar x)-\bar x)$ with $D$ a positive diagonal matrix and $\bar f:[0,1]^N\to[0,1]^N$ continuous; a multistate (multivalued, finite dynamical) network is a map $f:\mathcal{S}\to\mathcal{S}$, $\mathcal{S}=\prod_{j=1}^N\{0,1,\dots,m_j\}$, iterated as $x(t+1)=f(x(t))$. For each $j$ fix thresholds $0<k^j_1<\dots<k^j_{m_j}<1$ and associate to the level $\ell$ the interval $[\ell]=]k^j_\ell,k^j_{\ell+1}[$ (with $[0]=[0,k^j_1[$ and $[m_j]=]k^j_{m_j},1]$); for $x\in\mathcal{S}$ the **region** is $[x]=[x_1]\times\dots\times[x_N]\subseteq[0,1]^N$.

**Theorem (Veliz-Cuba et al., Theorem 3.4).** Let $(\bar f^n)$ be a family of continuous maps $[0,1]^N\to[0,1]^N$ (e.g. Hill-type functions with Hill exponents $n\to\infty$) and $f$ a multistate network. Consider

1. $\bar f^n\to L_x$ uniformly on compact subsets of $[x]$, for some point $L_x\in[f(x)]$, for every $x\in\mathcal{S}$;
2. the Jacobians $(\bar f^n)'\to 0$ uniformly on compact subsets of $[x]$, for every $x\in\mathcal{S}$.

For each $x\in\mathcal{S}$ choose a convex compact $K_x\subseteq[x]$ such that $L_x$ is an interior point of $K_{f(x)}$, and set $K=\bigcup_x K_x$. If (1) holds then, for $n$ large enough, the ODE $\bar x'=D(\bar f^n(\bar x)-\bar x)$ has a steady state in $K_x$ if and only if $x$ is a fixed point of $f$; this gives a one-to-one correspondence between steady states of the ODE in $K$ and steady states of $f$, and the ODE steady state $\bar x^n\in K_x$ satisfies $\bar x^n\to L_x$. If (2) also holds, each such ODE steady state is unique in $K_x$ and asymptotically stable.

**Corollary 3.6.** Under (1), for every $\epsilon>0$ the set $K$ can be chosen with Lebesgue measure $\mu([0,1]^N\setminus K)\le\epsilon$; ODE steady states outside $K$ can only lie near the threshold hyperplanes.

The theorem contains as special cases the known correspondences for piecewise-linear (Glass-type) ODEs and for Boolean networks with Hill functions.

## Proof sketch

The proof combines three lemmas (Lemmas 3.1–3.3): Brouwer's fixed point theorem gives a steady state in any convex compact $K$ with $\bar f(K)\subseteq K$; a contraction bound $\|\bar f'\|\le\epsilon<1$ on convex $K$ gives at most one; and $\|\bar f'\|<\min_i D_{ii}/(\sqrt N\|D\|)$ forces all Jacobian eigenvalues of $D(\bar f'-I)$ into the open left half-plane (Gershgorin). Uniform convergence gives $\bar f^n(K_x)\subseteq K_{f(x)}$ for large $n$; when $f(x)=x$ the box $K_x$ is invariant, and when $f(x)\ne x$ the image lies in a disjoint region so no fixed point can sit in $K_x$. The practical message is that steady states of sufficiently sigmoidal regulatory ODEs are dictated by the regulatory logic, not by precise kinetic parameters; in examples the correspondence already holds for Hill exponent $2$.

## Sources

- Alan Veliz-Cuba, Joseph Arthur, Laura Hochstetler, Victoria Klomps and Erikka Korpi, "On the Relationship of Steady States of Continuous and Discrete Models Arising from Biology", *Bulletin of Mathematical Biology* 74 (2012), 2779–2792, <https://doi.org/10.1007/s11538-012-9778-1>. Preprint version: arXiv:1109.5197 (2011), <https://doi.org/10.48550/arXiv.1109.5197>.
