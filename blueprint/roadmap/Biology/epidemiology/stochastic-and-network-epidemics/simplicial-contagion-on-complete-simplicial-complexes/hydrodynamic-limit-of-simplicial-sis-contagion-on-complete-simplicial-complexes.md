# Hydrodynamic limit of simplicial SIS contagion on complete simplicial complexes

**Model.** On $N$ nodes forming a complete simplicial complex of order $M$ (every set of $i+1 \le M+1$ nodes is an $i$-simplex), each node is susceptible or infected. Infected nodes recover at rate $\gamma$. A susceptible node in an $(i+1)$-node simplex whose other $i$ nodes are all infected receives infection pressure $r_i = s_i N^{-i}$ from that simplex ($s_i \ge 0$; $s_1 = \lambda$ is the pairwise rate, $s_2 = \mu$ the triangle rate, $s_3 = \theta$ the tetrahedron rate). Let $m^N(t)$ be the number of infected nodes.

**Theorem (hydrodynamic limit).** Fix $T > 0$. Assume $m^N(t)/N$ converges uniformly on $[0,T]$ to a deterministic $m_I(t)$ and the martingale remainder $\eta^N_t$ in the semimartingale decomposition of $m^N$ satisfies $\sup_{t\le T}\mathbb E[\eta^N_t] \to 0$. Then

$$\frac{dm_I}{dt} = (s_1 - \gamma)m_I + \sum_{i=1}^{M-1}\Big(\frac{s_{i+1}}{(i+1)!} - \frac{s_i}{i!}\Big)m_I^{i+1} - \frac{s_M}{M!}m_I^{M+1} = (1 - m_I)\sum_{i=1}^M \frac{s_i}{i!}m_I^i - \gamma m_I .$$

For $M = 2$ this is $\dot m_I = (\lambda - \gamma)m_I + (\tfrac{\mu}{2} - \lambda)m_I^2 - \tfrac{\mu}{2}m_I^3$, and for $M = 3$ it adds $(\tfrac{\theta}{6} - \tfrac{\mu}{2})m_I^3 - \tfrac{\theta}{6}m_I^4$.

**Bifurcations for $M = 2$.** Besides $m_I = 0$, steady states solve $0 = (\lambda - \gamma) + (\tfrac{\mu}{2} - \lambda)x - \tfrac{\mu}{2}x^2$. In the $(\lambda,\mu)$ quadrant, with discriminant curve $\lambda = -\mu/2 + \sqrt{2\mu\gamma}$:
- below the curve there is no endemic state;
- above it with $\lambda > \gamma$ there is exactly one positive state (supercritical regime);
- above it with $\lambda < \gamma$ and $\mu > 2\lambda$ there are two positive states, the larger stable and the smaller unstable, so the epidemic-free and endemic states are **bistable**.

**Bifurcations for $M = 3$.** The branch of the discriminant curve with positive steady states has a cusp point if $\theta > 6\gamma$ and is a convex arc if $\theta < 6\gamma$, so adding 3-simplices can create a region with three positive equilibria (multistability).

## Proof sketch

On the complete complex the state is exchangeable, so the number of infected nodes is a birth–death chain: with $k$ infected, a susceptible node lies in $\binom{k}{i}$ fully infected $(i+1)$-simplices, and $r_i\binom{k}{i} \to s_i m^i/i!$ under the scaling $r_i = s_iN^{-i}$. Summing over the $N - k$ susceptibles and dividing by $N$ gives the drift of the limiting equation, and Kurtz-type martingale estimates make the convergence rigorous. Bistability therefore needs no community or clustering structure: it is already present in the exact dynamics of the fully mixed higher-order model.

## Sources

- István Z. Kiss, Iacopo Iacopini, Péter L. Simon and Nicos Georgiou, "Insights from exact social contagion dynamics on networks with higher-order structures", *Journal of Complex Networks* 11 (2023), cnad044, <https://doi.org/10.1093/comnet/cnad044>. Preprint version: arXiv:2309.12752 (2023), Theorems 2.1–2.3 (Section 2) and Propositions 3.1–3.2 (Section 3), <https://doi.org/10.48550/arXiv.2309.12752>.
