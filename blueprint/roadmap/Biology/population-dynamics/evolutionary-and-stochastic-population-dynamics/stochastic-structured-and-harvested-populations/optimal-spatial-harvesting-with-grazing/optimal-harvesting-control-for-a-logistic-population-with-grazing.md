# Optimal spatial harvesting of a logistic population with grazing

**Model.** Let $\Omega \subset \mathbb{R}^N$ be a bounded domain with $C^2$ boundary and outward normal $\eta$. A population of density $u$ grows logistically with carrying capacity $K$, is grazed by a fixed number of grazers at the sigmoidal rate $c\,u^2/(1+u^2)$, and is harvested with spatial effort $h \in U = \{h \in L^2(\Omega) : 0 \le h \le H\}$:

$$-\Delta u = \lambda\Big[u - \frac{u^2}{K} - c\,\frac{u^2}{1+u^2} - h(x)\,u\Big] =: \lambda f_h(u) \ \text{ in } \Omega, \qquad \frac{\partial u}{\partial \eta} + q u = 0 \ \text{ on } \partial\Omega,$$

where $1/\lambda$ is the diffusion coefficient and $K, c, q > 0$. The Robin condition models a partly hostile boundary. The harvest profit is

$$J(h) = \int_\Omega h(x)\,u_h(x)\,dx - \int_\Omega \big(B_1 + B_2 h(x)\big)h(x)\,dx,$$

with $B_1 > 0$ the unit cost of effort at low effort and $B_2 > 0$ the rate at which cost rises with effort.

**Theorem.**

1. *(State equation.)* If $c < 2(1-H)$, there is $K^* > 0$ such that for $K > K^*$ and all sufficiently large $\lambda$ the boundary value problem has a unique positive solution $u_h$ for every $h \in U$; moreover, for any $\delta > 0$ and $\lambda$ large, $\frac{K(1-H)}{2} < u_H < u_0 < K$ on $\overline\Omega$.
2. *(Existence of an optimal control.)* For $K > K^*$ there exists $h^* \in U$ maximizing $J$.
3. *(Characterization.)* If $c < 2(1-H)$ and $K$, $\lambda$ are large, any optimal control satisfies

$$h(x) = \min\Big\{H,\ \max\Big\{0,\ \frac{u_h - p\,u_h - B_1}{2B_2}\Big\}\Big\},$$

where $p \in H^2(\Omega)$ solves the adjoint problem

$$-\Delta p - \lambda\Big(p - \frac{2u_h p}{K} - \frac{2c\,u_h}{(1+u_h^2)^2}\,p - h(x)\,p\Big) = h(x) \ \text{ in } \Omega, \qquad \frac{\partial p}{\partial\eta} + q p = 0 \ \text{ on } \partial\Omega.$$

4. *(Uniqueness.)* For $N \in \{2,3\}$ and $B_2$ large, the optimality system for $(h, p, u_h)$ with $u_h > 0$ has a unique solution.

## Expansion

For large $\lambda$ (small diffusion) the positive solution is close to the largest zero $r_0$ of $f_h$ away from a boundary layer; the condition $c < 2(1-H)$ with $K$ large guarantees that the grazing term creates no additional positive zeros that would destroy uniqueness, and sub- and supersolutions $u_H \le u_h \le u_0$ bracket the solution. Existence of a maximizer follows from weak compactness of $U$ and continuity of $h \mapsto u_h$. Differentiating $u_h$ in the direction $\gamma$ gives a sensitivity $\psi$ solving the linearized equation, and its solvability uses positivity of a principal eigenvalue, which replaces the monotonicity argument unavailable because the grazing term is not monotone. Pairing $\psi$ with the adjoint $p$ turns $\frac{d}{d\varepsilon}J(h+\varepsilon\gamma) \le 0$ into a pointwise projection formula, and an $L^\infty$ bound $\|p\|_\infty \le M'/B_2$ makes the optimality map a contraction when $B_2$ is large.

## Sources

- Mohan Mallick, Ardra A and Sarath Sasi, "Optimal harvesting for a logistic model with grazing", arXiv:2401.07264 (2024), Section 1 (Theorems 1.1–1.4), Section 2 (Propositions 2.1, 2.2 and 2.4, Lemma 2.5), Section 4 (Lemmas 4.1–4.3) and Section 5 (Lemma 5.1), <https://doi.org/10.48550/arXiv.2401.07264>. Published version: Evolution Equations and Control Theory 14 (2025) 511–529, <https://doi.org/10.3934/eect.2024066>.
