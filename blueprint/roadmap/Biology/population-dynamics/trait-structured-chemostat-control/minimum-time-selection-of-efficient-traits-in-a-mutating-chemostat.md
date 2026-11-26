# Minimum-time selection of efficient traits in a mutating chemostat

**Setting.** Consider the trait-structured chemostat $\partial_tf=(\mu(s,z)-u)f+\alpha\Delta_zf$, $\dot s=-\int_\Omega\mu(s,z)f\,dz+u(s_{in}-s)$ with Neumann boundary conditions on a bounded domain $\Omega\subset\mathbb{R}^d$, mutation rate $\alpha\ge0$, and Monod kinetics

$$
\mu(s,z)=\frac{\bar\mu\,s}{r(z)+s},
$$

where $r(z)>0$ is the half-saturation constant of trait $z$, $r_0=\min_{\bar\Omega}r$ and $r_1=\max_{\bar\Omega}r$. Admissible controls are measurable $u:\mathbb{R}_+\to[0,u_{max}]$. The mean half-saturation of a population is

$$
k[f]=\frac{\int_\Omega r(z)f(z)\,dz}{\int_\Omega f(z)\,dz}\in[r_0,r_1],
$$

and for $k_0\in(r_0,r_1)$ the target set is $\mathcal T_0=\{f\in L^1:\ k[f]\le k_0\}$. Initial data range over $\mathcal F=(0,s_{in}]\times\{f\in L^1(\Omega):\ f\ge\kappa\mathbf 1_{B_\eta(\bar x)\cap\Omega}\text{ for some }\kappa,\eta>0\}$ with $\bar x\in\arg\min_{\bar\Omega}r$ (positive mass near the most efficient trait). Put $\upsilon=\sup_{[0,s_{in}]\times\Omega}\mu$ and $\bar u=\max(\upsilon,4\upsilon s_{in})$.

**Reach-and-stay controllability.** Let $u_{max}\ge\bar u$ and $k_0\in(r_0,r_1)$. There is $\alpha_0>0$ such that for all $\alpha\in[0,\alpha_0)$ and all initial data in $\mathcal F$ some admissible control drives the solution into $\mathcal T_0$ in finite time and keeps it in $\mathcal T_0$ afterwards.

**Theorem (existence of a minimum-time control).** Under the same conditions, for every $(s_0,f_0)\in\mathcal F$ the problem

$$
\inf_{u}\ T_u\quad\text{subject to}\quad f(t,\cdot)\in\mathcal T_0\ \text{ for all } t\ge T_u
$$

admits an optimal control $u^*$, whose state reaches $\mathcal T_0$ at the minimal time $T^*$ and stays there.

## Depends on

- [Auxostat feedback stabilization of a trait-structured chemostat](auxostat-feedback-stabilization-of-a-trait-structured-chemostat.md)

## Expansion

Under an auxostat feedback that holds the substrate at a level $\sigma$, the trait profile converges to the principal eigenfunction $\varphi_{\sigma,\alpha}$ of $\alpha\Delta+\mu(\sigma,\cdot)$; as $\alpha\to0$ this eigenfunction concentrates on the traits maximizing $\mu(\sigma,\cdot)$, i.e. minimizing $r$, and $k[\varphi_{\sigma,\alpha}]\to r_0$. Hence for small mutation the stationary profile lies strictly inside $\mathcal T_0$, and a saturated version of the auxostat control (admissible because $u_{max}\ge\bar u$) reaches and then remains in the target. Existence of an optimal control follows from a compactness argument: minimizing sequences of controls converge weakly-star, the corresponding densities converge as Radon measures through an Aubin–Lions type lemma, and the reach-and-stay constraint passes to the limit.

## Sources

- Claudia Alvarez-Latuz, Térence Bayen, Jérôme Coville, *Target controllability for a minimum time problem in a trait-structured chemostat model*, arXiv (2026). Proposition 1.6 (reachability of the target), Theorem 1.7 (existence of an optimal control), Lemma 4.1 (small-mutation limit of the eigenfunction), Section 4. <https://doi.org/10.48550/arXiv.2602.21999>
