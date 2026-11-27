# Competitive exclusion in the infection-age-structured multi-strain virus model

Consider $n$ virus strains competing within a host for target cells. Let $T(t)$ be the uninfected target-cell concentration, $V_i(t)$ the free virus of strain $i$, and $T_i^*(t,a)$ the density of cells infected by strain $i$ with age since infection $a$:

$$\frac{dT}{dt} = f(T) - \sum_{i=1}^n k_i V_i T, \qquad \frac{dV_i}{dt} = \int_0^\infty p_i(a)\,T_i^*(t,a)\,da - \gamma_i V_i,$$

$$\partial_t T_i^* + \partial_a T_i^* = -\delta_i(a)\,T_i^*, \qquad T_i^*(t,0) = k_i V_i(t)\,T(t).$$

Assume $f$ is smooth with $f(T) > 0$ on $[0,\overline T_0)$ and $f(T) < 0$ for $T > \overline T_0$ (e.g. $f(T) = s - cT$ or $s - cT + rT(1 - T/T_{\max})$), $p_i, \delta_i \in L^\infty_+$, $p_i \le \kappa$ and $\delta_i \ge b > 0$ a.e. The state space is $X = \mathbb R_+^{n+1} \times (L^1_+(0,\infty))^n$. With survival $\phi_i(a) = \exp(-\int_0^a \delta_i)$ and burst size $N_i = \int_0^\infty p_i\phi_i\,da$, the **strain reproduction number** is

$$\mathcal R_i = \frac{N_i k_i \overline T_0}{\gamma_i}.$$

When $\mathcal R_i > 1$ there is a single-strain equilibrium $E_i$ with $\overline T_i = \overline T_0/\mathcal R_i$, $\overline V_i = f(\overline T_i)/(k_i \overline T_i)$ and $\overline T_i^*(a) = k_i\overline V_i\overline T_i\phi_i(a)$; if all $\mathcal R_i$ are distinct there is no coexistence equilibrium.

**Proposition (extinction).** If $\mathcal R_i < 1$, then $V_i(t) \to 0$ and $\int_0^\infty T_i^*(t,a)\,da \to 0$.

**Theorem (competitive exclusion).** Suppose $\mathcal R_1 > \mathcal R_2 > \dots > \mathcal R_n > 1$ and $f$ satisfies the sector condition

$$\big(f(T) - f(\overline T_i)\big)\Big(1 - \frac{\overline T_i}{T}\Big) \le 0 \quad \text{for all } T > 0,\ i = 1,\dots,n$$

(automatic when $f$ is decreasing). Then $E_1$, the equilibrium of the strain with maximal reproduction number, is globally asymptotically stable for all initial data with $V_1(0) + \int_0^\infty T_1^*(0,a)\,da > 0$.

So the strain that drives target cells lowest, $\overline T_1 = \overline T_0/\mathcal R_1$, excludes all others regardless of the shape of the age-dependent production and death profiles.

## Expansion

The solution semiflow is a $C^0$ semigroup on $X$ that is point dissipative and asymptotically smooth (a compactness argument in $L^1$), so it has a compact global attractor. Strong induction on the number of strains characterizes the boundary flow: on each face where strain $1$ is absent the dynamics reduce to fewer strains and converge to the corresponding $E_j$. Hale–Waltman persistence theory then gives uniform persistence of strain $1$ and an interior attractor. On complete orbits in that attractor, the Volterra-type functional

$$W = \frac{\overline T_1}{\overline u_1} g\Big(\frac{T}{\overline T_1}\Big) + \frac{k_1 \overline T_1 \overline V_1}{\gamma_1 \overline u_1} g\Big(\frac{V_1}{\overline V_1}\Big) + \frac{k_1\overline T_1}{\gamma_1}\int_0^\infty \alpha_1(a)\,g\Big(\frac{u_1(a)}{\overline u_1}\Big)da + \frac{1}{\overline u_1}\sum_{i\ge2}\frac{\int_0^\infty \alpha_i u_i\,da + V_i}{\alpha_i(0)},$$

with $g(x) = x - 1 - \ln x$, $u_i = T_i^*/\phi_i$, $\overline u_1 = k_1\overline V_1\overline T_1$ and $\alpha_i(a) = \int_a^\infty \phi_i p_i$, is non-increasing; a LaSalle argument forces the orbit to be $E_1$.

## Sources

- Cameron J. Browne, "A Multi-Strain Virus Model with Infected Cell Age Structure: Application to HIV", arXiv (2013). Section 2 (model (1)–(4)), Section 3 (Propositions 3.2, 3.3, 3.6), Section 4.1 (equation (5), equilibria), Proposition 4.1, Section 5 (conditions (8)–(10), functional (15), Proposition 5.1, Theorem 5.3). <https://doi.org/10.48550/arXiv.1309.0237>. Published version: Nonlinear Analysis: Real World Applications 22 (2015), 354–372, <https://doi.org/10.1016/j.nonrwa.2014.10.004>; locators above refer to the arXiv version.
