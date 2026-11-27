# Persistence and extinction in the almost periodic Tilman metapopulation model with habitat destruction

**Model.** In the Tilman–Nee–May generalization of the Levins metapopulation model, a fraction $h \in (0,1]$ of patches is habitable (the rest destroyed), species are ranked by competitive ability, and a superior competitor can colonize patches held by inferior ones. For two species with fractions $p_1$ (superior) and $p_2$ of occupied patches,

$$p_1' = p_1\big\{c_1(t)(h - p_1) - m_1(t)\big\}, \qquad p_2' = p_2\big\{c_2(t)(h - p_1 - p_2) - m_2(t) - c_1(t)p_1\big\},$$

with $0 < p_1(t_0) + p_2(t_0) < h$, where colonization rates $c_i$ and extinction rates $m_i$ are positive almost periodic functions with means $\mathcal{M}[\cdot]$, and the colonization rates are bounded away from zero, $\inf_{t\in\mathbb{R}} c_i(t) = c_i^- > 0$ (assumption (1.8) of the source). Define

$$\mathcal{R}_0 = \frac{\mathcal{M}[m_1]}{\mathcal{M}[c_1]},\qquad \mathcal{R}_1 = \frac{\mathcal{M}[m_2]}{\mathcal{M}[c_2]},\qquad \mathcal{R}^*_{1,1} = \mathcal{R}_1 + \ell_{1,1},\quad \ell_{1,1} = \frac{\mathcal{M}[(c_1+c_2)p^*_{1,1}]}{\mathcal{M}[c_2]},$$

where, when $\mathcal{R}_0 < h$,

$$p^*_{1,1}(t) = \Big(\int_{-\infty}^t c_1(s)\,e^{\int_s^t a_{11}(r)\,dr}\,ds\Big)^{-1},\qquad a_{11}(t) = -[c_1(t)h - m_1(t)],$$

is the unique positive almost periodic solution of the first equation. The interval $(\mathcal{R}_1, \mathcal{R}^*_{1,1})$ is the *exclusion interval* (niche shadow) cast by the superior competitor.

**Theorem (one species).** If $\mathcal{R}_0 < h$, then $p_1$ is strongly persistent and $|p_1(t) - p^*_{1,1}(t)| \to 0$ exponentially fast; if $\mathcal{R}_0 > h$ the species goes extinct exponentially fast.

**Theorem (two species, $\mathcal{M}[c_1] < \mathcal{M}[c_2]$).** Every positive solution converges exponentially to one of four almost periodic regimes:

1. (Coexistence.) If $\max\{\mathcal{R}_0, \mathcal{R}^*_{1,1}\} < h$, there is a unique positive almost periodic solution $(p^*_{1,1}, p^*_{2,1})$, globally exponentially attractive.
2. (Best competitor persists.) If $\mathcal{R}_0 < h < \mathcal{R}^*_{1,1}$, solutions converge to $(p^*_{1,1}, 0)$.
3. (Fugitive species persists.) If $\mathcal{R}_1 < h < \mathcal{R}_0$, solutions converge to $(0, p^*_{2,3})$, the almost periodic Levins equilibrium of species $2$ alone.
4. (Global extinction.) If $h < \min\{\mathcal{R}_0, \mathcal{R}_1\}$, both species go extinct exponentially fast.

The analysis extends recursively to $n$ species, each superior species casting a niche shadow on the next.

## Expansion

Each equation is a logistic (Bernoulli) equation whose substitution $u = 1/p$ gives a linear almost periodic equation $u' = a(t)u + c(t)$. A scalar linear almost periodic equation $x' = a(t)x$ has an exponential dichotomy iff its mean $\mathcal{M}[a] \ne 0$, contracting if $\mathcal{M}[a] < 0$ and expanding if $\mathcal{M}[a] > 0$; thus colonization dominates extinction exactly when $\mathcal{M}[c_1]h - \mathcal{M}[m_1] > 0$, i.e. $\mathcal{R}_0 < h$, and then the inhomogeneous equation has a unique bounded, exponentially attracting almost periodic solution. For the inferior species, the occupied fraction $p^*_{1,1}$ of the superior competitor enters as an almost periodic perturbation of its growth coefficient, whose mean shifts the threshold from $\mathcal{R}_1$ to $\mathcal{R}^*_{1,1}$; roughness of exponential dichotomies handles the transient approach.

## Sources

- Pablo Amster, Gonzalo Robledo and Daniel Sepúlveda, "Dynamics in an almost periodic metapopulation with competition and habitat destruction: An exponential dichotomy based approach", Mathematical Biosciences 398 (2026), 109723, <https://doi.org/10.1016/j.mbs.2026.109723>; numbering as in arXiv:2412.02952: Propositions 2.1–2.5 and Corollary 2.1 (Section 2), Theorem 3.1 (Section 3), Theorems 4.1–4.4 (Section 4).
