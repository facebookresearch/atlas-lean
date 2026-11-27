# Culled frequency process of a two-type branching population with competition and its large-population limit

**Model.** Let $X = (X^{(1)}, X^{(2)})$ be a two-type continuous-state branching process with immigration and competition (in the sense of Ma): type-$i$ mass has immigration rate $\eta_i \ge 0$, a deterministic interaction drift in which $b_{ij}(x)$ is the contribution of type-$j$ mass $x$ to the growth of type $i$, Gaussian branching coefficients $c_i \ge 0$, reproduction jumps driven by Borel measures $\mu_i$ on $U_2 = [0,\infty)^2 \setminus \{0\}$ (a type-$i$ parent producing masses $w = (w_1, w_2)$ of both types), and immigration jumps driven by a Borel measure $\nu$ on $U_2$. Throughout, each $b_{ij} : \mathbb{R} \to \mathbb{R}$ is locally Lipschitz with $b_{ij}(x) = 0$ for $x \le 0$ and $b_{ij}(x) \ge 0$ for $i \ne j$ (so competition acts only through $b_{ii}$, and cross-type effects are nonnegative), and, with $\|w\| = (w_1^2 + w_2^2)^{1/2}$,

$$\int_{U_2} (1 \wedge \|w\|)\,\nu(dw) < \infty, \qquad \int_{U_2} \big(\|w\| \wedge \|w\|^2 + w_j\big)\,\mu_i(dw) < \infty \quad (i \ne j).$$

Let $Z = X^{(1)} + X^{(2)}$ and $R = X^{(1)}/Z$. The pair $(R, Z)$ is Markov, but $R$ alone is not.

**Culling.** Fix a total mass $z > 0$. Run $(R, Z)$ on short time intervals of length $1/n$ and after each interval rescale the population back to total mass $z$ while keeping the frequency $R$ (culling). The resulting frequency processes $\bar R^{(z,n)}$ live on $[0,1]$.

**Theorem.**

1. *Culled frequency process.* For fixed $z > 0$ there is a unique strong $[0,1]$-valued solution $R^{(z,r)}$ of the frequency SDE obtained from the generator of $(R,Z)$ by freezing $Z = z$ (drift from immigration, interaction and selection terms, diffusion coefficient $\sigma(r)^2 = \frac{2r(1-r)}{z}\big[(1-r)c_1 + r c_2\big]$, and jumps $r \mapsto r + (1-r)u_1 - ru_2$ from reproduction events). It is Feller and $L^1$-Lipschitz in its initial condition, and $\bar R^{(z,n)} \Rightarrow R^{(z,r)}$ in $D([0,T],[0,1])$ as $n \to \infty$ whenever $\bar R^{(z,n)}_0 \Rightarrow r$.
2. *Moment duality.* Under a polynomial assumption on the coefficients and nonnegativity of the off-diagonal rates, $\mathbb{E}_r\big[(R^{(z,r)}_t)^n\big] = \mathbb{E}_n\big[r^{N_t}\big]$ for a branching–coalescing block-counting chain $N$ on $\mathbb{N}_0 \cup \{\dagger\}$.
3. *Large-population limit.* Suppose $\beta_{ij}(r) = \lim_{z\to\infty} b^{(z)}_{ij}(rz)/z$ exists uniformly on $[0,1]$ and is Lipschitz. Then for every $T > 0$, $\lim_{z\to\infty}\mathbb{E}\big[\sup_{t\le T}|R^{(z,r)}_t - R^{(\infty,r)}_t|^2\big] = 0$, where $R^{(\infty,r)}$ solves

    $$\dot R = \beta_{11}(R)(1-R) - \beta_{22}(1-R)R + \beta_{12}(1-R)(1-R) - \beta_{21}(R)R + (1-R)^2\!\int_{U_2} w_1\,\mu_2(dw) - R^2\!\int_{U_2} w_2\,\mu_1(dw),$$

    with $R_0 = r$.

## Expansion

Itô's formula for $R = X^{(1)}/Z$ gives a generator in which every frequency term carries a factor $1/z$ from the current total mass; culling keeps $Z \equiv z$ so the frequency becomes autonomous, generalising the $\Lambda$-asymmetric frequency process. Under polynomial coefficients the generator maps monomials $r^n$ to combinations of $r^m$, which is the condition for a moment dual: neutral reproduction appears as coalescence of blocks, selection and cross-type production as branching, and immigration or killing as absorption. As $z \to \infty$ the diffusion and jump terms vanish at rate $1/z$, except for jumps that produce mass of the other type, whose mean contributes the last two drift terms, leaving the deterministic ODE.

## Sources

- Imanol Nuñez and José Luis Pérez, "The Frequency Process in a Non-neutral Two-Type Continuous-State Branching Process with Competition and Its Genealogy", in *XIV Symposium on Probability and Stochastic Processes*, Progress in Probability, Springer (2025), 241–275, <https://doi.org/10.1007/978-3-031-96118-2_11>. Numbering as in the preprint arXiv:2406.04255v1, <https://arxiv.org/abs/2406.04255v1>: Section 3 (Propositions 3.1–3.3 and Theorem 3.1: culled frequency process, existence, Feller property and culling convergence), Section 4 (Theorem 4.1, moment duality) and Section 5 (Theorem 5.1, large population limit).
