# Unique equilibrium and feasibility in large random Lotka–Volterra communities

**Model.** $N$ species with abundances $x_i \ge 0$ follow

$$\frac{dx_i}{dt} = x_i\big(r_i - x_i + (\Gamma \boldsymbol x)_i\big), \qquad i = 1, \dots, N,$$

with random interaction matrix $\Gamma$ in one of two models: (i.i.d.) $\Gamma_{ij} = A_{ij}/(\alpha_N\sqrt N)$ with i.i.d. centered unit-variance $A_{ij}$ whose law does not depend on $N$; (elliptic) $\Gamma_{ij} = A_{ij}/(\alpha_N\sqrt N) + \mu/N$, where the pairs $(A_{ij}, A_{ji})$ are i.i.d. with correlation $\xi \in [-1, 1]$. An equilibrium $\boldsymbol x^*$ is *uninvadable* if no absent species can grow, which is exactly the linear complementarity problem $\boldsymbol x^* \in \mathrm{LCP}(I - \Gamma, -\boldsymbol r)$:

$$x^*_i \ge 0, \qquad r_i - x^*_i + (\Gamma\boldsymbol x^*)_i \le 0, \qquad x^*_i\big(r_i - x^*_i + (\Gamma\boldsymbol x^*)_i\big) = 0 \quad \forall i.$$

**Background (Takeuchi–Adachi).** If there is a positive diagonal $\Delta$ with $\Delta(I - \Gamma) + (I - \Gamma)^{\mathsf T}\Delta$ positive definite, the LCP has a unique solution $\boldsymbol x^*$ and every trajectory started in $(0,\infty)^N$ converges to it.

**Theorem.**

1. *(Unique globally stable equilibrium.)* Let $\alpha_N = \alpha$ be fixed. If $\Gamma$ is i.i.d. with $\alpha > \sqrt2$, or elliptic with

    $$\alpha > \sqrt{2(1 + \xi)} \quad\text{and}\quad \mu < \tfrac12 + \tfrac12\sqrt{1 - \tfrac{2(1+\xi)}{\alpha^2}},$$

    then almost surely, for all large $N$, the LCP has a unique solution $\boldsymbol x^* \ge 0$, and it is globally stable: $\boldsymbol x(t) \to \boldsymbol x^*$ for every $\boldsymbol x(0) \in (0, \infty)^N$.

2. *(Feasibility threshold.)* Let $\boldsymbol r = \mathbf 1$, $\alpha_N \to \infty$, $\alpha^*_N = \sqrt{2\log N}$, and in the elliptic case $\mu < 1$; let $\boldsymbol x^* = (I - \Gamma)^{-1}\mathbf 1$. If $\alpha_N \le (1-\varepsilon)\alpha^*_N$ for some $\varepsilon > 0$ then $\mathbb{P}(\min_i x^*_i > 0) \to 0$; if $\alpha_N \ge (1+\varepsilon)\alpha^*_N$ then $\mathbb{P}(\min_i x^*_i > 0) \to 1$.

So with interaction strength of order $1/\sqrt N$ the community has a unique stable equilibrium in which some species go extinct, and full coexistence of all $N$ species requires the interactions to be weaker by a factor $\sqrt{2\log N}$.

## Expansion

For $\alpha > \sqrt2$ the symmetric part of $I - \Gamma$ has smallest eigenvalue $1 - \sqrt2/\alpha > 0$ asymptotically, because the symmetrized i.i.d. matrix is a Wigner matrix with spectral edge $\sqrt2/\alpha$; the Takeuchi–Adachi criterion with $\Delta = I$ then applies, and in the elliptic case the edge moves to $\sqrt{2(1+\xi)}/\alpha$ while the rank-one mean shift $\mu$ must stay below the corresponding outlier threshold. For feasibility, $x^*_i \approx 1 + (\Gamma \mathbf 1)_i$ to first order, and the $N$ nearly Gaussian fluctuations of size $1/\alpha_N$ have minimum near $-\sqrt{2\log N}/\alpha_N$, so all abundances are positive exactly when $\alpha_N$ beats the Gaussian extreme-value scale.

## Sources

- Imane Akjouj, Matthieu Barbier, Maxime Clenet, Walid Hachem, Mylène Maïda, François Massol, Jamal Najim and Viet Chi Tran, "Complex systems in ecology: a guided tour with large Lotka–Volterra models and random matrices", Proceedings of the Royal Society A: Mathematical, Physical and Engineering Sciences 480 (2024), 20230284, <https://doi.org/10.1098/rspa.2023.0284>; numbering as in arXiv:2212.06136: Section 2.2 (random interaction models), Section 3 (Takeuchi–Adachi theorem, uniqueness theorem under the uninvadability condition, feasibility theorem).
