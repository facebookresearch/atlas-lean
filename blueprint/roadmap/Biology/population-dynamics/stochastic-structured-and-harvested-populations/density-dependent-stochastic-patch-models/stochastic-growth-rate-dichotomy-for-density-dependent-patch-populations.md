# Stochastic growth rate dichotomy for density-dependent patch populations

**Setting.** A population lives on $n$ patches with abundances $\mathbf{X}(t)=(X_1(t),\dots,X_n(t))\in[0,\infty)^n$ solving

$$dX_i=\Big(X_i\big(a_i-b_i(X_i)\big)+\sum_{j=1}^n D_{ji}X_j\Big)dt+X_i\,dE_i,\qquad i=1,\dots,n,$$

where $a_i\in\mathbb{R}$ are per-capita growth rates, $b_i$ are locally Lipschitz intraspecific competition functions with $b_i(0)=0$, $D_{ij}\ge0$ ($j\ne i$) are dispersal rates with $D_{ii}=-\sum_{j\ne i}D_{ij}$, and $\mathbf{E}=\Gamma^\top\mathbf{B}$ is a Brownian motion with covariance $\Sigma=\Gamma^\top\Gamma$. Assume: (i) competition dominates at large total abundance, i.e. there are $M_b,\gamma_b>0$ with $\sum_i x_i(b_i(x_i)-a_i)>\gamma_b\sum_i x_i$ whenever $\sum_i x_i\ge M_b$ (for example $b_i(x)=\kappa_i x$ with $\kappa_i>0$); (ii) $D$ is irreducible; (iii) $\Sigma$ is non-singular.

Without competition, the patch proportions $\tilde{\mathbf{Y}}=\mathbf{X}/\sum_i X_i$ form an ergodic diffusion on the simplex with unique invariant law $\nu^*$. The stochastic growth rate is

$$r=\int_\Delta\Big(\mathbf{a}^\top\mathbf{y}-\tfrac12\,\mathbf{y}^\top\Sigma\,\mathbf{y}\Big)\,\nu^*(d\mathbf{y}),$$

the almost-sure Lyapunov exponent $\lim_{t\to\infty}t^{-1}\ln\sum_i\mathcal{X}_i(t)$ of the linearized system with all $b_i\equiv0$.

**Theorem.**

1. If $r>0$, $\mathbf{X}$ has a unique invariant probability measure $\pi$ on $(0,\infty)^n$, absolutely continuous with respect to Lebesgue measure; for every $q>0$ and every $\mathbf{x}\in(0,\infty)^n$, $t^{q}\,\|P(t,\mathbf{x},\cdot)-\pi\|_{TV}\to0$; and time averages of $\pi$-integrable functions converge almost surely to their $\pi$-means from every nonzero initial state. In particular the population is stochastically persistent.
2. If $r<0$, then for every patch $i$ and every initial state, $\lim_{t\to\infty}t^{-1}\ln X_i(t)=r$ almost surely, so every patch goes extinct exponentially fast.
3. $r$ depends continuously on $(\mathbf{a},D,\Sigma)$, and persistence is robust: sufficiently small, possibly density-dependent, perturbations of the growth rates, dispersal matrix and noise covariance keep a persistent system persistent; extinction is robust under small constant perturbations.

## Expansion

Writing $S=\sum_i X_i$ and $\mathbf{Y}=\mathbf{X}/S$ splits the system into total abundance and spatial distribution. Near $S=0$ the competition terms vanish, so $\mathbf{Y}$ behaves like the competition-free proportion process $\tilde{\mathbf{Y}}$, and Itô's formula gives $d\ln S\approx(\mathbf{a}^\top\mathbf{Y}-\tfrac12\mathbf{Y}^\top\Sigma\mathbf{Y})dt+\mathbf{Y}^\top d\mathbf{E}$; averaging against $\nu^*$ shows that $\ln S$ drifts at rate $r$ when small. If $r>0$, a Lyapunov function of the form $S^{-\theta}$ times a correction decreases on average near the boundary, while assumption (i) gives confinement at infinity; together with irreducibility and non-degenerate noise this yields positive Harris recurrence with polynomial convergence rates. If $r<0$, comparison with the linear system (the drift is cooperative) forces every coordinate to decay at rate $r$. This generalizes and extends the density-independent analysis of Evans and coauthors and resolves one of their conjectures.

## Sources

- Alexandru Hening, Dang H. Nguyen, George Yin, "Stochastic population growth in spatially heterogeneous environments: The density-dependent case", arXiv:1605.02027 (2016); Journal of Mathematical Biology 76 (2018): Section 2 (model, competition and dispersal assumptions, definition of $r$, persistence theorem, persistence corollary and extinction theorem), Appendix on degenerate noise, Appendix "Robustness of the model". <https://doi.org/10.48550/arXiv.1605.02027> Published version: J. Math. Biol. (2018) 76: 697-754.
