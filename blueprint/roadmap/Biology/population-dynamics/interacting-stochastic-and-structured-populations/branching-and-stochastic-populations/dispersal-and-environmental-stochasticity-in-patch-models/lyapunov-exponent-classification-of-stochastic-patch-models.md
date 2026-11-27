# Lyapunov exponent classification of stochastic patch models

**Deterministic model.** Let $N_i(t)$ be the population in patch $i = 1, \dots, n$ and

$$N_i(t+1) = \sum_{j=1}^n d_{ij} f_j(N_j(t)) N_j(t), \qquad \text{i.e.}\quad \mathbf N(t+1) = D\Lambda(\mathbf N(t))\mathbf N(t),$$

where $d_{ij} \ge 0$ is the fraction moving from patch $j$ to patch $i$, with $d_{ii} = 1 - \sum_{k \ne i} d_{ki}$ the fraction staying, $D = (d_{ij})$ is primitive, and $\Lambda(\mathbf N) = \mathrm{diag}(f_1(N_1), \dots, f_n(N_n))$ holds the per-capita growth functions.

**Theorem 2.1 (deterministic classification).** Suppose each $f_i$ is strictly positive, continuous and decreasing, $\lim_{x \to \infty} f_i(x) < 1$, $x \mapsto x f_i(x)$ is increasing, and $D$ is primitive. If the spectral radius $\lambda(D\Lambda(0))$ exceeds $1$, there is $\bar{\mathbf N} > 0$ with $\mathbf N(t) \to \bar{\mathbf N}$ for every $\mathbf N(0) \in \mathbb R^n_{++}$; if $\lambda(D\Lambda(0)) \le 1$, then $\mathbf N(t) \to 0$ for every $\mathbf N(0) \in \mathbb R^n_+$. Beverton-Holt $f_i(x) = r_i/(1 + \kappa_i x)$, Ivlev and Hassell $f_i(x) = \alpha_i/(1 + K_i x)^c$ with $c < 1$ responses satisfy the hypotheses.

**Stochastic model.** Let the environment $(\xi(t))$ be i.i.d. and set $\mathbf N(t+1) = D(\xi(t))\Lambda(\mathbf N(t), \xi(t))\mathbf N(t)$. If $D$ is almost surely primitive, $\Lambda$ has a strictly positive diagonal and $\mathbb E|\ln\|D(\xi(0))\Lambda(0,\xi(0))\|| < \infty$, the linearization $\tilde{\mathbf N}(t+1) = A(0,\xi(t))\tilde{\mathbf N}(t)$ has a *metapopulation growth rate* $M$ with

$$\lim_{t\to\infty} \frac1t \ln\big(\tilde N_1(t) + \dots + \tilde N_n(t)\big) = M \quad \text{almost surely, for every } \tilde{\mathbf N}(0) \ne 0.$$

**Theorem 2.3 (Beverton-Holt with random dispersal).** Let $\mathbf N(t+1) = D(t)\,\mathrm{diag}\big(r_i(t)/(1 + \kappa_i(t)N_i(t))\big)\mathbf N(t)$, where $\xi(t) = (r_i(t), \kappa_i(t), d_{ij}(t))$ is i.i.d., almost surely $r_i > 0$, $\kappa_i > 0$, $0 < d_{ij} < 1$ and $\sum_j d_{ij} = 1$, and $\mathbb E \ln^+\big(\max_j r_j/\kappa_j + \max_j r_j + 2\max_j r_j\kappa_j\big) < \infty$. Then $M$ exists; if $M < 0$, $\mathbf N(t) \to 0$ almost surely from every initial state; if $M > 0$, $\mathbf N(t)$ converges in distribution to a positive random vector $\mathbf N(\infty)$, and the noise-induced change in expected total size $H = \sum_i \mathbb E N_i(\infty) - \sum_i \bar N_i$, measured against the globally attracting equilibrium $\bar{\mathbf N}$ of the model with averaged parameters, is well defined.

**Theorem 2.4 (Hassell).** The same classification holds for $f_i(x) = \alpha_i(t)/(1 + K_i(t)x)^c$ with $c \in (0,1)$ under the analogous moment and positivity conditions.

**Slow and fast dispersal.** With uniform dispersal of a fraction $\eta$, $D = (1-\eta)I + \eta U_n$ ($U_n$ the matrix with all entries $1/n$), $M(\eta)$ is continuous in $\eta$, with

$$M(0) = \max_i \mathbb E\ln r_i, \qquad M(1) = \mathbb E\ln\Big(\frac1n\sum_{i=1}^n r_i\Big) > \frac1n\sum_{i=1}^n \mathbb E\ln r_i.$$

So with small dispersal one source patch ($\mathbb E\ln r_i > 0$) keeps the whole system alive, and with near-complete mixing even all-sink systems ($\mathbb E\ln r_i < 0$ for every $i$) can persist.

## Expansion

Primitivity makes the patches survive or die together, so the $n$-dimensional system behaves like a single species and the general persistence theory for random products of nonlinear positive maps applies once a Lyapunov-type function $V$ with $V(A(\xi,x)x) \le \alpha(\xi)V(x) + \beta(\xi)$, $\mathbb E\ln\alpha < 0$, controls large populations and the entries of $A$ are decreasing in $\mathbf N$ (Assumption 2.2, Theorem 2.2). The Beverton-Holt and Hassell bounds verify these hypotheses (Appendices B and C). The values of $M(0)$ and $M(1)$ come from the decoupled and the fully mixed linearizations; Jensen's inequality gives the strict inequality for $M(1)$. The deterministic threshold in Theorem 2.1 is $\lambda(D\Lambda(0)) > 1$ for growth of the linearization at zero; the printed statement compares the spectral radius with $0$, which is automatic for a primitive positive matrix.

## Sources

- A. Hening, S. Sabharwal, "Population size in stochastic multi-patch ecological models", *Journal of Mathematical Biology* 92(3) (2026), 43, Section 2 (Theorem 2.1, Assumptions 2.1 to 2.4, Theorems 2.2 to 2.4, Remark 2.8 and the slow and fast dispersal subsection), Appendices B and C, <https://doi.org/10.1007/s00285-026-02365-7> (preprint arXiv:2511.19743).
