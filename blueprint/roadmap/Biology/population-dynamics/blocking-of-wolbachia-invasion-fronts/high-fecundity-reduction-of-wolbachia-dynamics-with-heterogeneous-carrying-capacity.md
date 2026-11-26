# High-fecundity reduction of Wolbachia dynamics to a scalar equation with heterogeneous carrying capacity

**Model.** Infected ($n_i$) and uninfected ($n_u$) mosquito densities on $\mathbb{R}^d$ satisfy

$$
\begin{aligned}
\partial_t n_i - \Delta n_i &= (1-s_f) F_u\, n_i \Big(1 - \frac{N}{K(x)}\Big) - \delta d_u\, n_i,\\
\partial_t n_u - \Delta n_u &= F_u\, n_u (1 - s_h p)\Big(1 - \frac{N}{K(x)}\Big) - d_u\, n_u,
\end{aligned}
\qquad N = n_i + n_u, \quad p = \frac{n_i}{N},
$$

where $d_u$ and $\delta d_u$ are death rates ($\delta > 1$: Wolbachia shortens lifespan), $F_u$ and $(1-s_f)F_u$ fecundities ($0 < s_f < 1$), $s_h \in (0,1]$ the cytoplasmic incompatibility strength and $K(x)$ the carrying capacity. Assume $s_f + \delta - 1 < s_h\delta$, so that the Wolbachia-free and the invaded equilibria are both stable. Let $F_u = \tilde F_u/\epsilon$ (high fecundity).

**Theorem.** Let $T > 0$. Suppose $K \in C^2 \cap L^\infty(\mathbb{R}^d)$ with $K \ge c' > 0$, $\nabla K \in L^2$ and $\Delta K \in L^1$, and that the initial data are uniformly bounded in $L^\infty$, $n_i^{\mathrm{init}} \ge 0$, $n_u^{\mathrm{init}} > 0$, with infection fraction $p^{\mathrm{init},\epsilon}$ bounded in $L^2$ and converging weakly to $p^{\mathrm{init}}$ (plus a compatibility condition on the initial total population). Then as $\epsilon \to 0$ the infection fraction $p^\epsilon = n_i^\epsilon/(n_i^\epsilon + n_u^\epsilon)$ converges strongly in $L^2(0,T; L^2(\mathbb{R}^d))$ and weakly in $L^2(0,T; H^1(\mathbb{R}^d))$ to the unique solution $p^0$ of

$$
\partial_t p - \Delta p - 2\frac{\nabla K}{K}\cdot\nabla p = f(p) + \frac{\Delta K}{K}\, g(p), \qquad p(0) = p^{\mathrm{init}},
$$

with

$$
f(p) = p(1-p)\,\frac{d_u(\delta s_h p - s_f + 1 - \delta)}{(1-s_f)p + (1-p)(1-s_h p)}, \qquad g(p) = \frac{-p(1-p)(s_h p - s_f)}{(1-s_f)p + (1-p)(1-s_h p)}.
$$

The reaction $f$ is bistable: $f(0) = f(\theta_1) = f(1) = 0$ with $\theta_1 = \frac{\delta - 1 + s_f}{s_h\delta} \in (0,1)$, $f < 0$ on $(0, \theta_1)$ and $f > 0$ on $(\theta_1, 1)$. Spatial variation of $K$ enters only through the drift $2\nabla K/K$ and the extra reaction $(\Delta K/K)\, g$.

## Expansion

Rewrite the system for $(N^\epsilon, p^\epsilon)$; the $p$-equation acquires the drift $2\nabla N^\epsilon\cdot\nabla p^\epsilon/N^\epsilon$. Under high fecundity the population saturates at capacity, so set $N^\epsilon = K(1 - \epsilon z^\epsilon)$; matching leading orders gives $z^\epsilon$ explicitly as a function of $p^\epsilon$ and $\Delta K/K$, which, inserted into the $p$-equation, yields the limit equation up to a term $2\nabla\ln(1-\epsilon z^\epsilon)$. Rigorously, a maximum principle gives $0 \le p^\epsilon \le 1$ and a uniform bound on $z^\epsilon$; energy estimates bound $\epsilon\|\nabla z^\epsilon\|^2_{L^2}$ and $\|\nabla p^\epsilon\|^2_{L^2}$ uniformly; the Aubin–Lions lemma then supplies strong compactness, so the nonlinear terms pass to the limit and the vanishing correction drops out. With constant $K$ this recovers the classical reduction to the scalar bistable equation $\partial_t p - \Delta p = f(p)$.

## Sources

- S. Latrach, N. Vauchelet and H. Zaag, *Blocking of bistable front propagation: Application to Wolbachia population replacement*, arXiv:2610.13497 (2026), Section 2.1 (model), Section 2.2 (convergence theorem, bistability remark) and Section 3 (proof of the reduction). <https://doi.org/10.48550/arXiv.2610.13497>
