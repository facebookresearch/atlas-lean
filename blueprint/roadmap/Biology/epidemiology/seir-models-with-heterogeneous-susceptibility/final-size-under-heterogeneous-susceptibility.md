# Final size under heterogeneous susceptibility

**Model.** Each host has a fixed trait $x \ge 0$ with population density $\phi$, normalized so that susceptibility equals $x$ and $\int_0^\infty x\phi(x)\,dx = 1$. With exposed and infectious exit rates $\alpha$ and $\gamma$ and infectiousness $c(x)$,

$$\partial_t s = -x s F(t), \quad \partial_t e = x s F(t) - \alpha e, \quad \partial_t i = \alpha e - \gamma i, \quad F(t) = \int_0^\infty c(x)i(t,x)\phi(x)\,dx.$$

Starting from $s_0 \equiv 1$ one has $s(t,x) = \bar s(t)^x$ with $\bar s = s(\cdot, 1)$. Let $\Phi_k(w) = \int_0^\infty x^k w^x\phi(x)\,dx$. Two cases close into three ODEs:

- *independent infectiousness*, $c \equiv \beta$ (labeled $k = 1$): $\bar s' = -\beta\bar sI$, $E' = \beta\Phi_1(\bar s)I - \alpha E$, $I' = \alpha E - \gamma I$;
- *perfectly correlated infectiousness*, $c(x) = \beta x$ (labeled $k = 2$): the same system for $(\bar s, U, V)$ with $\Phi_2$ in place of $\Phi_1$, where $U, V$ are the susceptibility-weighted exposed and infectious totals.

An outbreak can start iff $\mathcal R_0 = \beta\Phi_k(1)/\gamma > 1$; for $k = 1$ this is $\beta/\gamma$, for $k = 2$ it is $(\beta/\gamma)(1 + \mathrm{Var}(x))$.

**Final-size equation.** Since $\Phi_{k-1}$ is a primitive of $\Phi_k(w)/w$, the quantity $\Phi_{k-1}(\bar s) + E + I - \frac\gamma\beta\log\bar s$ (resp. with $U, V$) is conserved, and an outbreak started near $\bar s = 1$ ends at $\bar s_\infty$ solving

$$\Phi_{k-1}(\bar s_\infty) - \frac\gamma\beta\log\bar s_\infty = 1.$$

**Theorem.** This equation has a unique solution $\bar s_\infty \in (0,1)$ if $\mathcal R_0 > 1$ and none in $(0,1)$ if $\mathcal R_0 \le 1$. The final total susceptible fraction $\bar S_\infty = \Phi_0(\bar s_\infty)$ is larger than the final susceptible fraction of the homogeneous model with the same $\mathcal R_0$: for every susceptibility distribution, in both cases, heterogeneity lowers the attack ratio.

## Depends on

- [Final-size relation (Kermack-McKendrick 1927)](../kermack-mckendrick-sir-model/final-size.md)

## Expansion

The key identity $s(t,x) = \bar s(t)^x$ says that heterogeneous hosts share one cumulative force of infection, so the infinite-dimensional system collapses onto the Laplace-type transforms $\Phi_k$. For $G_k(w) = \Phi_{k-1}(w) - \frac\gamma\beta\log w$ one has $G_k(0^+) = +\infty$, $G_k(1) = 1$, every critical point is a minimum, and $G_k'(1) = \Phi_k(1)(1 - 1/\mathcal R_0)$, which is negative iff $\mathcal R_0 > 1$; this gives existence and uniqueness. The comparison with the homogeneous model follows from Jensen's inequality, $\Phi_0(w) = \mathbb E(w^X) > w^{\mathbb E X} = w$ (and an analogous convexity bound when $k = 2$). Biologically, the most susceptible hosts are infected first, so the effective susceptibility of the remaining population drops faster than in a homogeneous population, and the epidemic burns out earlier.

## Sources

- T. Tekeli, A. Pugliese and C. Soresina, "SEIR models with host heterogeneity: theoretical aspects and applications to seasonal influenza dynamics", arXiv preprint (2025), Sections 2 and 3, Theorem 3.1 and its proof in Appendix A. <https://doi.org/10.48550/arXiv.2511.18142>