# Resolvents, Green functions and spectral expansions

This page records two cited ingredients for a diffusion on $(0, 1)$ killed on reaching $0$ or $1$, and states their agreement as its own target in the Expansion.

First, the spectral representation of the transition density: Song and Steinrücken (2012, equation (5)) write the killed transition density as $q_t(x, y) = \sum_{n \ge 1}e^{-\Lambda_nt}\pi(y)B_n(x)B_n(y)/\langle B_n, B_n\rangle_\pi$, with $\pi$ the speed density in their normalization, eigenvalues $0 < \Lambda_1 < \Lambda_2 < \cdots$ and eigenfunctions $B_n$ of the backward generator. For the neutral Wright–Fisher diffusion without mutation, $B_n(x) = x(1 - x)C_{n - 1}^{(3/2)}(1 - 2x)$ in Gegenbauer polynomials with $\Lambda_n = n(n + 1)/2$ for $n \ge 1$ (Song and Steinrücken 2012, section on genic selection; Griffiths, Jenkins and Spanò 2018, equation (4) of the arXiv version).

Second, the closed-form Green's function of Karlin and Taylor (1981, Chapter 15), as stated in Durrett (2008, Theorem 7.16, equation (7.34), and Example 7.23, equation (7.43)): for the generator $\frac12\sigma^2(x)f'' + \mu(x)f'$ with scale function $S$ and speed density $m = 1/(\sigma^2S')$, $G(x, y) = 2\frac{S(\min(x,y)) - S(0)}{S(1) - S(0)}(S(1) - S(\max(x,y)))\,m(y)$, so that $E_x\int_0^\tau g(X_t)\,dt = \int_0^1G(x, y)g(y)\,dy$ for bounded $g$, with $\tau$ the absorption time; for the neutral Wright–Fisher diffusion without mutation, $G(x, y) = 2\min(x, y)(1 - \max(x, y))/(y(1 - y))$.

## Depends on

- [Dirichlet Green's function of a one-dimensional diffusion](../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/green-function.md)
- [Neutral Wright–Fisher Green's function](../../../Biology/population-genetics/diffusion-theory/sojourn-times-of-the-wright-fisher-diffusion/neutral-green.md)
- [Scale function of a one-dimensional diffusion](../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/scale-function.md)
- [Speed density of a one-dimensional diffusion](../../../Biology/population-genetics/diffusion-theory/scale-and-speed-of-one-dimensional-diffusions/speed-density.md)

## Expansion

1. The killed semigroup, its spectral representation (5), and positivity of the eigenvalues of the killed generator.
2. The page's own target, not stated in the cited sources: if, for fixed $x$ and $y$ in $(0, 1)$, $\sum_{n \ge 1}|B_n(x)B_n(y)|/(\Lambda_n\langle B_n, B_n\rangle_\pi) < \infty$, then integrating the series term by term (Fubini's theorem, since $\int_0^\infty e^{-\Lambda_nt}\,dt = 1/\Lambda_n$) gives, for every $\lambda \ge 0$, $\int_0^\infty e^{-\lambda t}q_t(x, y)\,dt = \pi(y)\sum_{n \ge 1}B_n(x)B_n(y)/((\lambda + \Lambda_n)\langle B_n, B_n\rangle_\pi)$, the kernel of the resolvent $(\lambda - L)^{-1}$ of the killed process.
3. The page's own target, not stated in the cited sources: at $\lambda = 0$ this kernel coincides almost everywhere in $y$ with the closed-form Green's function $G(x, y)$, since $\int_0^\infty\int_0^1q_t(x, y)g(y)\,dy\,dt = E_x\int_0^\tau g(X_t)\,dt$ for bounded $g$ and the density of the occupation measure is unique; for the neutral Wright–Fisher diffusion this expresses $2\min(x, y)(1 - \max(x, y))/(y(1 - y))$ as the Gegenbauer series.
4. Absolute summability for the neutral Gegenbauer series at interior points, from bounds on Gegenbauer polynomials in the interior of $[-1, 1]$.

## Sources

- Y. S. Song and M. Steinrücken, A simple method for finding explicit analytic transition densities of diffusion processes with general diploid selection, Genetics 190 (2012), 1117–1129, Background, equation (5), and the section on genic selection. <https://doi.org/10.1534/genetics.111.136929>
- R. C. Griffiths, P. A. Jenkins and D. Spanò, Wright–Fisher diffusion bridges, Theor. Popul. Biol. 122 (2018), 67–77; Section 2 and equation (4) in the numbering of the arXiv version, arXiv:1703.00208v3. <https://doi.org/10.1016/j.tpb.2017.09.005>
- S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press, New York (1981), Chapter 15 (the Green's function in terms of the scale function and speed density).
- R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed., Springer, New York (2008), Theorem 7.16, equation (7.34), and Example 7.23, equation (7.43).
