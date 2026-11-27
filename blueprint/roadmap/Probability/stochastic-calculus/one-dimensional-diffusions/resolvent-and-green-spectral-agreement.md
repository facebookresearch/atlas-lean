# Resolvents, Green functions and spectral expansions

For a diffusion on $(0, 1)$ killed on reaching $0$ or $1$, suppose that the killed transition density has the spectral representation $q_t(x, y) = \sum_{n \ge 1}e^{-\Lambda_nt}\pi(y)B_n(x)B_n(y)/\langle B_n, B_n\rangle_\pi$ with speed density $\pi$, eigenvalues $0 < \Lambda_1 < \Lambda_2 < \cdots$ and eigenfunctions $B_n$ of the backward generator, as in Song and Steinrücken (2012, equation (5)). If, for fixed $x$ and $y$ in $(0, 1)$, $\sum_{n \ge 1}|B_n(x)B_n(y)|/(\Lambda_n\langle B_n, B_n\rangle_\pi) < \infty$, then integrating the series term by term, justified by Fubini's theorem since $\int_0^\infty e^{-\Lambda_nt}\,dt = 1/\Lambda_n$, gives for every $\lambda \ge 0$

$$\int_0^\infty e^{-\lambda t}q_t(x, y)\,dt = \pi(y)\sum_{n \ge 1}\frac{B_n(x)B_n(y)}{(\lambda + \Lambda_n)\langle B_n, B_n\rangle_\pi},$$

the kernel of the resolvent $(\lambda - L)^{-1}$ of the killed process, and at $\lambda = 0$ the Green's function. Since $\int_0^\infty\int_0^1q_t(x, y)g(y)\,dy\,dt = E_x\int_0^\tau g(X_t)\,dt$ for bounded $g$, with $\tau$ the absorption time, this $\lambda = 0$ kernel coincides almost everywhere in $y$ with the Green's function of Karlin and Taylor (1981, Chapter 15), $G(x, y) = 2\frac{S(\min(x,y)) - S(0)}{S(1) - S(0)}(S(1) - S(\max(x,y)))\,m(y)$, by uniqueness of the density of the occupation measure. For the neutral Wright–Fisher diffusion without mutation, $B_n(x) = x(1 - x)C_{n - 1}^{(3/2)}(1 - 2x)$ in Gegenbauer polynomials with $\Lambda_n = n(n + 1)/2$ for $n \ge 1$ (Song and Steinrücken 2012, section on genic selection; Griffiths, Jenkins and Spanò 2018, equation (4) of the arXiv version), and the identity expresses $2\min(x, y)(1 - \max(x, y))/(y(1 - y))$ as the corresponding series.

## Depends on

- [Dirichlet Green's function of a one-dimensional diffusion](../../../Biology/population-genetics/diffusion-theory/selection-duality-and-general-one-dimensional-di/green-function.md)
- [Neutral Wright–Fisher Green's function](../../../Biology/population-genetics/diffusion-theory/sojourn-times-of-the-wright-fisher-diffusion/neutral-green.md)

## Expansion

1. The killed semigroup, its spectral representation, and positivity of the eigenvalues of the killed generator.
2. The Laplace transform of the series and Fubini's theorem under absolute summability.
3. Identification of the $\lambda = 0$ kernel with the Green's function through the occupation measure.
4. Absolute summability for the neutral Gegenbauer series at interior points, from bounds on Gegenbauer polynomials in the interior of $[-1, 1]$.

## Sources

- Y. S. Song and M. Steinrücken, A simple method for finding explicit analytic transition densities of diffusion processes with general diploid selection, Genetics 190 (2012), 1117–1129, Background, equation (5), and the section on genic selection. <https://doi.org/10.1534/genetics.111.136929>
- R. C. Griffiths, P. A. Jenkins and D. Spanò, Wright–Fisher diffusion bridges, Theor. Popul. Biol. 122 (2018), 67–77; Section 2 and equation (4) in the numbering of the arXiv version, arXiv:1703.00208v3. <https://doi.org/10.1016/j.tpb.2017.09.005>
- S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press, New York (1981), Chapter 15 (the Green's function in terms of the scale function and speed density).
