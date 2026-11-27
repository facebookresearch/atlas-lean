# Spectral expansion of the neutral multi-allele transition density

For the neutral $K$-allele Wright–Fisher diffusion with parent-independent mutation rates $\theta_1, \dots, \theta_K > 0$, with generator $\mathcal L_0$ as in Steinrücken, Wang and Song (2013, Section 2.1) with no selection, the multivariate Jacobi polynomials $P^\theta_n$, $n \in \mathbb N_0^{K-1}$, orthogonal on $\Delta_{K-1}$ with respect to $\Pi_0(x) = \prod_{i=1}^Kx_i^{\theta_i - 1}$, are eigenfunctions:

$$\mathcal L_0P^\theta_n = -\lambda^\theta_{|n|}P^\theta_n, \qquad \lambda^\theta_{|n|} = \frac12|n|(|n| - 1 + |\theta|)$$

(Lemma 5, equation (18)), and the transition density has the expansion

$$p(t; x, y) = \sum_{n\in\mathbb N_0^{K-1}}\frac{1}{C^\theta_n}e^{-\lambda^\theta_{|n|}t}P^\theta_n(x)P^\theta_n(y)\Pi_0(y)$$

(equation (19)), with $C^\theta_n$ the normalizing constants of equation (14). The eigenvalues depend on $n$ only through $|n|$, so the spectrum is degenerate; the authors attribute the explicit spectral representation to Shimakura (1977) and Griffiths (1979), who formed orthogonal kernel polynomials by summing over the polynomials with fixed $|n|$. For $K = 2$ the eigenvalues are $\frac12n(n - 1 + \alpha + \beta)$, with modified Jacobi polynomials as eigenfunctions (Section 2.4).

## Depends on

- [Transition density of the multi-allelic Wright–Fisher diffusion with selection](../../../../Biology/population-genetics/diffusion-theory/transition-densities-of-wright-fisher-diffusions/multi-allelic-transition-density-with-selection.md)
- [Uniqueness of the Dirichlet stationary law under parent-independent mutation](../../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion-with-mutation/dirichlet-stationary-law-under-parent-independent-mutation.md)
- [Generator of the K-allele Wright–Fisher diffusion with mutation and genic selection](../wright-fisher-diffusion-with-selection-and-mutat/k-allele-wright-fisher-generator-on-the-simplex.md)

## Expansion

1. Multivariate Jacobi polynomials on the simplex and their orthogonality for the Dirichlet weight.
2. The eigenvalue equation for $\mathcal L_0$, by its action on monomials.
3. Convergence of the expansion for $t > 0$ and its identification with the transition density.
4. The kernel polynomials of degree $|n|$ and the degenerate spectrum.

## Sources

- M. Steinrücken, Y. X. R. Wang and Y. S. Song, An explicit transition density expansion for a multi-allelic Wright–Fisher diffusion with general diploid selection, Theor. Popul. Biol. 83 (2013), 1–14, Sections 2.4 and 3.3, Lemma 5, equations (13), (14), (18) and (19). <https://doi.org/10.1016/j.tpb.2012.10.006>
- Original result: R. C. Griffiths, A transition density expansion for a multi-allele diffusion model, Adv. Appl. Probab. 11 (1979), 310–325. <https://doi.org/10.2307/1426842> The expansion follows Steinrücken, Wang and Song, Section 3.3.
