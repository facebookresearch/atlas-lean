# Reversibility and the Dirichlet form of the Wright–Fisher diffusion

Let $L = \frac12a\,\partial_x^2 + b\,\partial_x$ with $a(x) = x(1 - x)$ be the Wright–Fisher generator with mutation rates $\theta_1, \theta_2 > 0$ and genic or diploid selection, and let $\pi$ be its stationary density, which has zero probability current: $\frac12(a\pi)' = b\pi$. Then $\pi\,Lg = \frac12(a\pi g')'$, and for polynomials $f$ and $g$, integration by parts gives

$$\int_0^1f\,Lg\,\pi\,dx = \Bigl[\tfrac12a\pi g'f\Bigr]_0^1 - \frac12\int_0^1a\,f'g'\,\pi\,dx = -\frac12\int_0^1a\,f'g'\,\pi\,dx,$$

because $a\pi$ behaves like $x^{\theta_1}$ near $0$ and like $(1 - x)^{\theta_2}$ near $1$ and so vanishes at both endpoints. The right side is symmetric in $f$ and $g$, so $L$ is symmetric in $L^2(\pi)$ on polynomials and $-L$ is nonnegative there, with quadratic form $\mathcal E(f, f) = \frac12\int a\,f'^2\,d\pi$, the classical Dirichlet form of the diffusion (Fukushima, Oshima and Takeda 2011, Chapter 1). This is the self-adjointness with respect to the speed density on which Song and Steinrücken (2012, Background) base the orthogonality of eigenfunctions and the spectral representation, and it corresponds to the reversibility of the Wright–Fisher diffusion with respect to its speed measure noted by Griffiths, Jenkins and Spanò (2018, Section 2); the symmetric relation between the stationary law and the transitions is detailed balance (Kelly 1979, Chapter 1).

## Depends on

- [Speed density with selection and mutation](../../../../Biology/population-genetics/diffusion-theory/scale-and-speed-of-one-dimensional-diffusions/selection-mutation-speed-density.md)
- [Stationary law of the Wright–Fisher diffusion with dominance and mutation](../../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion-with-selection-and-mutat/dominance-stationary-law.md)

## Expansion

1. The zero-current condition and the divergence form $\pi\,Lg = \frac12(a\pi g')'$.
2. Integration by parts with vanishing boundary terms for $\theta_1, \theta_2 > 0$.
3. Closability of $\mathcal E$ on polynomials, its closure, and the associated self-adjoint generator in $L^2(\pi)$.
4. Reversibility of the stationary process: symmetry of the transition kernels with respect to $\pi$.

## Sources

- Y. S. Song and M. Steinrücken, A simple method for finding explicit analytic transition densities of diffusion processes with general diploid selection, Genetics 190 (2012), 1117–1129, Background. <https://doi.org/10.1534/genetics.111.136929>
- R. C. Griffiths, P. A. Jenkins and D. Spanò, Wright–Fisher diffusion bridges, Theor. Popul. Biol. 122 (2018), 67–77; Section 2 in the numbering of the arXiv version, arXiv:1703.00208v3. <https://doi.org/10.1016/j.tpb.2017.09.005>
- M. Fukushima, Y. Oshima and M. Takeda, *Dirichlet Forms and Symmetric Markov Processes*, 2nd ed., de Gruyter Studies in Mathematics 19, de Gruyter, 2011, Chapter 1.
- F. P. Kelly, *Reversibility and Stochastic Networks*, Wiley, 1979, Chapter 1.
