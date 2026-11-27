# The forward equation as an equation for measures

For a diffusion on $[0, 1]$ with drift $\mu$ and infinitesimal variance $\sigma^2$, the law $\mu_t$ of $X_t$ satisfies the forward equation in the weak sense: by the martingale property of $f(X_t) - \int_0^tLf(X_s)\,ds$, $\frac{d}{dt}\int f\,d\mu_t = \int Lf\,d\mu_t$ for every $f$ in a core of the generator. The density form $\partial_tp = -\partial_y(\mu p) + \frac12\partial_y^2(\sigma^2p)$ is derived by integrating the backward equation by parts against the transition density (Karlin and Taylor 1981, Chapter 15); the derivation discards boundary terms and requires $\mu$ to be differentiable and $\sigma^2$ to be twice differentiable. When the endpoints are absorbing those boundary terms carry mass: Zhao, Lascoux, Overall and Waxman (2013, Appendix A) use the complete distribution of the Wright–Fisher frequency, which integrates to $1$ over $[0, 1]$ and contains Dirac masses at $0$ and $1$ for loss and fixation, so that

$$\mu_t(dy) = P_x(X_t = 0)\,\delta_0(dy) + p(t, x, y)\,dy + P_x(X_t = 1)\,\delta_1(dy),$$

with an interior density of total mass $P_x(\tau > t)$, where $\tau$ is the absorption time. The forward equation is then an equation for $\mu_t$: the density form holds on $(0, 1)$, and, from the weak form with $f$ approximating the indicators of $\{0\}$ and $\{1\}$, the masses of the two atoms grow at the rates at which probability leaves the interior through each endpoint. Epstein and Pop (2019, Theorem 1.7 and Section 3) prove for generalized Kimura operators that the Dirichlet heat kernel is a weak solution of the forward equation in its final point.

## Depends on

- [Dynkin's formula at a fixed time](../../../Biology/population-genetics/diffusion-theory/fixation-and-absorption-in-the-wright-fisher-dif/integral-generator.md)

## Expansion

1. The weak forward equation for $\mu_t$ from Dynkin's formula at fixed times.
2. The decomposition of $\mu_t$ into the interior density and the two atoms when the endpoints are absorbing.
3. The strong equation for the interior density when $\mu$ is differentiable and $\sigma^2$ twice differentiable, and the rates of change of the atoms as boundary fluxes.
4. The neutral case without mutation, in which the interior density is Kimura's eigenfunction series and the atoms are the probabilities of loss and fixation by time $t$.

## Sources

- S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press, New York (1981), Chapter 15 (the forward equation).
- S. Zhao, M. Lascoux, A. D. J. Overall and D. Waxman, The characteristic trajectory of a fixing allele: a consequence of fictitious selection that arises from conditioning, Genetics 195 (2013), 993–1006, Appendix A. <https://doi.org/10.1534/genetics.113.156059>
- C. L. Epstein and C. A. Pop, Transition probabilities for degenerate diffusions arising in population genetics, Probab. Theory Related Fields 173 (2019), 537–603; Theorem 1.7 and Section 3 in the numbering of the arXiv version, arXiv:1608.02119v2. <https://doi.org/10.1007/s00440-018-0840-2>
- R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed., Springer, New York (2008), Chapter 7, Sections 7.3–7.7 (the diffusion facts cited above from Karlin and Taylor, Chapter 15). <https://doi.org/10.1007/978-0-387-78168-6>
