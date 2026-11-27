# Success condition for diffusible public goods

Keep the finite, connected, bi-transitive weighted graph $G$ on $N$ vertices (with $e_{ij} = e_{ji}$, $e_{ii} = 0$, and $\sum_j e_{ij} = 1$), diffusion parameter $\lambda > 0$, and the [retention fractions](public-goods-diffusion-equilibrium.md) $\phi_0$ (share kept by the producer) and $\phi_1$ (edge-weighted share reaching one neighbour). Let the fecundity of cell $i$ be

$$F_i = 1 + b\,\psi_i - c\, s_i, \qquad b > 0,\; 0 < c < 1,$$

and let the population evolve by death–birth updating: a uniformly chosen cell dies and its neighbours compete to fill the vacancy in proportion to fecundity times edge weight. Write $\rho_C$ and $\rho_D$ for the fixation probabilities of a single cooperator in a defector population and of a single defector in a cooperator population; cooperation is **favoured** when $\rho_C > \rho_D$.

**Theorem (finite-$N$ and large-population limit).** On a finite bi-transitive graph of $N > 2$ vertices under weak selection ($b, c \to 0$), cooperation is favoured when

$$\frac{b}{c} > \frac{N - 2}{N(\phi_0 + \phi_1) - 2}$$

(assuming $N(\phi_0 + \phi_1) > 2$; on the complete graph $K_N$ this reduces to $b/c > 1 + N\lambda/(N-1)$ and holds for arbitrary selection strength). In the large-population limit $N \to \infty$, the threshold simplifies to (Eq. 2)

$$\frac{b}{c} > \frac{1}{\phi_0 + \phi_1},$$

equivalently, using $(1+\lambda)\phi_0 = 1 + \lambda\phi_1$,

$$\frac{b}{c} > \frac{\lambda}{\phi_0 (1 + 2\lambda) - 1}.$$

In the $N \to \infty$ limit this holds for arbitrary selection strength on one-dimensional lattices and under weak selection on other bi-transitive graphs; it is unchanged under a variety of other diffusion processes, including diffusion along a graph different from the replacement graph, in which case $\phi_1$ is computed with the replacement graph's weights.

**Reading.** In the large-population limit, the benefit a cooperator confers on itself, $b\phi_0$, plus the benefit it confers on one average neighbour, $b\phi_1$, must exceed the cost $c$ of production. Only the zeroth and first neighbourhood shells enter; benefits reaching cells at distance two or more are irrelevant to the outcome, however large they are in total.

**Regimes.** For $\lambda \ll 1$ the good is effectively private, $\phi_0 \to 1$, and in the large-$N$ limit production is favoured whenever $b/c > 1$. On any finite graph of $N$ vertices, as $\lambda \to \infty$ the good is shared evenly ($\phi_0, \phi_1 \to 1/N$, so $N(\phi_0 + \phi_1) \to 2$) and the finite-$N$ threshold $(N-2)/(N(\phi_0 + \phi_1) - 2)$ diverges to $+\infty$, making cooperation unattainable for any finite $b/c$. In the $N \to \infty$ limit, the small-$\lambda$ expansion gives

$$\frac{b}{c} > 1 + \frac{\lambda(\kappa - 1)}{\kappa} + O(\lambda^2),$$

so the threshold rises with the diffusion parameter and with the [Simpson degree](retention-fraction-from-a-random-walk-generating-function.md) $\kappa$: more diffusion and more neighbours both make cooperation harder.

## Depends on

- [Public-goods diffusion equilibrium on a weighted graph](public-goods-diffusion-equilibrium.md)
- [Retention fraction from a random-walk generating function](retention-fraction-from-a-random-walk-generating-function.md)

## Expansion

The proof combines two random walks. The public-goods distribution is a geometric sum over walks from the producer, which supplies $\phi_0$ and $\phi_1$; the assortment of types under death–birth updating is described by coalescing random walks tracing ancestral lineages, which supplies the probability that a competitor for a vacancy is of the same type as the cell that produced the good. Under death–birth updating the competition for a vacant site is among the neighbours of that site, so what matters is the comparison of fecundities within one neighbourhood; benefits delivered further away raise everyone's fecundity in the relevant comparison equally and cancel. That cancellation, not a decay of the public good with distance, is why only $\phi_0 + \phi_1$ appears. The simplicity of the resulting threshold is the striking part: the diffusion process can spread the good over the whole graph in complicated patterns, and the entire effect on evolution is two numbers.

## Sources

- B. Allen, J. Gore and M. A. Nowak, "Spatial dilemmas of diffusible public goods", eLife 2 (2013), e01169, Results (Eq. (2), the equivalent form, the three regimes) and Materials and methods / Supplementary file 1 (derivation by coalescing random walks, small-$\lambda$ expansion), <https://doi.org/10.7554/elife.01169>, PMCID PMC3865686.
