# Next-generation reproduction number of an SEAIR model on a weighted mobility graph

**Model.** Cities form the vertex set $V = \{1, \dots, n\}$ of a graph with mobility weights $\omega(x,y) \ge 0$ (flow from city $y$ to city $x$, $\omega(x,x) = 0$), adjacency matrix $M = (\omega_{ij})$, discrete Laplacian and travel-contact operator

$$\Delta_\omega f(x) = \sum_{y \sim x}\big(\omega(x,y) f(y) - \omega(y,x) f(x)\big), \qquad \nabla_\omega f(x) = \sum_{y \sim x}\omega(x,y) f(y).$$

In each city susceptible ($S$), exposed ($E$), asymptomatic ($A$), symptomatic ($I$) and removed ($R$) individuals evolve with transmission rate $\beta$, relative infectiousness $\xi$ of asymptomatics, incubation rate $\sigma$, symptomatic fraction $\theta$, removal rates $\gamma_A, \gamma_I$, a fraction $\varepsilon$ of symptomatics able to travel, and an elevated in-transit transmission rate $\beta^* = k\beta$:

$$\partial_t S - \Delta_\omega S + \beta^*\nabla_\omega(\varepsilon I + \xi A) = -\beta S\frac{I + \xi A}{N}, \qquad \partial_t E - \Delta_\omega E - \beta^*\nabla_\omega(\varepsilon I + \xi A) = \beta S \frac{I + \xi A}{N} - \sigma E,$$

$$\partial_t A - \Delta_\omega A = (1-\theta)\sigma E - \gamma_A A, \qquad \partial_t I - \varepsilon\Delta_\omega I = \theta\sigma E - \gamma_I I, \qquad \partial_t R - \Delta_\omega R = \gamma_A A + \gamma_I I.$$

Assume time-independent parameters and balanced travel at the disease-free equilibrium $(N^*, 0, 0, 0, 0)$: $\omega(y,x)N^*(x) = \omega(x,y)N^*(y)$.

**Reproduction number.** With $D_\omega = \operatorname{diag}\big(\sum_j \omega_{ji}\big)$,

$$V_{11} = \sigma I_n + D_\omega - M, \qquad V_{22} = \gamma_A I_n + D_\omega - M, \qquad V_{33} = \gamma_I I_n + \varepsilon(D_\omega - M),$$

the next-generation method gives $R_0 = \rho(FV^{-1}) = \rho(K_{\mathrm{loc}} + K_{\mathrm{tr}})$, where

$$K_{\mathrm{loc}} = \beta\sigma\big(\xi(1-\theta)V_{22}^{-1}V_{11}^{-1} + \theta V_{33}^{-1}V_{11}^{-1}\big), \qquad K_{\mathrm{tr}} = \beta^*\sigma\big(\xi(1-\theta)MV_{22}^{-1}V_{11}^{-1} + \theta\varepsilon MV_{33}^{-1}V_{11}^{-1}\big),$$

$K_{\mathrm{loc}}$ counting infections within cities and $K_{\mathrm{tr}}$ infections acquired while travelling. The spectral radius is taken of the sum: in general $\rho(K_{\mathrm{loc}} + K_{\mathrm{tr}}) \ne \rho(K_{\mathrm{loc}}) + \rho(K_{\mathrm{tr}})$. Without mobility ($M = 0$), $R_0 = \beta\big(\xi(1-\theta)/\gamma_A + \theta/\gamma_I\big)$.

**Theorem.** Under the assumptions above, if the mobility weights are small or $M$ is irreducible, and $R_0 < 1$, then the disease-free equilibrium is globally asymptotically stable for all nonnegative initial data with some initial infection whose initial total population is the equilibrium one, $N(x,0)=N^*(x)$ for every city $x$ (the source's (A1)). Without that condition the statement fails, since the total population is conserved: data with $S(\cdot,0)=2N^*$ cannot approach $(N^*,0,0,0,0)$.

## Expansion

When the $\omega_{ij}$ are small (or $M$ is irreducible), $V_{11}, V_{22}, V_{33}$ are irreducible nonsingular M-matrices with positive column sums, so their inverses are positive and $FV^{-1}$ has a single nonzero block row. Its nonzero eigenvalues are those of the block $F_{12}V_{22}^{-1}V_{21}V_{11}^{-1} + F_{13}V_{33}^{-1}V_{31}V_{11}^{-1}$ with $F_{12} = \beta\xi I_n + \beta^*\xi M$, $F_{13} = \beta I_n + \beta^*\varepsilon M$, $V_{21} = (1-\theta)\sigma I_n$ and $V_{31} = \theta\sigma I_n$, which is $K_{\mathrm{loc}} + K_{\mathrm{tr}}$; the travel matrix $M$ acts after the residence times, on the left. The source's Eq. (3.1) states this block correctly but then splits $R_0$ into a sum of two spectral radii with $M$ placed between $V_{22}^{-1}$ (or $V_{33}^{-1}$) and $V_{11}^{-1}$, which is not equal to $\rho(FV^{-1})$ in general. The global stability statement is stated as a modification of an earlier result for reaction–diffusion epidemic models on graphs, and its proof is omitted in the source. The decomposition shows how travel restrictions act: lowering $M$ (and $\varepsilon$) shrinks the second term, while local measures lower $\beta$; staged response levels make $\beta$, $\omega$ and $\gamma$ piecewise constant in time, giving stage-wise reproduction numbers.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Sources

- J. Ge, D. He, Z. Lin and H. Zhu, "Four-tier response system and spatial propagation of COVID-19 in China by a network model", arXiv:2008.08152 (2020), Section 2 (weighted network model and graph operators), Section 3 (next-generation matrix, reproduction number and Theorem 3.1), <https://doi.org/10.48550/arXiv.2008.08152>.
