# Unit-level reproduction number from a transmission kernel

Let units (farms) sit at points $x_1, \dots, x_n \in \mathbb{R}^2$ with distances $r_{ij} = |x_i - x_j|$, and let $h : [0, \infty) \to [0, \infty)$ be a transmission kernel, the hazard per unit time with which an infectious unit infects a susceptible unit at distance $r$. If unit $i$ is infectious for a time $T_i$, the probability that it infects unit $j$ is

$$p(r_{ij}; T_i) \;=\; 1 - e^{-h(r_{ij})\, T_i} .$$

In the early phase of an outbreak, when depletion of susceptibles is negligible:

1. The unit-level reproduction number is $R_i = \sum_{j \ne i} \mathbb{E}\bigl[1 - e^{-h(r_{ij}) T_i}\bigr]$.
2. If $T_i$ is gamma distributed with mean $\bar T$ and shape $c > 0$ (scale $\bar T/c$), then

$$R_i \;=\; \sum_{j \ne i} \Bigl[1 - \Bigl(1 + \frac{h(r_{ij})\,\bar T}{c}\Bigr)^{-c}\Bigr],$$

which reduces to $\sum_j (1 - e^{-h(r_{ij})\bar T})$ for a fixed infectious period ($c \to \infty$) and to $\sum_j h(r_{ij})\bar T/(1 + h(r_{ij})\bar T)$ for an exponential one ($c = 1$).
3. If units form a homogeneous planar pattern of density $\rho$ and the infectious period is fixed, then $R = 2\pi\rho \int_0^\infty p(r)\, r\, dr$ with $p(r) = 1 - e^{-h(r)\bar T}$, which is proportional to $\rho$; the threshold $R = 1$ defines the critical density

$$\rho_c \;=\; \Bigl(2\pi \int_0^\infty p(r)\, r\, dr\Bigr)^{-1},$$

above which a single infected unit can start a major outbreak.

A common kernel is $h(r) = h_0 / (1 + (r/r_0)^{\alpha})$, with $h_0$ the hazard at zero distance, $r_0$ the distance at which it halves and $\alpha > 2$ ensuring $\int_0^\infty h(r)\, r\, dr < \infty$.

## Expansion

Each susceptible unit $j$ escapes infection from $i$ with probability $e^{-h(r_{ij})T_i}$ given $T_i$, so the expected number of units infected by $i$ is the sum of the infection probabilities, averaged over $T_i$. For gamma $T$, $\mathbb{E}[e^{-sT}] = (1 + s\bar T/c)^{-c}$, which gives item 2; the limits follow from $(1 + x/c)^{-c} \to e^{-x}$ and direct substitution of $c = 1$. Item 3 replaces the sum by an integral against the intensity $\rho$ in polar coordinates, $\sum_j p(r_{ij}) \approx \int_0^\infty p(r)\, \rho\, 2\pi r\, dr$; solving $R = 1$ gives $\rho_c$. When unit locations form an (inhomogeneous) Poisson process, the offspring number is itself Poisson with mean $R_i$. Applied to the 2003 H7N7 highly pathogenic avian influenza epidemic among Dutch poultry farms, with $\bar T = 7.47$ days and $c = 11.1$, mapping $R_i > 1$ farm by farm identified high-risk areas that contained most of the farms actually infected.

## Sources

- G. J. Boender, T. J. Hagenaars, A. Bouma, G. Nodelijk, A. R. W. Elbers, M. C. M. de Jong, M. van Boven, "Risk maps for the spread of highly pathogenic avian influenza in poultry", *PLoS Computational Biology* 3(4) (2007) e71, Methods, "Modelling Approach and Reproduction Numbers" (Equations 1–5) and "Parameter Estimation" (Equation 6), <https://doi.org/10.1371/journal.pcbi.0030071> (PMC1853123).
