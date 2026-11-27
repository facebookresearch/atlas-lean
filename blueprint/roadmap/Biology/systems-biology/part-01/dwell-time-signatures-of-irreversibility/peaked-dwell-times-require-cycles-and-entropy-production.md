# Peaked dwell times require cycles and entropy production

**Setting.** As for dwell times in a coarse-grained Markov chain: microstates with rates $w_{ij}$, an observed mesostate $A$ (two ON microstates in the minimal model) and the dwell-time density $f$ of sojourns in $A$. For a cycle $\mathcal C = (i_1 \to i_2 \to \dots \to i_L \to i_1)$ of the transition graph, the steady-state entropy produced per completion of the cycle in the forward direction is

$$\Delta_{\mathcal C} s = k_B \ln \frac{w_{i_1 i_2} w_{i_2 i_3} \cdots w_{i_L i_1}}{w_{i_2 i_1} w_{i_3 i_2} \cdots w_{i_1 i_L}},$$

and for a graph with a single cycle the entropy production rate is $\sigma = J\, \Delta_{\mathcal C} s$, where $J$ is the net stationary probability current around the cycle (Schnakenberg).

**Statements.**

1. *Trees are reversible.* If the transition graph (with every edge present in both directions) has no cycles other than back-and-forth pairs, the stationary law satisfies detailed balance. Hence, by the equilibrium monotonicity theorem, a peaked dwell-time density cannot arise on such a graph; for three strongly connected microstates a peaked density requires the cyclic graph $1 \to 2 \to 3 \to 1$.
2. *Cycle criterion.* On a single cycle, detailed balance holds iff $\Delta_{\mathcal C} s = 0$ (Kolmogorov's criterion), so a peaked density requires $\Delta_{\mathcal C} s \ne 0$ and $\sigma > 0$.
3. *Maximal peaking.* In the three-state clock model with ON $= \{1, 2\}$ and OFF $= \{3\}$, a biexponential density $f(t) = c_1 e^{\lambda_1 t} + c_2 e^{\lambda_2 t}$ ($\lambda_{1,2} < 0$) with $f(0) = c_1 + c_2 = 0$ (maximally peaked) is attained only in the limit where ON is entered exclusively through one microstate and left exclusively through the other, i.e. the reverse rates on the cycle vanish and $\Delta_{\mathcal C} s \to \infty$. As the reverse rates increase toward their detailed-balance values, $f(0)$ increases and the density becomes monotone at equilibrium.

## Expansion

For statement 1, on a tree the stationary law can be built edge by edge from $\pi_j = \pi_i w_{ij}/w_{ji}$, which is consistent because there is a unique path between any two states, and it solves the balance equations edge by edge. Statement 2 is Kolmogorov's criterion for a single cycle: $\pi_i w_{ij} = \pi_j w_{ji}$ around the cycle forces the ratio of forward to backward rate products to be $1$. For statement 3, $f(0)$ equals the stationary-weighted exit rate at the entry microstates; if every entry is into microstate $1$ and every exit is from microstate $2$, then $f(0) = 0$ and the density must first rise, which needs the forward cycle $3 \to 1 \to 2 \to 3$ to dominate its reverse. The PHO5 ON and OFF periods were both best fit with $f(0) = 0$, so entry into and exit from each state are effectively forward paths of different reactions; the inferred net current runs in one direction around cycles involving the activator Pho4 and the ATP-dependent chromatin remodelers Chd1 and Isw2, consistent with kinetic proofreading of activator identity.

## Depends on

- [Monotone dwell-time densities under detailed balance](monotone-dwell-time-densities-under-detailed-balance.md)

## Sources

- R. Shelansky, S. Abrahamsson, C. R. Brown, M. Doody, T. L. Lenstra, D. R. Larson, H. Boeger, "Single gene analysis in yeast suggests nonequilibrium regulatory dynamics for transcription", Nature Communications 15 (2024), 6226, Results ("The observed process is irreversible", Fig. 3 and its legend, Eq. (11)) and Supplementary Information (Theorems 1–3), <https://doi.org/10.1038/s41467-024-50419-5> (PMC11266658).
- J. Schnakenberg, "Network theory of microscopic and macroscopic behavior of master equation systems", Reviews of Modern Physics 48 (1976), 571–585, <https://doi.org/10.1103/RevModPhys.48.571>.
