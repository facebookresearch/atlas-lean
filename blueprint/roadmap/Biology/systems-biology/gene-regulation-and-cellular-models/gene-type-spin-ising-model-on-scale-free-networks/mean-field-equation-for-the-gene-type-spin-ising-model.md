# Mean-field equation for the gene-type spin Ising model on Barabási–Albert networks

**Model.** Genes sit on the $N$ nodes of a Barabási–Albert network grown with $m$ links per new node (adjacency $A_{ij}$, degrees $k_i$, $\sum_i k_i \approx 2mN$). Each gene is inactive or active, $s_i \in \{0, 1\}$ ("gene-type" spins), with Hamiltonian

$$H_{0,1} = -\frac12\sum_{i,j} J A_{ij}\,s_is_j - h\sum_i s_i,$$

coupling $J$ (gene–gene interaction) and field $h$ (interaction with the environment), at temperature $T = 1/\beta$. The order parameter is the fraction of active genes $M = \frac1N\sum_i s_i$.

**Mean-field equation.** Neglecting products of fluctuations $(s_i - M)(s_j - M)$ and replacing $A_{ij}$ by its annealed Barabási–Albert average $\langle A_{ij}\rangle = k_ik_j/(2mN)$ decouples the spins into independent spins in local fields $h + JMk_i$, giving the self-consistency equation

$$M = \frac1N\sum_{i=1}^N \frac{1}{1 + e^{-\beta(h + JMk_i)}},$$

with $J \to -J$ for antiferromagnetic coupling. At $h = 0$: $M \to 1/2$ as $T \to \infty$, while $M \to 1$ (ferromagnetic) or $M \to 0$ (antiferromagnetic) as $T \to 0$.

**Low-temperature transition.** As $T \to 0$ the solution $M = 0$ is self-consistent iff $h < 0$ and $M = 1$ iff $h + Jk_i > 0$ for all $i$, i.e. $h > -Jm$ since the minimum degree is $m$. For $J > 0$ both states coexist for $-Jm < h < 0$, so the active fraction jumps discontinuously with hysteresis, and the critical field scales linearly with $J$ and $m$, $|h_c| = Jm$ ($h_c \approx 5$ for $J = 1$, $m = 5$), independent of $N$ at this order.

**Relation to the classical Ising model.** With $\sigma_i = 2s_i - 1 \in \{-1, 1\}$,

$$H_{0,1} = -\frac12\sum_{i,j}\frac{J A_{ij}}{4}\sigma_i\sigma_j - \sum_i\Big(\frac h2 + \frac{Jk_i}{4}\Big)\sigma_i - \Big(\frac{J}{8}\sum_{i,j}A_{ij} + \frac{hN}{2}\Big),$$

a classical Ising model with coupling $J/4$ and a degree-dependent intrinsic field $Jk_i/4$; the asymmetry of gene-type spins acts as an internal magnetic field even when $h = 0$.

## Expansion

In the mean-field Hamiltonian $\langle H_{\mathrm{MF}}\rangle = JM^2mN - \sum_i(h + JMk_i)s_i$, the partition function factorizes as $e^{-\beta JM^2 mN}\prod_i(1 + e^{\beta(h + JMk_i)})$, and $M = (N\beta)^{-1}\partial_h \ln Z$ gives the logistic average. Hubs feel the strongest field, so in a scale-free network the lowest-degree nodes set the edge of the bistable window. Monte Carlo heat-bath simulations with $N = 5000$ show the discontinuity and a nearly rectangular hysteresis loop, with a weak finite-size dependence of $h_c$ that the mean-field approximation misses; the mean-field theory overestimates the dependence on $J$ and $m$. Biologically, the active (above $h_c$) and inactive states are read as healthy and diseased network states.

## Sources

- J. Krishnan, R. Torabi, A. Schuppert, E. Di Napoli, "A modified Ising model of Barabási–Albert network with gene-type spins", Journal of Mathematical Biology 81 (2020) 769–798, equations (1)–(3), Theorem 1 with equations (4)–(18), and Theorem 2 with equations (19)–(24), <https://doi.org/10.1007/s00285-020-01518-6>, PMCID: PMC7519008.
