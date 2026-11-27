# Ensemble epistasis between mutations that are additive within each conformation

Take the three-conformation model of the [Boltzmann-averaged free energy](boltzmann-averaged-free-energy-of-a-conformational-ensemble.md): $\Delta G_{\mathrm{obs}} = G_i - \langle G_{j,k}\rangle$. Mutation $a\to A$ shifts conformation $c \in \{i,j,k\}$ by $\delta G_c^{a\to A}$ and $b \to B$ by $\delta G_c^{b\to B}$, and the mutations are additive within each conformation: $G_c^{AB} = G_c^{ab} + \delta G_c^{a\to A} + \delta G_c^{b\to B}$, and likewise for $Ab$, $aB$. Epistasis is

$$\varepsilon = (\Delta G_{\mathrm{obs}}^{AB} - \Delta G_{\mathrm{obs}}^{aB}) - (\Delta G_{\mathrm{obs}}^{Ab} - \Delta G_{\mathrm{obs}}^{ab}).$$

**Equation (16) (Morrison, Wheeler and Harms).**

$$\varepsilon = -\big[(\langle G_{j,k}^{AB}\rangle - \langle G_{j,k}^{aB}\rangle) - (\langle G_{j,k}^{Ab}\rangle - \langle G_{j,k}^{ab}\rangle)\big],$$

so every term involving the active conformation $i$ cancels. For two sub-ensembles $X$ and $Y$ (equation (19)), $\varepsilon$ is the double difference of $\langle G_X\rangle$ minus that of $\langle G_Y\rangle$.

**Characterization (a consequence of equation (16)).** Let $d = G_j^{ab} - G_k^{ab}$, $\alpha = \delta G_j^{a\to A} - \delta G_k^{a\to A}$ and $\beta = \delta G_j^{b\to B} - \delta G_k^{b\to B}$. Then

1. $\varepsilon = 0$ if and only if $\alpha = 0$ or $\beta = 0$;
2. $\operatorname{sign}(\varepsilon) = \operatorname{sign}(\alpha\beta)$;
3. $|\varepsilon| < \min(|\alpha|, |\beta|)$ whenever $\varepsilon \ne 0$.

So ensemble epistasis requires both mutations to act differently on the two inactive conformations. It is positive when both shift the balance the same way (the paper's magnitude region) and negative when each favors a different conformation (the sign region). It vanishes in the limits where one inactive conformation carries essentially all of the weight, since then the populations do not redistribute. Unlike threshold epistasis, it cannot be removed by moving to the free-energy scale, because both observable and mutational effects already live there.

## Depends on

- [Boltzmann-averaged free energy of a conformational ensemble](boltzmann-averaged-free-energy-of-a-conformational-ensemble.md)
- [Reciprocal sign epistasis, multiple peaks and the small-face limitation](epistasis-and-landscape-structure.md)

## Proof depends on

- [Boltzmann-averaged free energy of a conformational ensemble](boltzmann-averaged-free-energy-of-a-conformational-ensemble.md)

## Expansion

Substituting $\Delta G_{\mathrm{obs}} = G_i - \langle G_{j,k}\rangle$ into $\varepsilon$, the $G_i$ parts form a double difference of an additive function and cancel, giving equation (16). By shift equivariance, $\langle G_{j,k}\rangle = G_k + h(G_j - G_k)$ with $h(u) = -RT\ln(1 + e^{-u/RT})$, and the $G_k$ parts cancel too, leaving

$$\varepsilon = -\big[h(d+\alpha+\beta) - h(d+\beta) - h(d+\alpha) + h(d)\big] = -\int_0^\alpha\!\!\int_0^\beta h''(d+s+t)\,dt\,ds.$$

Here $h'(u) = 1/(1+e^{u/RT}) \in (0,1)$ is strictly decreasing, so $h'' < 0$, which gives items 1 and 2. For item 3, each of $h(d+\beta+\alpha) - h(d+\beta)$ and $h(d+\alpha) - h(d)$ lies strictly between $0$ and $\alpha$, so their difference is smaller than $|\alpha|$ in absolute value; the same holds with $\alpha$ and $\beta$ exchanged. As $|d| \to \infty$, $h''(d + \cdot) \to 0$ uniformly on bounded sets, so $\varepsilon \to 0$.

## Sources

- A. M. Morrison, L. C. Wheeler and M. J. Harms, *Ensemble epistasis: thermodynamic origins of nonadditivity between mutations*, Genetics 219 (2021), iyab105. <https://doi.org/10.1093/genetics/iyab105>. PMCID: PMC8633102. Equations (11)–(16) and (19); sections "Conditions necessary for ensemble epistasis" and "Ensembles can lead to magnitude epistasis, sign-epistasis, and reciprocal sign-epistasis".
