# Invasion threshold and bistability in the aggregated coinfection model

**System.** Consider the aggregated primary-disease system with demography and stage-dependent competition

$$
\begin{aligned}
\frac{dS}{dt} &= rS + \bar a rI - mS - (c_{SS}S+\bar c_{SI}I)S - \bar\beta SI + \bar\gamma I,\\
\frac{dI}{dt} &= -mI - (\bar c_{IS}S+\bar c_{II}I)I + \bar\beta SI - \bar\gamma I - \bar\mu I,
\end{aligned}
$$

with nonnegative parameters, $c_{SS},\bar c_{II}>0$. Define the disease-free carrying capacity, the invasion threshold and the facilitation threshold

$$
S_1^* = \frac{r-m}{c_{SS}},\qquad \bar A = \frac{m+\bar\gamma+\bar\mu}{\bar\beta-\bar c_{IS}},\qquad \bar B = \frac{\bar a r+\bar\gamma}{\bar c_{SI}+\bar\beta}.
$$

**Theorem.**

1. If $r\le m$, every nonnegative solution tends to $(0,0)$. If $r>m$, solutions are bounded and $E_1^*=(S_1^*,0)$ is the disease-free equilibrium; it is a saddle if $S_1^*(\bar\beta-\bar c_{IS})>m+\bar\gamma+\bar\mu$ and locally asymptotically stable if the reverse strict inequality holds; if $\bar\beta\le\bar c_{IS}$ it attracts all of $\mathbb R_+^2\setminus\{0\}$.

Assume now $r>m$ and $\bar\beta>\bar c_{IS}$.

2. *(Extinction.)* If $\bar A\ge\max\{S_1^*,\bar B\}$, $E_1^*$ is the unique nonnegative equilibrium besides the origin and attracts every positive solution.
3. *(Endemic invasion.)* If $S_1^*>\bar A$, there is a unique interior equilibrium $E_+^*$, which is locally asymptotically stable; if in addition $S_1^*<\bar B$, it attracts every positive solution.
4. *(Bistability without invasion.)* If $S_1^*<\bar A<\bar B$, $E_1^*$ is asymptotically stable. Let

$$
\mathcal R = \frac{\bar c_{II}(r-m) + (\bar ar+\bar\gamma)(\bar\beta-\bar c_{IS}) + (\bar c_{SI}+\bar\beta)(m+\bar\mu+\bar\gamma)}{2\sqrt{\big(c_{SS}\bar c_{II}+(\bar c_{SI}+\bar\beta)(\bar\beta-\bar c_{IS})\big)(\bar ar+\bar\gamma)(m+\bar\mu+\bar\gamma)}}.
$$

(Substituting the $I$-nullcline into the $S$-equation gives the quadratic $\big(c_{SS}\bar c_{II}+(\bar c_{SI}+\bar\beta)(\bar\beta-\bar c_{IS})\big)S^2-\big(\bar c_{II}(r-m)+(\bar ar+\bar\gamma)(\bar\beta-\bar c_{IS})+(\bar c_{SI}+\bar\beta)(m+\bar\mu+\bar\gamma)\big)S+(\bar ar+\bar\gamma)(m+\bar\mu+\bar\gamma)=0$ for interior equilibria, and $\mathcal R$ compares its discriminant with zero. The source's (12)–(14) drop $m$ from $m+\bar\mu+\bar\gamma$; with $r=2$, $m=1$, $c_{SS}=1$, $\bar c_{SI}=\bar c_{IS}=0$, $\bar c_{II}=\bar a=\bar\beta=\bar\gamma=1$, $\bar\mu=0$ the quadratic is $S^2-3S+3=0$, with no real root, and $\mathcal R=6/(2\sqrt{12})<1$ as written here.) If $\mathcal R<1$ there is no interior equilibrium and $E_1^*$ attracts $\mathbb R_+^2\setminus\{0\}$. If $\mathcal R=1$ there is a single, unstable interior equilibrium. If $\mathcal R>1$ there are two interior equilibria $E_{+1}^*<E_{+2}^*$ (componentwise), a saddle and a locally asymptotically stable node: the infection can persist even though it cannot invade the disease-free population.

## Expansion

Rewriting the system as $\dot S = c_{SS}S(S_1^*-S) + (\bar c_{SI}+\bar\beta)(\bar B-S)I$ and $\dot I = (\bar\beta-\bar c_{IS})(S-\bar A)I - \bar c_{II}I^2$ exposes the thresholds. $\bar A$ is the susceptible density needed for a few infecteds to spread, so $S_1^*>\bar A$ is the invasion condition. $\bar B$ separates susceptible densities at which infected hosts raise ($S<\bar B$, through their residual fertility $\bar ar$ and recovery $\bar\gamma$) or lower the susceptible growth rate. The $I$-nullcline is the line $I=\frac{\bar\beta-\bar c_{IS}}{\bar c_{II}}(S-\bar A)$ and the $S$-nullcline is $I=\frac{c_{SS}}{\bar c_{SI}+\bar\beta}\frac{S(S_1^*-S)}{S-\bar B}$; counting their intersections, combined with Poincaré–Bendixson arguments, gives the classification, and $\mathcal R=1$ is the tangency (saddle-node) condition in case 4. Through the aggregated coefficients, an opportunistic disease can move the primary disease between these regimes, for instance from extinction to bistable persistence.

## Depends on

- [Approximate aggregation of the primary–opportunistic coinfection model](approximate-aggregation-of-the-primary-opportunistic-coinfection-model.md)

## Sources

- M. Marvá, E. Venturino, R. Bravo de la Parra, *A time scales approach to coinfection by opportunistic diseases*, arXiv:1403.3517 (2014). <https://doi.org/10.48550/arXiv.1403.3517> — Section 3: Propositions 1–6 (extinction, boundedness, disease-free equilibrium, global extinction, endemic equilibrium, bistability). Published version: Journal of Applied Mathematics 2015 (2015), 1–10, <https://doi.org/10.1155/2015/275485>; locators above refer to the arXiv version.
