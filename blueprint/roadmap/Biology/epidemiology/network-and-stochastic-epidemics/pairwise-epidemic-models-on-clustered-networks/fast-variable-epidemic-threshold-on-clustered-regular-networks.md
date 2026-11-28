# Fast-variable epidemic threshold on clustered regular networks

**Pairwise model.** SIR spreads on a regular network of $N$ nodes and degree $n$ with per-link transmission rate $\tau$ and recovery rate $\gamma$; $\phi \in [0,1)$ is the global clustering coefficient (fraction of closed triples). Singles $[A]$, pairs $[AB]$ and triples $[ABC]$ denote expected counts. The pair equations require triples $[ASI]$, closed by Keeling's clustered closure

$$[ASI] = \frac{n-1}{n}\,\frac{[AS][SI]}{[S]}\Big( (1 - \phi) + \phi\, \frac{N [AI]}{n [A][I]} \Big),$$

which mixes the independent-neighbor closure with a correction by the correlation factor $C_{AI} = N[AI]/(n[A][I])$ on closed triangles. Correlations of the exact process satisfy $C_{SI} \le 1$, $C_{II} \ge 1$, $C_{SS} \ge 1$.

**Fast variables.** With $\xi = (n-1)/n$, the ratios $\alpha = [SI]/[I]$ (susceptible neighbors per infected node) and $\delta = [II]/[I]$ relax quickly to a quasi-equilibrium during the early epidemic, where $[S] \approx N$, and satisfy

$$\dot\alpha = -\tau\alpha + \tau\xi n (1 - \phi)\alpha + \tau\xi\phi\alpha^2 - \tau\xi \tfrac1n \phi \alpha^2 \delta - \tau\alpha^2, \qquad \dot\delta = 2\tau\alpha - \gamma\delta + 2\tau\xi\tfrac1n\phi\alpha^2\delta - \tau\alpha\delta .$$

The epidemic threshold is the growth-rate-based quantity $R = \tau \alpha^\ast/\gamma$, with $\alpha^\ast$ the quasi-equilibrium; $R = 1$ exactly when $R_0 = 1$.

**Results.**
1. Without clustering ($\phi = 0$): $(\alpha^\ast, \delta^\ast) = \big(n-2,\ 2\tau(n-2)/(\gamma + \tau(n-2))\big)$, so $R = \tau(n-2)/\gamma$.
2. With clustering, a unique biologically meaningful steady state in $D = \{0 \le \alpha \le n,\ 0 \le \delta \le n - \alpha\}$ exists provided $\phi < (n-2)/(n-1)$; for larger $\phi$ the disease dies out. $\alpha^\ast$ is the admissible root of the cubic

$$2\tau\xi\phi(1 - \xi\phi)\alpha^3 + \big(\tau\xi n\phi - 2\tau\xi^2 n\phi(1-\phi) - \tau n\big)\alpha^2 + \big(-n(\tau+\gamma) + \tau\xi n^2(1-\phi) + \gamma\xi n\phi\big)\alpha + \gamma\xi n^2(1-\phi) - \gamma n = 0,$$

with $\alpha^\ast = (n-2) + O(\phi)$.
3. By the Bendixson criterion the steady state is globally stable in $D$ if $\phi < 2n/(3(n-1))$, which covers all admissible $\phi$ when $n < 6$.

Clustering lowers $\alpha^\ast$ and therefore shifts the threshold $R_c = 1$ to larger $\tau$ and $n$.

## Expansion

Dividing the pair equations by $[I]$ and using the closure turns the unclosed hierarchy into a planar system for $(\alpha,\delta)$, whose time scale is set by $\tau$ and $\gamma$ rather than by the slow depletion of susceptibles. The $\alpha$-nullcline is a decreasing curve $\delta_1(\alpha)$ when $\xi n(1-\phi) > 1$ and the $\delta$-nullcline is increasing, so they cross once in $D$ under the stated clustering bound, and the boundary of $D$ is inflowing. The divergence of the vector field after division by $\alpha$ is $-2\tau - \gamma/\alpha + \phi\tau\xi(n - \delta + 2\alpha)/n$, which is negative on $D$ under the stated bound, excluding periodic orbits. Setting $\dot\alpha = 0$, solving for $\delta$ and substituting into $\dot\delta = 0$ gives the cubic, and a regular perturbation in $\phi$ around the root $n - 2$ gives explicit corrections. A modified closure that renormalizes the clustered neighbor-state probabilities so that they sum to one conserves link counts and gives a different, closure-dependent threshold.

## Sources

- R. C. Barnard, L. Berthouze, P. L. Simon, I. Z. Kiss, "Epidemic threshold in pairwise models for clustered networks: closures and fast correlations", Journal of Mathematical Biology 79(3) (2019) 823, Equations (3.1)-(3.10), (4.11)-(4.24), Propositions 1-2, <https://doi.org/10.1007/s00285-019-01380-1>, PMCID PMC6667428.
