# Exactness of the pairwise closure on configuration-model networks

**Setting.** A Markovian SIR epidemic runs on a configuration-model network with $N$ nodes and degree PGF $\psi$; transmission occurs across each $S$–$I$ edge at rate $\beta$ and infectives recover at rate $\gamma$. Write $[A]$ for the number of nodes in state $A$, $[AB]$ for the number of (ordered) $A$–$B$ edges and $[ABC]$ for the number of connected $A$–$B$–$C$ triples. The (unclosed) pairwise equations are

$$\dot{[S]} = -\beta[SI], \qquad \dot{[SI]} = \beta([SSI] - [ISI]) - (\beta+\gamma)[SI], \qquad \dot{[SS]} = -2\beta[SSI],$$

and the closure under study, for $A \in \{S, I\}$, is

$$[ASI] \simeq \kappa\,\frac{[AS][SI]}{[S]}.$$

**Theorem.** Assume either $\psi(0) > 0$, $\psi'(0) > 0$ and $\psi''(1) < \infty$, or $\psi(u) = u^n$. The closure is exact, meaning both sides divided by $N$ agree as $N \to \infty$ (uniformly in probability on finite time intervals), if and only if the degree distribution is [Poisson-type](poisson-type-degree-distributions.md). In that case $\kappa = (n-1)/n$ for $\mathrm{Bin}(n,p)$ (including $n$-regular, and $\kappa = 0$ for $n = 1$, where there are no triples), $\kappa = 1$ for $\mathrm{Poi}(\lambda)$, and $\kappa = (r+1)/r$ for $\mathrm{NB}(r,p)$, and the closed pairwise system is equivalent to the edge-based (Volz) and dynamic survival analysis limits of the epidemic. Theorem 2 uses the family with $\kappa>0$ in (19); we include $\mathrm{Bin}(1,p)$ because degrees at most one give no connected triples, so $[ASI]\equiv0$ and the closure holds with $\kappa=0$.

## Depends on

- [Poisson-type degree distributions](poisson-type-degree-distributions.md)

## Expansion

Resolving triples by degree and using the configuration-model approximation $[A_jS_kI_\ell] \simeq (k-1)[A_jS_k][SI_\ell]/[S\bullet]$, with $[S\bullet] = [SS] + [SI]$, gives $[ASI] \simeq [AS][SI]\sum_k k(k-1)[S_k]/[S\bullet]^2$. If $\theta$ is the probability that infection has not crossed a random edge, then $[S_k] \simeq Np_k\theta^k$, so $[S] \simeq N\psi(\theta)$, $[S\bullet] \simeq N\theta\psi'(\theta)$ and $\sum_k k(k-1)[S_k] \simeq N\theta^2\psi''(\theta)$, whence

$$[ASI] \simeq \frac{\psi''(\theta)\psi(\theta)}{\psi'(\theta)^2}\,\frac{[AS][SI]}{[S]}.$$

The extra variable $\theta$ drops out exactly when $\psi''\psi/\psi'^2$ is constant, i.e. for PT laws. For these laws $\psi''(\theta)/\psi'(\theta)^2 = \kappa/x_S$ with $x_S = \psi(\theta)$, and substituting into the dynamic survival analysis equations reproduces the limiting closed pairwise equations term by term.

## Sources

- I. Z. Kiss, E. Kenah, G. A. Rempała, "Necessary and sufficient conditions for exact closures of epidemic equations on configuration model networks", Journal of Mathematical Biology (2023), Eqs. (4), (10)–(17), (24), Table 2, Theorem 2 and Lemma 1, <https://doi.org/10.1007/s00285-023-01967-9>, PMCID PMC10397147.
