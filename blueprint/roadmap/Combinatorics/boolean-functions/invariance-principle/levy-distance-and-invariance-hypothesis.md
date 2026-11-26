# Lévy distance and the hypothesis of the basic invariance principle

For real random variables $X, Y$ the *Lévy distance* is the least $\varepsilon \ge 0$ such that $\Pr[X \le u - \varepsilon] - \varepsilon \le \Pr[Y \le u] \le \Pr[X \le u + \varepsilon] + \varepsilon$ for all $u$. A family of real random variables satisfies the *invariance hypothesis* (Hypothesis 11.65 in O'Donnell) if each has mean $0$, variance $1$, third moment $0$ and fourth moment at most $9$; uniform $\pm1$ bits and standard Gaussians satisfy it. For a formal multilinear polynomial $Q(z) = \sum_{S} c_S \prod_{i \in S} z_i$, the influence of coordinate $i$ is $\mathrm{Inf}_i[Q] = \sum_{S \ni i} c_S^2$ and its variance is $\sum_{S \ne \emptyset} c_S^2$.

## Depends on

- [Influence of a coordinate](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-influence.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
