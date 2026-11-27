# Coalitional influence

For $f : \{-1,1\}^n \to \{-1,1\}$, a coalition $J \subseteq [n]$ and an outcome $b \in \{-1,1\}$, the *coalitional influence of $J$ toward $b$* is

$$\widetilde{\mathbf{Inf}}^{\,b}_J[f] = \Pr_z\big[\exists y \in \{-1,1\}^J : f(y, z) = b\big] - \Pr[f = b],$$

where $z$ is a uniform assignment to the coordinates outside $J$, and the *coalitional influence* is $\widetilde{\mathbf{Inf}}_J[f] = \Pr_z[f(\cdot, z) \text{ is not constant}]$. Then $\widetilde{\mathbf{Inf}}_J = \widetilde{\mathbf{Inf}}^{\,1}_J + \widetilde{\mathbf{Inf}}^{\,-1}_J$, $0 \le \widetilde{\mathbf{Inf}}^{\,b}_J \le 1$, a single voter has $\widetilde{\mathbf{Inf}}^{\,b}_{\{i\}} = \mathbf{Inf}_i/2$, for monotone $f$ the coalition's best strategy is to vote $b$ unanimously, and every nonempty coalition has coalitional influence $1$ on the parity of all coordinates.

## Depends on

- [Influence of a coordinate](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-influence.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
