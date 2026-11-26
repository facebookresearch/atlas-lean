# Stable influence and total stable influence

For a real $f$ on $\{-1,1\}^n$, a coordinate $i$ and $\rho \in [0, 1]$, the *$\rho$-stable influence* is

$$\mathbf{Inf}^{(\rho)}_i[f] = \mathrm{Stab}_\rho[D_i f] = \sum_{S \ni i}\rho^{|S| - 1}\hat f(S)^2,$$

where $D_i f$ is the $i$-th derivative, and the *total stable influence* is $\mathbf{I}^{(\rho)}[f] = \sum_i \mathbf{Inf}^{(\rho)}_i[f] = \sum_S |S|\rho^{|S|-1}\hat f(S)^2$. At $\rho = 1$ these are the ordinary influences. For $\rho < 1$ the total stable influence is at most $\mathrm{Var}[f]\max_k k\rho^{k-1}$, so only boundedly many coordinates can have large stable influence, which makes stable influences central to invariance-based hardness results.

## Depends on

- [Influence of a coordinate](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-influence.md)
- [Noise stability on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
