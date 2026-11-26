# Noise sensitivity

For $f : \{-1,1\}^n \to \{-1,1\}$ and $\delta \in [0, 1]$, the *noise sensitivity* at noise rate $\delta$ is $\mathrm{NS}_\delta[f] = \Pr[f(x) \ne f(y)]$, where $x$ is uniform and $y$ is obtained from $x$ by flipping each coordinate independently with probability $\delta$. In terms of noise stability, $\mathrm{NS}_\delta[f] = \frac12 - \frac12\mathrm{Stab}_{1 - 2\delta}[f] = \frac12\sum_S\big(1 - (1-2\delta)^{|S|}\big)\hat f(S)^2$. A class of functions is *uniformly noise-stable* if there is $\varepsilon(\delta) \to 0$ as $\delta \to 0^+$ with $\mathrm{NS}_\delta[f] \le \varepsilon(\delta)$ for all members.

## Depends on

- [Noise stability on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab.md)
- [Fourier formula for noise stability](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab-eq-sum.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
