# The spectral sample of a Boolean function

For $f : \{-1,1\}^n \to \{-1,1\}$, Parseval gives $\sum_S \hat f(S)^2 = 1$, so the squared Fourier coefficients form a probability distribution on subsets of $[n]$: the *spectral sample* $\mathscr{S}_f$ draws $S$ with probability $\hat f(S)^2$. Its size $|\mathscr{S}_f|$ equals $k$ with probability $\mathbf{W}^k[f]$, so $\mathbb{E}|\mathscr{S}_f| = \mathbf{I}[f]$ and $\Pr[i \in \mathscr{S}_f] = \mathbf{Inf}_i[f]$.

## Depends on

- [Fourier weight at each degree](fourier-weight-at-each-degree.md)
- [Parseval's identity on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/expect-sq-eq-sum-bool-fourier-coeff-sq.md)
- [Total influence on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence.md)
- [Influence of a coordinate](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-influence.md)

## Proof depends on

- [Total influence in Fourier form](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence-eq-sum-card-mul-sq.md)
- [Fourier formula for influence](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-influence-eq-sum-sq.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
