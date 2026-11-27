# A direction is unate exactly when its influence equals the absolute value of its degree-one coefficient

For every $f : \{-1,1\}^n \to \{-1,1\}$ and coordinate $i$, $|\hat f(\{i\})| \le \mathbf{Inf}_i[f]$, with equality if and only if $f$ is unate in direction $i$ (flipping $x_i$ from $1$ to $-1$ never decreases $f$ at any point, or never increases it). In particular for monotone $f$, $\mathbf{Inf}_i[f] = \hat f(\{i\})$.

## Proof sketch

$\hat f(\{i\}) = \mathbb{E}[D_i f]$ and $\mathbf{Inf}_i[f] = \mathbb{E}[|D_i f|]$ for the derivative $D_i f \in \{0, \pm 1\}$; equality in $|\mathbb{E}[D_i f]| \le \mathbb{E}|D_i f|$ holds iff $D_i f$ has constant sign.

## Depends on

- [Influence of a coordinate](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-influence.md)
- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)
- [Unate Boolean function](../unate-and-monotone-boolean-functions/is-unate-bool-fun.md)

## Proof depends on

- [Fourier formula for influence](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-influence-eq-sum-sq.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
