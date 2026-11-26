# Boolean functions with all Fourier weight at degree one are the literals

For $f : \{-1,1\}^n \to \{-1,1\}$, $\mathbf{W}^1[f] = 1$ if and only if $f = \pm\chi_{\{i\}}$ for some coordinate $i$ (a literal $x_i$ or $-x_i$).

## Proof sketch

If $\mathbf{W}^1[f] = 1$ then $f = \sum_i \hat f(i) x_i$ is a linear form taking only values $\pm1$. Flipping one coordinate changes $f$ by $\pm 2\hat f(i) \in \{0, \pm 2\}$, so each $\hat f(i) \in \{0, \pm1\}$, and $\sum_i \hat f(i)^2 = 1$ leaves one nonzero coefficient.

## Depends on

- [Fourier weight at each degree](fourier-weight-at-each-degree.md)

## Proof depends on

- [Parseval's identity on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/expect-sq-eq-sum-bool-fourier-coeff-sq.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
