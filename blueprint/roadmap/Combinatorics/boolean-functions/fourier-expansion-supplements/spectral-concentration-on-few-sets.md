# Small spectral norm gives concentration on few sets, and concentration survives approximation

For real functions $f, g$ on $\{-1,1\}^n$: (1) for every $\varepsilon > 0$, $f$ is $\varepsilon$-concentrated (Fourier weight at most $\varepsilon$ outside) on a collection of at most $\|\hat f\|_1^2/\varepsilon$ sets: if $\|\hat f\|_1 > 0$, those with $|\hat f(S)| \ge \varepsilon/\|\hat f\|_1$, and if $f = 0$, the empty collection; (2) for every collection $\mathcal{T}$ of sets, $\sum_{S \in \mathcal{T}} \hat g(S)^2 \le 2\big(\sum_{S \in \mathcal{T}}\hat f(S)^2 + \mathbb{E}[(f - g)^2]\big)$. Hence if $f$ is $\varepsilon_1$-concentrated on $\mathcal{F}$ and $\|f - g\|_2^2 \le \varepsilon_2$ then $g$ is $2(\varepsilon_1 + \varepsilon_2)$-concentrated on $\mathcal{F}$.

## Proof sketch

(1) For $f = 0$ there is nothing to prove. Otherwise the weight on small coefficients is at most $\max_{\text{small}}|\hat f(S)| \cdot \|\hat f\|_1 \le \varepsilon$, and there are at most $\|\hat f\|_1^2/\varepsilon$ large ones. (2) $(a + b)^2 \le 2a^2 + 2b^2$ coefficientwise and Parseval for $f - g$.

## Depends on

- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)
- [Fourier weight at each degree](fourier-weight-at-each-degree.md)

## Proof depends on

- [Parseval's identity on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/expect-sq-eq-sum-bool-fourier-coeff-sq.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
- E. Kushilevitz and Y. Mansour, "Learning Decision Trees Using the Fourier Spectrum", SIAM Journal on Computing 22(6), 1993.
