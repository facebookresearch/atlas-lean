# Level structure of majority: complementary levels and monotone decrease

Let $n = 2m + 1$. (1) Coefficients on sets $S, T$ with $|S| + |T| = n + 1$ agree up to the sign $(-1)^m$, and for odd $k \le n$, $(n - k + 1)\,\mathbf{W}^{n - k + 1}[\mathrm{Maj}_n] = k\,\mathbf{W}^{k}[\mathrm{Maj}_n]$. (2) For odd $k \le n$, $\mathbf{W}^k[\mathrm{Maj}_{n+2}] < \mathbf{W}^k[\mathrm{Maj}_n]$. (3) Every coefficient is at most the singleton coefficient in absolute value, and $|\widehat{\mathrm{Maj}_n}(S)| \ge |\widehat{\mathrm{Maj}_n}(T)|$ for odd $|S| \le |T| \le m + 2$. (4) For $0 < \rho < 1$, $\mathrm{Stab}_\rho[\mathrm{Maj}_{n+2}] < \mathrm{Stab}_\rho[\mathrm{Maj}_n]$.

## Proof sketch

All four follow from the closed form of the coefficients by comparing ratios of binomial coefficients; (4) follows from (2) through the level formula for noise stability.

## Depends on

- [Majority function](../majority-is-least-stable-conjecture/majority.md)
- [Fourier weight at each degree](../fourier-expansion-supplements/fourier-weight-at-each-degree.md)
- [Noise stability on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab.md)

## Proof depends on

- [The Fourier coefficients of majority](fourier-coefficients-of-majority.md)
- [Fourier formula for noise stability](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab-eq-sum.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
