# Majority maximizes the sum of degree-one Fourier coefficients

For every $f : \{-1,1\}^n \to \{-1,1\}$, $\sum_{i=1}^n \hat f(\{i\}) = \mathbb{E}\big[f(x) \sum_i x_i\big] \le \mathbb{E}\big|\sum_i x_i\big|$, with equality iff $f(x) = \mathrm{sgn}(\sum_i x_i)$ wherever $\sum_i x_i \ne 0$, i.e. iff $f$ is a majority function (for odd $n$, exactly $\mathrm{Maj}_n$). Interpreted as voting, majority maximizes the expected number of voters who agree with the outcome. For odd $n$ the maximum is $n \binom{n-1}{(n-1)/2} 2^{1-n} \sim \sqrt{2n/\pi}$.

## Proof sketch

$f(x)\sum_i x_i \le |\sum_i x_i|$ pointwise, with equality iff $f(x)$ has the sign of the sum.

## Depends on

- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)
- [Majority function](../majority-is-least-stable-conjecture/majority.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
