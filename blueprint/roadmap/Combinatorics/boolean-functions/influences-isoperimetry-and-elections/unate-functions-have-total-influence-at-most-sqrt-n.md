# Unate functions have total influence at most √(n·Var)

If $f : \{-1,1\}^n \to \{-1,1\}$ is unate, then $\mathbf{I}[f] \le \sqrt{n\,\mathrm{Var}[f]} \le \sqrt n$. In particular monotone, antitone and linear threshold functions have total influence at most $\sqrt n$, and majority attains $\sqrt{2/\pi}\sqrt n + O(n^{-1/2})$.

## Proof sketch

By unateness $\mathbf{I}[f] = \sum_i |\hat f(\{i\})|$; Cauchy–Schwarz gives $\sum_i |\hat f(\{i\})| \le \sqrt{n \sum_i \hat f(\{i\})^2} \le \sqrt{n \mathrm{Var}[f]}$ by Parseval.

## Depends on

- [Total influence on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-total-influence.md)
- [Variance on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-variance.md)
- [Unate Boolean function](../unate-and-monotone-boolean-functions/is-unate-bool-fun.md)
- [Linear threshold function](../majority-is-least-stable-conjecture/is-linear-threshold-function.md)
- [Majority function](../majority-is-least-stable-conjecture/majority.md)

## Proof depends on

- [Linear threshold functions are unate](linear-threshold-functions-are-unate.md)
- [A direction is unate exactly when its influence equals the absolute value of its degree-one coefficient](unate-direction-influence-equals-coefficient.md)
- [Parseval's identity on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/expect-sq-eq-sum-bool-fourier-coeff-sq.md)
- [Majority maximizes the sum of degree-one Fourier coefficients](majority-maximizes-sum-of-degree-one-coefficients.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
