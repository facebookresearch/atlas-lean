# The Fourier coefficients of majority

Let $n = 2m + 1$ and $\mathrm{Maj}_n(x) = \mathrm{sgn}(x_1 + \dots + x_n)$. Then $\widehat{\mathrm{Maj}_n}(S) = 0$ for $|S|$ even, and for $|S| = 2j + 1$,

$$\widehat{\mathrm{Maj}_n}(S) = (-1)^j \frac{\binom{m}{j}}{\binom{2m}{2j}} \cdot \frac{\binom{2m}{m}}{4^m}.$$

In particular $\widehat{\mathrm{Maj}_n}(\{i\}) = \binom{2m}{m}4^{-m} \sim \sqrt{2/(\pi n)}$.

## Proof sketch

Majority is odd, so even coefficients vanish, and symmetric, so coefficients depend only on $|S|$. The coefficient on $S$ is $\mathbb{E}[D_i\mathrm{Maj} \cdot \chi_{S \setminus\{i\}}]$ for $i \in S$; the derivative is the indicator that the other $2m$ bits are balanced, and summing $\chi$ over balanced strings is a Krawtchouk-polynomial evaluation that gives the closed form.

## Depends on

- [Majority function](../majority-is-least-stable-conjecture/majority.md)
- [Fourier coefficient on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/bool-fourier-coeff.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
