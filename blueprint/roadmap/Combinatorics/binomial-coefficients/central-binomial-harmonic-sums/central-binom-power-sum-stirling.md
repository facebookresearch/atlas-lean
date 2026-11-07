# Central binomial power sums via Stirling numbers

For every natural number $m$ and every
real $x$ with $|x| < 1/4$,

$$\sum_{n=0}^{\infty} \binom{2n}{n} n^m x^n =
\frac{1}{\sqrt{1-4x}} \sum_{k=0}^{m} S(m,k) \binom{2k}{k}\, k! \left(\frac{x}{1-4x}\right)^k,$$

where $S(m,k)$ denotes the Stirling numbers of the second kind (and $n^0 = 1$ for every $n$).

The source asks for positive $m$; the identity also holds at $m = 0$, where both sides are the
generating function of the central binomial coefficients.

## Sources

- Khristo N. Boyadzhiev, "Series with Central Binomial Coefficients, Catalan Numbers, and Harmonic Numbers," Journal of Integer Sequences 15 (2012), Article 12.1.7, Theorem (label t3, equation 8), lines 155–160, https://cs.uwaterloo.ca/journals/JIS/VOL15/Boyadzhiev/boyadzhiev6.tex
