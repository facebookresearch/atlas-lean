# Closeness testing by collision statistics and flattening

For two unknown distributions $p, q$ on $n$ points, the statistic $Z = C_1 + C_2 - \frac{k-1}{k} C_3$, where $C_1, C_2$ count collisions within $k$ samples from $p$ and from $q$ and $C_3$ counts cross collisions, is an unbiased estimator of $\binom{k}{2}\|p - q\|_2^2$. Thresholding $Z$ gives a closeness tester; combined with *flattening* (splitting each domain element into several copies according to the multiplicities in a first batch of samples, which makes both collision probabilities small) it uses

$$O\big(n^{2/3}\varepsilon^{-4/3} + \sqrt n\, \varepsilon^{-2}\big)$$

samples, which is optimal up to constants (Chan–Diakonikolas–Valiant–Valiant).

## Proof sketch

Compute the mean and variance of $Z$ in terms of $\|p\|_2, \|q\|_2$ and $\|p - q\|_2$; flattening with $m$ extra samples reduces $\|p\|_2^2, \|q\|_2^2$ to $O(1/m)$ in expectation without changing $\|p - q\|_1$, and balancing $m$ against the $\ell_2$ tester's sample count gives the bound.

## Depends on

- [Sample-based distribution testers](sample-based-distribution-testers.md)

## Proof depends on

- [The collision tester for uniformity](collision-tester-for-uniformity.md)

## Sources

- T. Batu, L. Fortnow, R. Rubinfeld, W. D. Smith and P. White, "Testing Closeness of Discrete Distributions", Journal of the ACM 60(1), 2013.
- I. Diakonikolas, T. Gouleakis, J. Peebles and E. Price, "Collision-Based Testers are Optimal for Uniformity and Closeness", Chicago Journal of Theoretical Computer Science 2019.
- I. Diakonikolas and D. M. Kane, "A New Approach for Testing Properties of Discrete Distributions", FOCS 2016.
- C. L. Canonne, "A Survey on Distribution Testing: Your Data is Big. But is it Blue?", Theory of Computing Graduate Surveys 9, 2020.
