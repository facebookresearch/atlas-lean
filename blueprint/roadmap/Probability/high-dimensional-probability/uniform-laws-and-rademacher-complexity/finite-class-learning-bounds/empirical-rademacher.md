# Empirical Rademacher complexity of a finite set of vectors

For a finite set $A \subseteq \mathbb{R}^n$, the empirical Rademacher complexity is

$$\hat{\mathfrak R}(A) = \frac{1}{2^n}\sum_{\sigma \in \{\pm1\}^n}\max_{a \in A}\frac1n\sum_{i}\sigma_ia_i,$$

the average over all sign vectors of the largest normalized correlation (one-sided, with no absolute value); the empty set has complexity $0$ (and $0^{-1} = 0$). On finite sets it equals the [empirical Rademacher complexity of a set of vectors](../../../../ComputerScience/machine-learning/generalization-bounds-and-concentration/rademacher-complexity/rademacher-complexity.md), defined for arbitrary sets with a supremum.
