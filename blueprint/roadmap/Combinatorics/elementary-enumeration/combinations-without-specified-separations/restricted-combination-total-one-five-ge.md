# Generating function for subsets avoiding differences 1 and 5

Let $S^{\{1,5\}}_n$ be the
number of subsets of $\{1, \dots, n\}$ in which no two elements differ by $1$ or by $5$. Then,
in the ring $\mathbb{Z}[[x]]$ of formal power series,

$$\Bigl(\sum_{n \ge 0} S^{\{1,5\}}_n x^n\Bigr)
(1 - x^2 - x^3 - x^4 + x^5 - x^6 - x^7 - x^8 - x^{10}) =
1 + 2x + 2x^2 + 2x^3 + 2x^4 + 4x^5 + 3x^6 + 2x^7 + x^8 + x^9.$$

This is the paper's formula for $\sum_{n \ge 0} S^{\{1,5\}}_n x^n$ as a quotient of the two
polynomials, with the denominator cleared.

## Sources

- Michael A. Allen, *Connections Between Combinations Without Specified Separations and Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer Sequences 28 (2025), Article 25.3.7, Proposition 10.
