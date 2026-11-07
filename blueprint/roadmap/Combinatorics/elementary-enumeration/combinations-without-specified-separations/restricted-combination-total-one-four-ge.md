# Generating function for subsets avoiding differences 1 and 4

Let $S^{\{1,4\}}_n$ be the
number of subsets of $\{1, \dots, n\}$ in which no two elements differ by $1$ or by $4$. Then,
in the ring $\mathbb{Z}[[x]]$ of formal power series,

$$\Bigl(\sum_{n \ge 0} S^{\{1,4\}}_n x^n\Bigr)(1 - x - x^3 + x^4 - 2x^5 + x^6 - x^7) =
1 + x + x^2 + x^3 + 2x^4 + x^6.$$

This is the paper's formula for $\sum_{n \ge 0} S^{\{1,4\}}_n x^n$ as a quotient of the two
polynomials, with the denominator cleared.

## Sources

- Michael A. Allen, *Connections Between Combinations Without Specified Separations and Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer Sequences 28 (2025), Article 25.3.7, Proposition 9.
