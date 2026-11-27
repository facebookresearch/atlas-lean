# Generating function for subsets avoiding differences 1 and 6

Let $S^{\{1,6\}}_n$ be the
number of subsets of $\{1, \dots, n\}$ in which no two elements differ by $1$ or by $6$. Then,
in the ring $\mathbb{Z}[[x]]$ of formal power series,

$$\Bigl(\sum_{n \ge 0} S^{\{1,6\}}_n x^n\Bigr)
(1 - x - x^4 - x^5 + 2x^6 - 4x^7 + 2x^8 - 2x^{10} + 2x^{11} - 4x^{12} + 3x^{13} - x^{14} +
2x^{16} - x^{17} + x^{18}) =
1 + x + x^2 + 2x^3 + 2x^4 + 2x^5 + 5x^6 + 3x^8 + 2x^9 - x^{10} + x^{11} - 4x^{12} - x^{13} -
2x^{14} - 2x^{15} - x^{17}.$$

This is the paper's formula for $\sum_{n \ge 0} S^{\{1,6\}}_n x^n$ as a quotient of a polynomial
of degree $17$ by a polynomial of degree $18$, with the denominator cleared.

## Sources

- Michael A. Allen, *Connections Between Combinations Without Specified Separations and Strongly Restricted Permutations, Compositions, and Bit Strings*, Journal of Integer Sequences 28 (2025), Article 25.3.7, Proposition 11.
