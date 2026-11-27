# Manacher's algorithm computes all palindromic radii in linear time

**Manacher's algorithm** scans the centers left to right, maintaining the center $C$ whose maximal palindrome reaches furthest right, to position $R$. At a center $c < R$ it initializes the radius from the mirror center $2C - c$ as $\min(\mathrm{rad}(2C - c),\, R - c)$ (in the appropriate half-integer units) and extends by direct comparisons. It computes $\mathrm{rad}_w(c)$ for all $2n + 1$ centers and the span of a longest palindromic factor, and on the word RAM it runs in $O(n + 1)$ instructions.

## Proof sketch

Inside the current palindrome, the factor about $c$ mirrors the factor about $2C - c$, which justifies the initialization. Every successful comparison advances $R$, so there are at most $O(n)$ successful and $O(n)$ failing comparisons.

## Depends on

- [Maximal palindromic radii at all centers](maximal-palindromic-radii.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- G. Manacher, "A New Linear-Time On-Line Algorithm for Finding the Smallest Initial Palindrome of a String", Journal of the ACM 22(3), 1975.
- A. Apostolico, D. Breslauer and Z. Galil, "Parallel Detection of All Palindromes in a String", Theoretical Computer Science 141(1-2), 1995.
