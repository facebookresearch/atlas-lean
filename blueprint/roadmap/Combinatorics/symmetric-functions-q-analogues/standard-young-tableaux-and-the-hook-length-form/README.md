# Standard Young tableaux and the hook length formula

A standard Young tableau of shape $\lambda \vdash n$ fills the Young diagram of $\lambda$ with
$1, \dots, n$, increasing along rows and down columns; $f^\lambda$ denotes their number. It is the
dimension of the irreducible representation of $\mathfrak S_n$ indexed by $\lambda$. Two classical
facts about it: the hook length formula $f^\lambda = n! / \prod_{u \in \lambda} h(u)$, and
$\sum_{\lambda \vdash n} (f^\lambda)^2 = n!$, which the Robinson–Schensted–Knuth (RSK) algorithm
proves bijectively by sending a permutation of $[n]$ to a pair of standard Young tableaux of the
same shape. Richard P. Stanley, *Topics in Algebraic Combinatorics* (author's draft of 1 February
2013), Chapter 8, develops both: Theorem 8.1 (hook length formula), Corollary 8.5, and Theorem 8.13
(RSK) in Appendix 1 to the chapter.

- [Straight shape as a skew shape](straight-shape.md)
- [Tableaux are determined by their entries](ext.md)
- [Number of standard Young tableaux](syt-count.md)
- [Hook length of a cell](hook-length.md)
- [Hook lengths are positive](hook-length-pos.md)
- [Hook length formula](syt-count-mul-prod-hook-length.md)
- [Sum of the squares of the numbers of standard Young tableaux](sum-syt-count-sq.md)

## Related topics

- [Symmetric functions and skew Young tableaux](../symmetric-functions-and-skew-young-tableaux/README.md):
  the definitions of skew shapes and of semistandard and standard Young tableaux used here.
