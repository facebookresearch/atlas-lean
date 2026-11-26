# Interval evaluation is exact when each variable occurs once

Let $e$ be an arithmetic expression in variables $x_1, \dots, x_n$, computing the real function $f$, in which each variable occurs exactly once, and let $I_1, \dots, I_n$ be [intervals](interval.md) for which the [interval evaluation](interval-evaluation-of-an-expression.md) is defined. Then

$$E(I_1, \dots, I_n) = \{f(x_1, \dots, x_n) : x_i \in I_i\},$$

so interval evaluation of such an expression computes the exact range of $f$ on the box.

## Depends on

- [Interval evaluation of an arithmetic expression](interval-evaluation-of-an-expression.md)

## Proof depends on

- [Interval evaluation encloses the range](interval-evaluation-encloses-the-range.md)

## Sources

- M. H. van Emden and B. Moa, *The fundamental theorems of interval analysis*, arXiv:cs/0701141v2, 2009, Section 4, Theorem 2 and its proof, which uses that the two operands of each operation have no variables in common. <https://arxiv.org/abs/cs/0701141>
