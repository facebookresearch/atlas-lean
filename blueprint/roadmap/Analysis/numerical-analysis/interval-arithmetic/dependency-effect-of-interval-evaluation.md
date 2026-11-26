# Dependency effect of interval evaluation

When a variable occurs more than once in an expression, [interval evaluation](interval-evaluation-of-an-expression.md) can strictly overestimate the range. For the expression $e = x - x$, which computes the zero function, and an [interval](interval.md) $I = [a, b]$ with $a < b$,

$$E(I) = [a, b] - [a, b] = [a - b,\ b - a] \supsetneq \{0\},$$

so the enclosure has width $2(b - a)$ while the range is a point. Rewriting an expression so that each variable occurs once removes the effect, by [exactness for single occurrences](interval-evaluation-is-exact-for-single-occurrences.md).

## Depends on

- [Interval evaluation of an arithmetic expression](interval-evaluation-of-an-expression.md)
- [Interval](interval.md)

## Related topics

- [Interval evaluation encloses the range](interval-evaluation-encloses-the-range.md)
- [Interval evaluation is exact when each variable occurs once](interval-evaluation-is-exact-for-single-occurrences.md)

## Sources

- M. H. van Emden and B. Moa, *The fundamental theorems of interval analysis*, arXiv:cs/0701141v2, 2009, Section 1, the remark after display (1) that the enclosing interval is typically considerably wider than the range, and Section 4, where the occurrences of a variable shared between subexpressions are tracked by the distribution function. <https://arxiv.org/abs/cs/0701141>
