# Dependency effect of interval evaluation

When a variable occurs more than once in an expression, [interval evaluation](interval-evaluation-of-an-expression.md) can strictly overestimate the range. For the expression $e = x - x$, which computes the zero function, and an [interval](interval.md) $I = [a, b]$ with $a < b$,

$$E(I) = [a, b] - [a, b] = [a - b,\ b - a] \supsetneq \{0\},$$

so the enclosure has width $2(b - a)$ while the range is a point.

## Depends on

- [Interval evaluation of an arithmetic expression](interval-evaluation-of-an-expression.md)
- [Interval](interval.md)

## Related topics

- [Interval evaluation encloses the range](interval-evaluation-encloses-the-range.md)

## Sources

- T. Hickey, Q. Ju and M. H. van Emden, "Interval arithmetic: from principles to implementation", *Journal of the ACM* 48(5):1038–1068, 2001, Section 1: the main cause of wide intervals is that interval arithmetic does not identify different occurrences of the same variable, and treats them as if they were unique occurrences. <https://doi.org/10.1145/502102.502106>
