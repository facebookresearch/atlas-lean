# Interval arithmetic

Interval arithmetic computes with sets of reals: each operation on intervals returns an interval containing every result of the operation on members of its arguments. Evaluating an arithmetic expression this way encloses the range of the function it computes (the fundamental theorem of interval arithmetic). Repeated occurrences of a variable can make the enclosure strict (the dependency effect, as for $x - x$), though they need not (for $x + x$ on $[0, 1]$ it is exact). With outward rounding the same enclosure holds in floating-point arithmetic, which makes interval methods a tool for verified computation.

- [Interval](interval.md)
- [Interval arithmetic operations](interval-arithmetic-operations.md)
- [Interval evaluation of an arithmetic expression](interval-evaluation-of-an-expression.md)
- [Interval evaluation encloses the range](interval-evaluation-encloses-the-range.md)
- [Dependency effect of interval evaluation](dependency-effect-of-interval-evaluation.md)

## Related topics

- [Fundamental theorem of interval arithmetic and the dependency effect](../fundamental-theorem-of-interval-arithmetic-and-the-dependenc.md): the parent node, whose expansion list also covers exactness for single occurrences and the width laws.
- [Floating-point interval arithmetic with directed rounding is sound](../floating-point-interval-arithmetic-with-directed-rounding-is.md)
