# Counting measure on [0, 1] is not s-finite

Counting measure on $[0, 1]$ is not s-finite, that is, not a countable sum of finite measures,
and in particular not $\sigma$-finite. This is the hypothesis that Tonelli's theorem needs: for
s-finite measures, and in particular $\sigma$-finite ones, the two iterated integrals of a
nonnegative measurable function on a product agree. With Lebesgue measure $m$ and counting
measure $\#$ on $[0, 1]$, both with the Borel $\sigma$-algebra, the indicator of the diagonal has
iterated integrals $1$ and $0$, so the conclusion fails without the hypothesis.

## Idea

Integrate the indicator of the diagonal $\Delta = \{(x, x)\}$ in the two orders. With counting
measure inside, each slice meets $\Delta$ in exactly one point, so the inner integral is $1$ and
the iterated integral is $1$. With Lebesgue measure inside, each slice is a single point of
Lebesgue measure $0$, so the iterated integral is $0$. If counting measure on $[0, 1]$ were
s-finite, Tonelli's theorem would make the two values equal, which proves the main statement.
Tao's exercise uses the Lebesgue and the discrete $\sigma$-algebras; the diagonal is Borel, so
this version is slightly stronger.

## Statements

- [Counting measure on \[0, 1\] is not s-finite](not-s-finite-count-restrict-icc.md)
- [Diagonal indicator, counting measure inside](lintegral-lintegral-count-indicator-diag.md): the first iterated integral, equal to $1$.
- [Diagonal indicator, Lebesgue measure inside](lintegral-count-lintegral-indicator-diag.md): the second iterated integral, equal to $0$.

## Related topics

- [A product of measures with densities](../products-of-measures-with-densities/pi-with-density.md): a use of Tonelli's theorem for σ-finite measures, the hypothesis whose failure this card exhibits.

## Sources

- T. Tao, *An Introduction to Measure Theory*, Graduate Studies in Mathematics 126, American Mathematical Society, 2011, Section 1.7.
