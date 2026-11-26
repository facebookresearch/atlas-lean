# Radon–Nikodym theorem for finite signed measures

Let $\mu$ be a σ-finite measure and $s$ a signed measure with real values on the same measurable space, with $s(E) = 0$
whenever $\mu(E) = 0$. Then $s(E) = \int_E (ds/d\mu) \, d\mu$ for every measurable $E$, where the Radon–Nikodym
derivative $ds/d\mu$ is integrable, by the card's second statement. Applied to the real and imaginary parts, it gives
the Radon–Nikodym theorem for a complex measure $\nu$ absolutely continuous with respect to $\mu$: $d\nu = h \, d\mu$
for an integrable complex $h$.

## Idea

A measure with a density, $E \mapsto \int_E h \, d\mu$, vanishes on the sets of $\mu$-measure $0$; the theorem is the
converse, and the density is unique up to sets of $\mu$-measure $0$. The proof treats the positive and negative parts of
the Jordan decomposition of $s$ separately, finite positive measures absolutely continuous with respect to $\mu$. For
such a measure $\nu$, the measurable $f \ge 0$ with $\int_E f \, d\mu \le \nu(E)$ for every measurable $E$ are closed
under maxima, one of them has the largest integral, and it is a density of $\nu$. The theorem identifies the dual of
$L^1$ of a σ-finite measure with $L^\infty$, and it gives conditional expectations in probability.

## Statements

- [Radon–Nikodym theorem for finite signed measures](with-density-rn-deriv-eq.md)
- [The Radon–Nikodym derivative of a finite signed measure is integrable](integrable-rn-deriv.md): the density is integrable, so the first statement gives $s(E) = \int_E (ds/d\mu) \, d\mu$.
- [Lebesgue decomposition of a measure](lebesgue-decomposition-of-a-measure.md): a measure $\mu$ is the sum of a part singular with respect to $\nu$ and a part with a density with respect to $\nu$.

## Background

- [Absolute continuity of measures](../absolute-continuity-of-measures/README.md): the hypothesis
- [Jordan decomposition of a finite signed measure](../../jordan-decomposition-of-signed-measures/README.md): the parts used in the construction

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, result 9.36 (version read: the open-access PDF dated 12 June 2026).
