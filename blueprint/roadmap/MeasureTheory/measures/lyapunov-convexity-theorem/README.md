# Lyapunov convexity theorem

Let $\mu$ be a finite atomless measure, $E$ a finite-dimensional real normed space and
$f : \alpha \to E$ Bochner integrable. Then the set
$\{\int_s f \, d\mu : s \text{ measurable}\}$ of integrals of $f$ over measurable sets is compact
and convex.

## Idea

For real-valued $f \ge 0$ this is close to Sierpiński's theorem: the integrals over measurable sets
fill a whole interval. In several dimensions convexity is the surprise. Applied to the densities
of finitely many atomless measures, it says that a space can be cut into two sets that every one of
the measures splits in half, a fair division. The theorem fails for infinite-dimensional $E$. A
short proof, due to Lindenstrauss, uses the Krein–Milman theorem: the extreme points of the set of
measurable functions $0 \le g \le 1$ mapping to a given value of $\int g f \, d\mu$ are indicator
functions.

## Statements

- [Lyapunov convexity theorem](lyapunov-convexity.md)
- [Lyapunov range](lyapunov-range.md): the set of the statement.

## Background

- [Sierpiński's theorem on atomless measures](../atomless-measures/README.md): the one-dimensional case and the definition of atomless measures.

## Sources

- A. Lyapunov, Izv. Akad. Nauk SSSR 4 (1940).
- J. Diestel and J. J. Uhl, *Vector Measures*, American Mathematical Society, 1977.
