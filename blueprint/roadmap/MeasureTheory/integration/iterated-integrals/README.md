# Fubini–Tonelli theorem for iterated integrals

Let $\mu$ and $\nu$ be s-finite measures, for instance σ-finite ones. For a function $f$ on the product that is
integrable for $\mu \times \nu$, with values in a real Banach space such as $\mathbb{R}$ or $\mathbb{C}$, the two
iterated integrals of $f$ are equal: $\int \int f \, d\nu \, d\mu = \int \int f \, d\mu \, d\nu$. This is Fubini's
theorem; the card's second statement, Tonelli's theorem, gives the same equality in $[0, \infty]$ for $f \ge 0$ almost
everywhere measurable, with no integrability hypothesis.

## Idea

Both iterated integrals equal the integral over the product, whose measure gives a rectangle $A \times B$ the mass
$\mu(A) \nu(B)$, so a double integral can be computed one variable at a time. Tonelli's form comes first. For indicators
of measurable sets and finite $\mu$ and $\nu$, the sets for which it holds contain the rectangles, which form a
π-system, and are closed under complements, by finiteness, and under countable disjoint unions, by monotone convergence,
so Dynkin's π–λ theorem gives every measurable set; s-finite measures are countable sums of finite ones, over which both
sides add up. Simple functions and monotone convergence then give every nonnegative measurable function. Fubini's form
follows for a real $f$ by applying Tonelli's form to $f^+$ and $f^-$, whose integrals are finite, and subtracting, and
for a complex $f$ by taking real and imaginary parts. For $f$ with values in a Banach space, approximate $f$ in
$L^1(\mu \times \nu)$ by simple functions $\sum_k v_k \chi_{E_k}$, for which the equality follows from the case of
indicators; replacing $f$ by such a $g$ changes each iterated integral by at most $\int \|f - g\| \, d(\mu \times \nu)$,
by Tonelli's form applied to $\|f - g\|$, so the equality passes to the limit. A hypothesis on the measures cannot be
dropped: for Lebesgue measure and counting measure on $[0, 1]$, the indicator of the diagonal has iterated integrals $1$
and $0$.

## Statements

- [Fubini's theorem for iterated integrals](integral-integral-swap.md)
- [Tonelli's theorem for iterated integrals](lintegral-lintegral-swap.md): the form for functions with values in $[0, \infty]$, with no integrability hypothesis.

## Background

- [Counting measure on \[0, 1\] is not s-finite](../fubini-tonelli-theorem/README.md): the hypothesis on the measures cannot be dropped
- [Lebesgue integral](../nonnegative-lebesgue-integral/lebesgue-integral/README.md): the integral

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, results 5.28 and 5.32 (version read: the open-access PDF dated 12 June 2026).
