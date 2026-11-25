# Covariance of coalescence times

Let $\rho \ge 0$, let $Q_\rho$ be the [two-locus rate matrix](two-locus-rate.md), and let $m_A$, $m_B$ and $f$ be real functions on the [two-locus states](two-locus-state.md) such that

- $m_A(i) = 0$ where locus $A$ has coalesced, and $(Q_\rho m_A)(i) = -1$ elsewhere;
- $m_B(i) = 0$ where locus $B$ has coalesced, and $(Q_\rho m_B)(i) = -1$ elsewhere;
- $f(i) = 0$ where locus $A$ or locus $B$ has coalesced, and $(Q_\rho f)(i) = -(m_A(i) + m_B(i))$ where neither has.

Then, with $d = \rho^2 + 13\rho + 18$,

- $f(\text{linked}) - m_A(\text{linked})\, m_B(\text{linked}) = (\rho + 18)/d$;
- $f(\text{partly split}) - m_A(\text{partly split})\, m_B(\text{partly split}) = 6/d$;
- $f(\text{split}) - m_A(\text{split})\, m_B(\text{split}) = 4/d$.

These are the backward equations of the means and of the product moment of the two coalescence times; the [path-form statements](covariance-coalescence-times.md) identify their solutions with the moments of the chain.

## Sources

- R. R. Hudson, *Properties of a neutral allele model with intragenic recombination*, Theoret. Population Biol. 23 (1983), 183–201.
- N. L. Kaplan and R. R. Hudson, *The use of sample genealogies for studying a selectively neutral m-loci model with recombination*, Theoret. Population Biol. 28 (1985), 382–396.
