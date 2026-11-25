# Mutually singular measures

Two vector measures $v$ and $w$ on a measurable space $X$, with values in additive commutative monoids with a topology,
are mutually singular, written $v \perp w$, if there is a measurable set $s$ such that $v(t) = 0$ for every
$t \subseteq s$ and $w(t) = 0$ for every $t \subseteq X \setminus s$: $v$ lives on $X \setminus s$ and $w$ lives on $s$.
This is the general form of mutual singularity of two signed measures: taking $v$ and $w$ to be them, $E = s$ and
$F = X \setminus s$, it says that $X$ is the disjoint union of measurable sets $E$ and $F$ with $E$ null for $v$ and $F$
null for $w$.

## Idea

Mutual singularity and absolute continuity are the two extreme relations of the Lebesgue decomposition, not negations of
each other: a measure that has both relations to a positive measure is $0$, while $\lambda + \delta_0$ has neither
relation to Lebesgue measure $\lambda$ on $[0, 1]$. Lebesgue measure on $\mathbb{R}$ is singular with respect to the
Dirac measure at a point and with respect to the measure whose distribution function is the Cantor function. The two
parts of the Jordan decomposition $\nu = \nu^+ - \nu^-$ of a finite signed measure are mutually singular, and, for a
positive measure $\mu$, the Lebesgue decomposition writes a σ-finite positive measure as the sum of a part absolutely
continuous with respect to $\mu$ and a part singular with respect to $\mu$.

## Statements

- [Mutually singular vector measures](mutually-singular.md)

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, Definition 9.28 (version read: the open-access PDF dated 12 June 2026).
