# Absolute continuity of measures

Let $v$ and $w$ be vector measures on a measurable space $X$, with values in additive commutative monoids with a
topology, such as $\mathbb{R}$, $\mathbb{C}$ or $[0, \infty]$: countably additive functions on the measurable sets,
extended by $0$ to the other sets. Then $v$ is absolutely continuous with respect to $w$, written $v \ll w$, if
$v(s) = 0$ for every set $s$ with $w(s) = 0$. This is the general form of absolute continuity of a signed or complex
measure $\nu$ with respect to a positive measure $\mu$: taking $v = \nu$ and $w = \mu$, viewed as a vector measure with
values in $[0, \infty]$, it says that $\nu(E) = 0$ for every measurable set $E$ with $\mu(E) = 0$.

## Idea

Absolute continuity says that $\nu$ charges no set that $\mu$ ignores. For a positive measure $\mu$, a measure with a
density, $\nu(E) = \int_E h \, d\mu$ for a nonnegative measurable or an integrable $h$, is absolutely continuous with
respect to $\mu$; the Radon–Nikodym theorem gives the converse for σ-finite $\mu$ and finite signed or complex $\nu$,
and $h$ is then the derivative $d\nu/d\mu$. For a positive $\mu$ and a finite signed measure $\nu$, absolute continuity
is equivalent to the condition that for every $\varepsilon > 0$ there is $\delta > 0$ with $|\nu(E)| < \varepsilon$
whenever $\mu(E) < \delta$. Absolute continuity and mutual singularity are the two extreme relations of the Lebesgue
decomposition, not negations of each other: a measure that has both relations to a positive $\mu$ is $0$, while
$\lambda + \delta_0$ has neither relation to Lebesgue measure $\lambda$ on $[0, 1]$.

## Statements

- [Absolute continuity of a vector measure with respect to another](absolutely-continuous.md)

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, Definition 9.32 (version read: the open-access PDF dated 12 June 2026).
