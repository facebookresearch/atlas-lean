# Natural-number utilities for finite preferences by lower-contour counts

Let $X$ be a finite set and $\succsim$ a complete and transitive preference on $X$. Define $u : X \to \mathbb N$ by

$$u(x) = \#\{y \in X : x \succsim y\},$$

the size of the weak lower contour set of $x$. Then $u$, viewed as real-valued, [represents](represents.md) $\succsim$: $x \succsim y$ if and only if $u(x) \ge u(y)$. Indeed, if $x \succsim y$ then by transitivity every element below $y$ is below $x$, so $u(x) \ge u(y)$; if not, then $y \succ x$ by completeness, and $y$ lies in its own lower contour set but not in that of $x$, which is contained in that of $y$, so $u(y) > u(x)$. Indifferent alternatives have equal counts.

Consequently, for every nonempty $A \subseteq X$ the $\succsim$-best elements of $A$ are exactly the maximizers of $u$ on $A$, and such a maximizer exists. This gives a direct construction of a [real-valued representation of finite preferences](exists-represents.md) with natural-number values. The utilities are ordinal: their differences carry no meaning as intensities of preference, and the representation is distinct from an expected-utility representation.

## Background

- [Rational preferences on finite sets have utility representations](exists-represents.md)

## Sources

- J. Levin and P. Milgrom, *Introduction to Choice Theory*, lecture notes, Stanford University, September 2004, Proposition 3, for the background finite representation result. Their proof ranks the alternatives by successively removing choice sets; the lower-contour count gives an independent, non-inductive construction of the same representation result.
