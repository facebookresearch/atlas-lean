# Atoms of a distribution function

Let $\mu$ be a probability measure on $\mathbb{R}$ with cumulative distribution function $F(y) = \mu((-\infty, y])$, and for $x \in \mathbb{R}$ let $F(x^-) = \lim_{y \to x^-} F(y)$ be its left limit at $x$. Then the mass of the atom at $x$ is the jump of $F$ at $x$: $\mu(\{x\}) = F(x) - F(x^-)$, a nonnegative number since $F$ is nondecreasing.

## Idea

The half-line $(-\infty, x)$ is the increasing union of the half-lines $(-\infty, y]$ for $y < x$, so its measure is $F(x^-)$; removing it from $(-\infty, x]$ leaves the point $\{x\}$. Since $F$ is right-continuous, it follows that $F$ is continuous at $x$ exactly when $\mu(\{x\}) = 0$. A probability measure has fewer than $n$ atoms of mass greater than $1/n$, hence at most countably many atoms, so the continuity points of $F$ are dense; at such a point the boundary of $(-\infty, x]$ is a null set. These are the points where convergence in distribution is tested: probability measures on $\mathbb{R}$ converge weakly exactly when their distribution functions converge at every continuity point of the limit.

## Statements

- [Atoms are the jumps of the cdf](measure-singleton-eq-cdf-sub-left-lim.md)
- [The cdf is continuous exactly at the non-atoms](continuous-at-cdf-iff-measure-singleton.md): consequence: continuity exactly at non-atoms
- [No atom at a continuity point of the cdf](cdf-continuous-at-singleton-null.md): consequence: no atom at a continuity point
- [Continuity points of the cdf have null boundary](cdf-continuous-at-frontier-iic-null.md): consequence: null boundary of half-lines at continuity points
- [The continuity points of the cdf are dense](dense-cdf-continuity-points.md): a consequence: a probability measure has at most countably many atoms, so the continuity points of the distribution function are dense
- [Mass of a half-open interval via the cdf](measure-ioc-eq-of-real-cdf.md): the masses of half-open intervals, $\mu((a, b]) = \max(F(b) - F(a), 0)$; the atom formula is their limit as $a$ increases to $b$
