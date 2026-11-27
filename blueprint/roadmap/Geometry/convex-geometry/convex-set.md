# Convex set

A subset $C$ of a real vector space is convex if $(1 - t)x + ty \in C$ whenever $x, y \in C$ and $0 \le t \le 1$, so that $C$ contains the segment between any two of its points. Mathlib defines convexity more generally, with scalars in a partially ordered semiring and two weights in place of $1 - t$ and $t$. Let $\mathbb{k}$ be a semiring with a partial order, $E$ an additive commutative monoid with a scalar multiplication by $\mathbb{k}$, and $s \subseteq E$. Mathlib calls $s$ *star-convex* at a point $x$ if $ax + by \in s$ for every $y \in s$ and all $a, b \in \mathbb{k}$ with $a \ge 0$, $b \ge 0$ and $a + b = 1$, and calls $s$ *convex* if it is star-convex at each of its points. Equivalently, $ax + by \in s$ for all $x, y \in s$ and all such weights $a, b$. No order on $E$ is needed, and the empty set is convex. For $\mathbb{k} = \mathbb{R}$, the weights $a, b \ge 0$ with $a + b = 1$ are exactly $a = 1 - t$ and $b = t$ with $0 \le t \le 1$, which gives the familiar definition.

## Sources

- Stephen Boyd and Lieven Vandenberghe, Convex Optimization, Cambridge University Press, 2004.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for star-convex sets: `StarConvex`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Convex/Star.lean#L67-L71.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for convexity with two weights: `convex_iff_add_mem`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Convex/Basic.lean#L72-L74.
