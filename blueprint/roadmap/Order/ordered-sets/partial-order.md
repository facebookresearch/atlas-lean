# Partially ordered set

A *partial order* on a set $P$ is a binary relation $\le$ on $P$ with three properties. It is reflexive: $x \le x$ for every $x \in P$. It is transitive: $x \le y$ and $y \le z$ imply $x \le z$. It is antisymmetric: $x \le y$ and $y \le x$ imply $x = y$. A *partially ordered set* (poset, or ordered set) is a pair $(P, \le)$ consisting of a set $P$ and a partial order $\le$ on $P$. The associated strict order is given by $x < y$ when $x \le y$ and not $y \le x$; by antisymmetry this holds exactly when $x \le y$ and $x \ne y$.

## Sources

- B. A. Davey and H. A. Priestley, Introduction to Lattices and Order, 2nd ed., Cambridge University Press, 2002.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for the strict order $x < y$ as $x \le y$ and not $y \le x$: `Preorder`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Order/Defs/PartialOrder.lean#L43-L47.
