# Least upper bound of a subset

In a partially ordered set $P$, an element $s^*$ is the supremum of a subset $S$ when it is an upper bound of $S$ and lies below every upper bound of $S$; that is, $s^*$ is the least element of the set of upper bounds of $S$. Mathlib defines this property for any set with a relation $\le$. Let $\le$ be a binary relation on a set $\alpha$, with no axioms assumed, and let $S \subseteq \alpha$. An *upper bound* of $S$ is an element $x \in \alpha$ with $a \le x$ for all $a \in S$. An element $a \in \alpha$ is a *least upper bound* of $S$ when $a$ is an upper bound of $S$ and $a \le x$ for every upper bound $x$ of $S$. This is a property of $a$; it does not assert that a least upper bound exists. In a partially ordered set a least upper bound is unique when it exists, since two of them lie below each other, and it is then the supremum $\sup S$ of the familiar definition.

## Sources

- B. A. Davey and H. A. Priestley, Introduction to Lattices and Order, 2nd ed., Cambridge University Press, 2002.
- The mathlib Community, *mathlib4* at revision fc4f59e577feb1a4956671bc04ac18aaaf8cd842, for upper bounds and least elements: `upperBounds`, https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Order/Bounds/Defs.lean#L35-L49.
