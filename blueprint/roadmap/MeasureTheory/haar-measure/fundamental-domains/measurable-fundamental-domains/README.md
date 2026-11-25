# Measurable fundamental domains for discrete subgroups

Let $G$ be a second-countable Hausdorff topological group with its Borel $\sigma$-algebra and
$\Gamma \le G$ a discrete subgroup. Then there is a measurable set $D \subseteq G$ such that every
$x \in G$ has exactly one $\gamma \in \Gamma$ with $x \gamma \in D$; so $D$ is a fundamental domain
for the right action of $\Gamma$, for every measure on $G$.

## Idea

A fundamental domain picks one point from each orbit. For a measure invariant under right
translation by $\Gamma$, integrals over $G$ then split as integrals over $D$ of sums over $\Gamma$;
without that invariance they need not (for $\Gamma = \mathbb{Z}$ in $\mathbb{R}$, $D = [0, 1)$ and the
point mass at $3/2$, every integral over $D$ vanishes). For the lattice $\mathbb{Z}^n$ in
$\mathbb{R}^n$ the half-open unit cube $[0, 1)^n$ is one; the closed cube repeats boundary orbits.
For a discrete subgroup, discreteness gives a neighbourhood $U$ of the identity so small that each
translate $gU$ meets every orbit $x\Gamma$ in at most one point. Second countability covers $G$ by
countably many such translates, and keeping from each translate the points whose orbit no earlier
translate meets gives a measurable set of orbit representatives.

## Statements

- [Measurable fundamental domains for discrete subgroups](exists-measurable-set-is-fundamental-dom.md)
