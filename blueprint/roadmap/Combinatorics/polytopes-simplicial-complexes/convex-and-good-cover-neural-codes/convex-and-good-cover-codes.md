# Convex and good-cover neural codes

A neural code is convex if convex open sets realize it, and a good-cover code if contractible open sets whose nonempty intersections are all contractible realize it.

Let $\mathcal{C}$ be a [neural code](neural-codes-and-their-realizations.md) on $n$ neurons. Then $\mathcal{C}$ is *convex* if it is realized by a collection of [convex](../../../Geometry/convex-geometry/convex-set.md) open sets in some $\mathbb{R}^d$, and a *good-cover code* if it is realized by a collection $\mathcal{U}$ of [contractible](../../../Topology/algebraic-topology/contractibility-and-local-contractibility/contractible-space.md) open sets such that every nonempty intersection of sets in $\mathcal{U}$ is contractible; such a $\mathcal{U}$ is a *good cover*.

Convex codes are good-cover codes (Proposition 2.15). The converse fails: a code on five neurons is a good-cover code but not convex (Lienkaemper, Shiu and Woodstock; Proposition 2.16).

## Depends on

- [Neural codes and their realizations](neural-codes-and-their-realizations.md)
- [Convex set](../../../Geometry/convex-geometry/convex-set.md)
- [Contractible space](../../../Topology/algebraic-topology/contractibility-and-local-contractibility/contractible-space.md)

## Proof depends on

None.

## Sources

- Aaron Chen, Florian Frick and Anne Shiu, *Neural codes, decidability, and a new local obstruction to convexity*, SIAM Journal on Applied Algebra and Geometry 3 (2019), no. 1, 44–66, https://doi.org/10.1137/18M1186563; read as arXiv:1803.11516v2: Definition 2.3, Propositions 2.15 and 2.16.
