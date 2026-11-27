# Modular lattices and lattices of subspaces

A lattice is a partially ordered set in which any two elements have a least upper bound and a greatest lower bound; it is modular if $x \le z$ implies $x \vee (y \wedge z) = (x \vee y) \wedge z$. The subspace lattice of a vector space is its set of subspaces ordered by inclusion.

**Lattices.** A *lattice* is a [partially ordered set](../../ordered-sets/partial-order.md) $(L, \le)$ in which every two elements $x, y$ have a least upper bound $x \vee y$ (join) and a greatest lower bound $x \wedge y$ (meet). Equivalently it is an algebra $(L, \vee, \wedge)$ with two binary operations that are associative, commutative and idempotent and satisfy the absorption laws $x \vee (x \wedge y) = x$ and $x \wedge (x \vee y) = x$, the order being recovered by $x \le y \iff x \wedge y = x$. A lattice is *bounded* if it has a least element $0$ and a greatest element $1$, which may then be added as constants.

**Modular lattices.** A lattice is *modular* if it satisfies the modular law: $x \le z$ implies $x \vee (y \wedge z) = (x \vee y) \wedge z$; equivalently, it satisfies the identity $x \vee (y \wedge (x \vee z)) = (x \vee y) \wedge (x \vee z)$.

**Lattices of subspaces.** For a vector space $V$ over a division ring $F$, the *subspace lattice* $\mathrm L(V)$ is the set of all subspaces of $V$ ordered by inclusion; it is a bounded modular lattice with $U \vee W = U + W$, $U \wedge W = U \cap W$, $0 = \{0\}$ and $1 = V$. If $V$ is [finite-dimensional](../../../LinearAlgebra/bases-and-dimension/bases-and-coordinates/dimension/finite-dimensional.md) of dimension $d$, then $\mathrm L(V)$ has height $d$, and it is finite if moreover $F$ is finite.

## Depends on

- [Partially ordered set](../../ordered-sets/partial-order.md)
- [Finite-dimensional vector space](../../../LinearAlgebra/bases-and-dimension/bases-and-coordinates/dimension/finite-dimensional.md)

## Proof depends on

None.

## Expansion

This node states definitions. The modularity of $\mathrm L(V)$ follows from the modular law for subspaces, $U + (W \cap X) = (U + W) \cap X$ whenever $U \subseteq X$.

## Sources

- Christian Herrmann, Yasuyuki Tsukamoto and Martin Ziegler, "On the consistency problem for modular lattices and related structures", *International Journal of Algebra and Computation* 26(8), 2016, pp. 1573–1595, doi:[10.1142/S0218196716500697](https://doi.org/10.1142/S0218196716500697); read as arXiv:1607.03315v1, <https://arxiv.org/abs/1607.03315v1>, whose numbering is used: Section 2 ("Algebraic structures") and Section 3 ("Coordinates in modular lattices").
