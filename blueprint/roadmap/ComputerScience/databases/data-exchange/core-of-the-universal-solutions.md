# The core of the universal solutions in data exchange

In a data exchange setting $(\mathbf S, \mathbf T, \Sigma_{st}, \Sigma_t)$, a solution for a source instance $I$ is
a target instance $J$ such that $I$ and $J$ together satisfy the source-to-target dependencies $\Sigma_{st}$ and $J$
satisfies the target dependencies $\Sigma_t$; a universal solution is a solution with a homomorphism (fixing
constants) to every solution. A core of an instance $J$ is a subinstance $C$ of $J$ such that some homomorphism (the
identity on constants) maps $J$ to $C$ and none maps $J$ to a proper subinstance of $C$; all cores of $J$ are isomorphic.

Let $\Sigma_{st}$ be a set of tuple-generating dependencies and $\Sigma_t$ a set of tuple- and equality-generating
dependencies. If $J$ is a solution for $I$, then its core is a solution for $I$, and if $J$ is universal, so is its
core. Consequently, if $I$ has a universal solution, there is a universal solution $J_0$, unique up to isomorphism,
that is a core, is isomorphic to the core of every universal solution, and has a one-to-one homomorphism into every
universal solution; in particular it has the fewest facts among universal solutions.

## Depends on

- [Data exchange: universal solutions and certain answers of UCQs](../dependencies-and-the-chase/data-exchange-universal-solutions-and-certain-answers-of-ucq.md)
- [Tuple- and equality-generating dependencies and the chase](../dependencies-and-the-chase/tuple-and-equality-generating-dependencies-and-the-chase.md)

## Proof depends on

- [Successful terminating chases yield universal models](../dependencies-and-the-chase/successful-terminating-chases-yield-universal-models.md)

## Sources

- R. Fagin, P. G. Kolaitis and L. Popa, "Data exchange: getting to the core", *ACM Transactions on Database Systems* 30(1):174–208, 2005, Definitions 2.1 and 2.4 (pp. 179–182), Definition 3.2 and Proposition 3.3 (pp. 185–186), Proposition 3.4 (p. 186) and Corollary 3.5 (p. 187).
