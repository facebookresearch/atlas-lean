# The core of the universal solutions is computable in polynomial time for target egds

In a data exchange setting $(\mathbf S, \mathbf T, \Sigma_{st}, \Sigma_t)$, a solution for a source instance $I$ is
a target instance $J$ such that $I$ and $J$ together satisfy the source-to-target dependencies $\Sigma_{st}$ and $J$
satisfies the target dependencies $\Sigma_t$; a universal solution is a solution with a homomorphism (fixing
constants) to every solution. A core of an instance $J$ is a subinstance $C$ of $J$ such that some homomorphism (the
identity on constants) maps $J$ to $C$ and none maps $J$ to a proper subinstance of $C$; all cores of $J$ are isomorphic.

For every fixed data exchange setting in which $\Sigma_{st}$ is a set of tuple-generating dependencies and $\Sigma_t$
is a set of equality-generating dependencies, there is a polynomial-time algorithm that, given a source instance $I$,
decides whether $I$ has a solution and, if so, computes the core of its universal solutions (greedily for
$\Sigma_t = \emptyset$; in general, starting from the canonical universal solution as the current instance $K$, by
repeatedly replacing $K$ by $h(K)$ for an endomorphism $h$ of $K$ with $h(K) \subsetneq K$ that moves only the nulls of
a bounded number of blocks of the preuniversal instance, the target before the egds are chased, and stopping when no
such map exists). Progress is measured on the current instance: for the canonical solution $\{R(a, u), R(a, v)\}$,
folding $v$ onto $u$ leaves the core $\{R(a, u)\}$, on which the same map, still useful on the original, does nothing.

## Depends on

- [The core of the universal solutions in data exchange](core-of-the-universal-solutions.md)

## Proof depends on

- [Data exchange: universal solutions and certain answers of UCQs](../dependencies-and-the-chase/data-exchange-universal-solutions-and-certain-answers-of-ucq.md)

## Sources

- R. Fagin, P. G. Kolaitis and L. Popa, "Data exchange: getting to the core", *ACM Transactions on Database Systems* 30(1):174–208, 2005, Algorithm 5.1 and Theorem 5.2 (pp. 191–192), Theorem 5.9, Algorithm 5.14 and Theorem 5.15 (pp. 196–200).
