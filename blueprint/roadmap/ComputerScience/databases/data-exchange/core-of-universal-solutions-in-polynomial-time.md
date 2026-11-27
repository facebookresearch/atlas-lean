# The core of the universal solutions is computable in polynomial time for target egds

In a data exchange setting $(\mathbf S, \mathbf T, \Sigma_{st}, \Sigma_t)$, a solution for a source instance $I$ is
a target instance $J$ such that $I$ and $J$ together satisfy the source-to-target dependencies $\Sigma_{st}$ and $J$
satisfies the target dependencies $\Sigma_t$; a universal solution is a solution with a homomorphism (fixing
constants) to every solution. A core of an instance $J$ is a subinstance $C$ of $J$ such that some homomorphism maps
$J$ to $C$ and none maps $J$ to a proper subinstance of $C$; all cores of $J$ are isomorphic.

For every fixed data exchange setting in which $\Sigma_{st}$ is a set of tuple-generating dependencies and $\Sigma_t$
is a set of equality-generating dependencies, there is a polynomial-time algorithm that, given a source instance $I$,
decides whether $I$ has a solution and, if so, computes the core of its universal solutions (greedily for
$\Sigma_t = \emptyset$, and in general by repeatedly applying useful endomorphisms of the canonical universal solution
that move only a bounded set of nulls).

## Depends on

- [The core of the universal solutions in data exchange](core-of-the-universal-solutions.md)

## Proof depends on

- [Data exchange: universal solutions and certain answers of UCQs](../dependencies-and-the-chase/data-exchange-universal-solutions-and-certain-answers-of-ucq.md)

## Sources

- R. Fagin, P. G. Kolaitis and L. Popa, "Data exchange: getting to the core", *ACM Transactions on Database Systems* 30(1):174–208, 2005, Algorithm 5.1 and Theorem 5.2 (pp. 191–192), Theorem 5.9, Algorithm 5.14 and Theorem 5.15 (pp. 196–200).
