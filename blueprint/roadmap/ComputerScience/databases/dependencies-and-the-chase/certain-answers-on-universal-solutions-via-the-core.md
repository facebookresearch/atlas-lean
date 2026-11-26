# Certain answers on universal solutions are the null-free answers on the core

In a data exchange setting $(\mathbf S, \mathbf T, \Sigma_{st}, \Sigma_t)$, a solution for a source instance $I$ is
a target instance $J$ such that $I$ and $J$ together satisfy the source-to-target dependencies $\Sigma_{st}$ and $J$
satisfies the target dependencies $\Sigma_t$; a universal solution is a solution with a homomorphism (fixing
constants) to every solution. A core of an instance $J$ is a subinstance $C$ of $J$ such that some homomorphism maps
$J$ to $C$ and none maps $J$ to a proper subinstance of $C$; all cores of $J$ are isomorphic. An existential query over $\mathbf T$ is a formula $\exists \bar y\,\varphi(\bar x, \bar y)$
with $\varphi$ a disjunction of conjunctions of atoms, negated atoms, equalities and negated equalities, subject to the
safety condition that every variable occurring in a conjunction occurs in a relational atom of that conjunction; for a target instance $J$, $q(J){\downarrow}$ is the set of null-free tuples of $q(J)$.
The certain answers of $q$ on universal solutions, $\text{u-certain}(q, I)$, are the tuples in $q(J)$ for every
universal solution $J$ for $I$.

Let $\Sigma_{st}$ be a set of tuple-generating dependencies and $\Sigma_t$ a set of tuple- and equality-generating
dependencies, let $I$ have a universal solution, and let $J_0$ be the core of its universal solutions. For every
existential query $q$ over $\mathbf T$, $\text{u-certain}(q, I) = q(J_0){\downarrow}$; and a universal solution with
this property for every conjunctive query with inequalities is isomorphic to $J_0$. Hence, when $\Sigma_t$ consists of
equality-generating dependencies, $\text{u-certain}(q, I)$ is computable in time polynomial in $I$ for each fixed
existential $q$, whereas the certain answers over all solutions of a Boolean conjunctive query with inequalities can be
coNP-complete.

## Depends on

- [The core of the universal solutions in data exchange](core-of-the-universal-solutions.md)
- [Conjunctive queries with inequalities](../conjunctive-queries/conjunctive-queries-with-inequalities.md)

## Proof depends on

- [The core of the universal solutions is computable in polynomial time for target egds](core-of-universal-solutions-in-polynomial-time.md)

## Sources

- R. Fagin, P. G. Kolaitis and L. Popa, "Data exchange: getting to the core", *ACM Transactions on Database Systems* 30(1):174–208, 2005, the definition of existential queries with its safety condition, Definition 6.3, Proposition 6.4 and the two results numbered Theorem 6.5, the first credited to Abiteboul and Duschka (pp. 204–207).
