# Tuple- and equality-generating dependencies and the chase

A tuple-generating dependency is a sentence $\forall \bar{x}\,(\varphi(\bar{x}) \to \exists \bar{y}\,
\psi(\bar{x}, \bar{y}))$ and an equality-generating dependency is $\forall \bar{x}\,(\varphi(\bar{x}) \to
x_i = x_j)$, where $\varphi$ and $\psi$ are conjunctions of atoms.

A trigger for a dependency on an instance is a match of its body. A trigger for a tuple-generating
dependency is active if no extension of the match satisfies the head; a restricted chase step applies one
active trigger, adding the head atoms with fresh labelled nulls for $\bar{y}$. An equality step for an
active equality-generating trigger replaces a null by the other term, and fails if both terms are distinct
constants. A chase sequence is successful and terminating if it is finite, never fails, and ends in an
instance satisfying all dependencies.

For infinite sequences, fairness must be required separately: an arbitrary infinite restricted sequence
need not apply every trigger. Example (added here for illustration): from $R(a)$ with $R(x) \to \exists y\, S(x,y)$,
$S(x,y) \to R(y)$ and $R(x) \to T(x)$, a run can extend the $R$/$S$ chain forever and never add $T(a)$.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Conjunctive queries, answers and canonical databases.

## Sources

- R. Fagin, Ph. G. Kolaitis, R. J. Miller and L. Popa, *Data exchange: semantics and query answering*, Theoret. Comput. Sci. 336 (2005) 89–124, Definitions 3.1 and 3.2 (chase steps for tgds and egds, chase sequences). <https://www.cis.upenn.edu/~val/CIS650/DataX-tcs.pdf>
- Database Theory, Lecture 19: The Chase, TU Dresden, Definition 19.1 (dependencies). <https://iccl.inf.tu-dresden.de/w/images/5/54/Lecture-19-chase-4.pdf>
