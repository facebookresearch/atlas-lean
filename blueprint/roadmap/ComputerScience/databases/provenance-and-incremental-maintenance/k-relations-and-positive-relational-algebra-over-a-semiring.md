# K-relations and positive relational algebra over a semiring

Let $(K, +, \cdot, 0, 1)$ be a commutative semiring. A $K$-relation over a schema $S$ is a function from
tuples over $S$ to $K$ with finite support. The positive relational algebra acts on $K$-relations as
follows: union adds annotations; projection sums the annotations of all tuples with the same projection;
selection multiplies by $1$ or $0$ according to the selection predicate; natural join multiplies
annotations; renaming re-indexes attributes. These operations preserve finite support.

Set semantics is the case $K = \mathbb{B}$, bag semantics the case $K = \mathbb{N}$, and provenance
polynomials the case $K = \mathbb{N}[X]$.

## Depends on

- [Tuple](../relational-algebra/tuple.md)

## Sources

- T. J. Green, G. Karvounarakis and V. Tannen, *Provenance semirings*, PODS 2007, Definition 3.2 and Proposition 3.3. <http://www.cs.ucdavis.edu/~green/papers/pods07.pdf>
