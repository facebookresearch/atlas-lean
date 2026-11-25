# RA+ identities hold over every commutative semiring

Let $(K, +, \cdot, 0, 1)$ be a set with two binary operations and two distinguished elements, and define union,
natural join, projection, selection (by a predicate taking the values $0$ and $1$, such as an equality with a
constant) and renaming on $K$-relations by the formulas of Green, Karvounarakis and Tannen (Definition 3.2): union
adds annotations, join multiplies them, projection sums the annotations of the tuples with the same projection,
selection multiplies by the predicate's value, and renaming re-indexes attributes. The following identities, each
when its sides are defined on the same schema, hold for all $K$-relations if and only if $K$ is a commutative
semiring (Proposition 3.4): union is associative and commutative with the empty relation as identity; join is
associative and commutative and distributes over union; projections and selections commute with each other and
with unions and joins where applicable; and $\sigma_{\mathrm{false}}(R) = \emptyset$ and
$\sigma_{\mathrm{true}}(R) = R$. Over a commutative semiring, join also has as identity the relation over the empty
schema that annotates the empty tuple with $1$. This is the canonical page for positive bag laws, which are the case
$K = \mathbb{N}$.

## Depends on

- [K-relations and positive relational algebra over a semiring](k-relations-and-positive-relational-algebra-over-a-semiring.md)

## Sources

- Provenance Semirings (Green, Karvounarakis, Tannen), PODS 2007, Definition 3.2 and Proposition 3.4. <http://www.cs.ucdavis.edu/~green/papers/pods07.pdf>
