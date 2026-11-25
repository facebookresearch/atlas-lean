# Which RA identities survive bag semantics

This node collects the bag-semantics consequences of the identities for relations annotated in a
commutative semiring; the positive identities themselves are stated once, on the
[semiring identity page](../provenance-and-incremental-maintenance/ra-identities-hold-over-every-commutative-semiring.md).

## Expansion

A sound expansion has separate pages for:

1. **Positive laws for bags** as the specialization to the natural numbers of the semiring identity
   theorem (union and join associative and commutative, join distributive over union, selection and
   projection pushdown where applicable).
2. **Failures for bags,** each with an explicit instance, where $t$ is a tuple and $\{t\}$ the bag
   containing it once: union is not idempotent ($R \cup R \neq R$ whenever $R$ is nonempty, for example
   $R = \{t\}$); join is not idempotent ($R \bowtie R \neq R$ when some tuple has multiplicity at least $2$);
   and bag difference, the truncated subtraction of multiplicities, does not distribute over union
   ($(R \cup S) - T \neq (R - T) \cup (S - T)$ for $R = S = T = \{t\}$, where the multiplicities of $t$ are
   $1$ and $0$). Not every identity involving difference or duplicate elimination fails: $R - \varnothing = R$
   and $\delta(\delta(R)) = \delta(R)$ hold for bags. Bag difference and duplicate elimination are not
   operations of the positive algebra; the page for this item defines them before using them.

## Depends on

- [Bag relations and bag relational algebra](bag-relations-and-bag-relational-algebra.md)
- [RA+ identities hold over every commutative semiring](../provenance-and-incremental-maintenance/ra-identities-hold-over-every-commutative-semiring.md)

## Sources

- Provenance Semirings (Green, Karvounarakis, Tannen), PODS 2007, Proposition 3.4 (RA identities valid on K-relations). <http://www.cs.ucdavis.edu/~green/papers/pods07.pdf>
