# Abstract stream/relation semantics of continuous queries (CQL)

This node collects the abstract semantics of continuous queries over the discrete time domain $\mathbb{N}$, as
separate definitions and results.

## Expansion

A sound expansion has separate pages for:

1. **Streams and relations.** Time is $\mathbb{N}$. A stream is a bag of elements $(s, \tau)$ with $\tau \in \mathbb{N}$ in which
   only finitely many elements have any given timestamp; over $\mathbb{N}$ this makes every prefix (timestamps at most
   $\tau$) finite. A time-varying relation is a map $R$ from $\mathbb{N}$ to finite bags of tuples. Over a time domain with
   infinitely many instants before a given one, such as $\mathbb{Z}$, prefix finiteness fails (the Rstream of a constant
   nonempty relation has infinitely many elements before time $0$), which is why the clock is $\mathbb{N}$.
2. **Window operators.** For a range $\omega \in \mathbb{N}$, the time-based window maps a stream $S$ to the relation
   $R(\tau) = \{\!\{ s : (s, t) \in S,\ \max(0, \tau - \omega) \le t \le \tau \}\!\}$, finite by prefix finiteness. This page uses
   the closed window. The tuple-based and partitioned windows are defined with an explicit tie-breaking rule for elements
   with equal timestamps.
3. **Relation-to-stream operators.** With $R(\tau - 1)$ the relation at the preceding instant for $\tau \ge 1$, and the
   empty bag in its place at $\tau = 0$, $\mathrm{Istream}(R)$ contains $(s, \tau)$ with multiplicity
   $\max(0, R(\tau)(s) - R(\tau - 1)(s))$, $\mathrm{Dstream}(R)$ with multiplicity $\max(0, R(\tau - 1)(s) - R(\tau)(s))$,
   and $\mathrm{Rstream}(R)$ contains every tuple of $R(\tau)$ at each $\tau$.
4. **Signed change.** The signed change of $R$ at $\tau$, the $\mathbb{Z}$-relation $R(\tau) - R(\tau - 1)$, equals
   $\mathrm{Istream}(R)$ minus $\mathrm{Dstream}(R)$ at $\tau$. $\mathrm{Istream}$ alone is not the signed change: deleting the
   only copy of a tuple gives signed change $-1$ and $\mathrm{Istream}$ multiplicity $0$.
5. **Relation-to-relation operators and composition.** Each operator of the bag relational algebra lifts pointwise to
   time-varying relations, $(\mathrm{op}\, R)(\tau) = \mathrm{op}(R(\tau))$. A continuous query is any type-consistent composition of
   these three operator classes (a relation-to-stream result may feed a later window); each operator maps finite bags at
   each instant to finite bags and uses only inputs up to that instant, so by induction on the composition every query is well
   defined on streams with finitely many elements per timestamp.

## Depends on

- [Bag relations and bag relational algebra](../bags-and-nulls/bag-relations-and-bag-relational-algebra.md)
- [Z-relations and delta rules for incremental maintenance](../provenance-and-incremental-maintenance/z-relations-and-delta-rules-for-incremental-maintenance.md)

## Sources

- A. Arasu, S. Babu and J. Widom, *The CQL continuous query language: semantic foundations and query
  execution*, VLDB Journal 15(2), 2006, Sections 4–6.3 (Section 4: time domain $\mathbb{N}$ and finite bags per timestamp;
  Definition 3: queries as type-consistent compositions; Section 6.1.1: the time-based window with
  $\max(\tau - T, 0) \le t \le \tau$; Section 6.3: relation-to-stream operators).
  <http://infolab.stanford.edu/~arvind/papers/cql-vldbj.pdf>
