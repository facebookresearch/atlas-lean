# Edmonds' base packing theorem

A matroid $M$ with finite ground set $E$ has $k$ pairwise disjoint bases if and only if for every $U \subseteq E$,

$$
|E \setminus U| \ge k\,\big(r(E) - r(U)\big).
$$

For graphic matroids this is the Nash-Williams-Tutte theorem on $k$ edge-disjoint spanning trees.

## Proof sketch

$k$ disjoint bases exist iff the $k$-fold union of $M$ has rank $k \cdot r(E)$; apply the union rank formula.

## Depends on

- [Matroid union](matroid-union.md)

## Proof depends on

- [Edmonds' matroid union theorem](matroid-union-rank-formula.md)
- [Edmonds' matroid partition theorem](../../../Combinatorics/matroid-theory/matroid-partition-theorem/edmonds-matroid-partition-2.md)

## Sources

- J. Edmonds, "Minimum Partition of a Matroid into Independent Subsets", Journal of Research of the National Bureau of Standards, Section B 69B, 1965.
- A. Schrijver, "Combinatorial Optimization: Polyhedra and Efficiency", Springer, 2003.
