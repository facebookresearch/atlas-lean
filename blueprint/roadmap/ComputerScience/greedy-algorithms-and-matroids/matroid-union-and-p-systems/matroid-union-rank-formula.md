# Edmonds' matroid union theorem

The rank function of the matroid union satisfies, for every finite $X$,

$$
r_{M_1 \vee \dots \vee M_k}(X) = \min_{U \subseteq X} \Big( |X \setminus U| + \sum_{i=1}^{k} r_{M_i}(U) \Big),
$$

and the maximum size of a union-independent subset of $X$ equals this minimum.

## Proof sketch

Reduce to matroid intersection: take the direct sum of $M_1, \dots, M_k$ on $k$ disjoint copies of the ground set and intersect with the partition matroid allowing at most one copy of each element; Edmonds' intersection formula gives the min-max relation.

## Depends on

- [Matroid union](matroid-union.md)

## Proof depends on

- [Edmonds' matroid intersection theorem](../../../Combinatorics/matroid-theory/matroid-intersection-theorem/edmonds-matroid-intersection.md)

## Sources

- J. Edmonds, "Minimum Partition of a Matroid into Independent Subsets", Journal of Research of the National Bureau of Standards, Section B 69B, 1965.
- J. Edmonds, "Submodular Functions, Matroids, and Certain Polyhedra", in Combinatorial Structures and Their Applications, Gordon and Breach, 1970.
- A. Schrijver, "Combinatorial Optimization: Polyhedra and Efficiency", Springer, 2003.
