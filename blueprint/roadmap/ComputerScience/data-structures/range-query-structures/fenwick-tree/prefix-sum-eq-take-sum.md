# Correctness of Fenwick tree prefix sums

Let $t$ be a Fenwick tree representing a list $a$
of elements of an additive commutative monoid. Then for every natural number $k$, including
$k > |a|$, the prefix sum of length $k$ of $t$ equals the sum of the first $\min(k, |a|)$ entries
of $a$.
