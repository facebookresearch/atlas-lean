---
article_id: af_91d1e811e85d8e3484790168
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.orderly_canonical_prefix
---

# Orderly canonical prefix

Orderly generation for union-closed sets: let `U ≠ {Ω_n, ∅}` be a union-closed
family for the universe `Ω_n` that is the canonical representative of its
isomorphism class. If `U = {A_1, …, A_k, ∅}` with `A_1 < ⋯ < A_k` in the
paper's set order and `1 ≤ m ≤ k`, then the prefix `{A_1, …, A_m, ∅}` is also
the canonical representative of its class.

Provenance: Gunnar Brinkmann and Robin Deklerck, "Generation of Union-Closed
Sets and Moore Families", Journal of Integer Sequences 21 (2018),
Article 18.1.7, Theorem `thm:orderly`, source lines 275–281,
<https://cs.uwaterloo.ca/journals/JIS/VOL21/Brinkmann/brink6.tex>.
Canonical means the family string (sort keys of nonempty members in increasing
order) is lexicographically minimal among permuted images; the set order sorts
by decreasing cardinality, breaking ties by the binary code.

Proof: The binary-key bound identifies the indexed families with strictly sorted key lists, and
sorted-submultiset order statistics lift any improving permutation of a prefix to the full family.
This is the orderly-generation argument of Brinkmann and Deklerck, Theorem `thm:orderly`.

## Depends on

- [Is Canonical](is-canonical.md)
- [Is Union Closed](is-union-closed.md)
- [Set LT](set-lt.md)

## Proof depends on

- [Orderly canonical prefix of sorted](orderly-canonical-prefix-of-sorted.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.UnionClosedOrderly](../../../../../../../sources/v2/MathlibExt.md)
