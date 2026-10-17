---
article_id: af_9bab78590e943556cf7e26c7
declaration: def
origin: cited
statement: formalized
lean: SimpleGraph.generalizedExtremalNumber
---

# Generalized Extremal Number

Generalized Turán number `ex(n, T, H)`: the maximum possible number of
copies of pattern `T` in an `H`-free host graph on `n` vertices. `G.copyCount T`
counts copies of pattern `T` in host `G`, and `H.Free G` states that `G` is
`H`-free. The intended domain from the source is patterns `T` and `H` with no
isolated vertices; the definition itself does not require this.

The total definition follows Mathlib's `Finset.sup` convention used by
`SimpleGraph.extremalNumber`: it is the supremum of `G.copyCount T` over the
filtered family `Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G)`.
As with `Finset.sup` over `ℕ`, the value is `0` when the filtered family is
empty.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.SimpleGraph.GeneralizedExtremal](../../../../../../../sources/v2/MathlibExt.md)
