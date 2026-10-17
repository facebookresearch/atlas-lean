---
article_id: af_2fa8d727b75f5549c0862859
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Combinatorics.SimpleGraph.StronglyRegularWanted.srg_reachable_eq_or_adj_mu_zero
---

# Srg reachable eq or adj mu zero

In a strongly regular graph with `μ = 0`, reachable vertices are equal or
adjacent: each connected component is a clique. (Without `μ = 0` this is
false: opposite vertices of a 5-cycle are reachable but neither equal nor
adjacent.)

Proof: Induct on a witnessing walk and close each two-edge segment using the
zero common-neighbor count. Brouwer and Haemers, Section 9.1.4, state the
result: `μ = 0` makes the graph a disjoint union of complete graphs.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Adj of adj of adj of mu zero](adj-of-adj-of-adj-of-mu-zero.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.SimpleGraph.StronglyRegular](../../../../../../../sources/v2/MathlibExt.md)
- A. E. Brouwer and W. H. Haemers, Spectra of Graphs, Springer 2012, Ch. 9 (a disconnected strongly regular graph is a disjoint union of complete graphs); C. Godsil and G. Royle, Algebraic Graph Theory, GTM 207, Ch. 10.
