---
article_id: af_9075f2c59b80b21b3f637b2d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.zagier_probability_product_two_cyclic_permutations
---

# Zagier Cyclic Permutation Product

Zagier's formula for the probability that the product of two uniformly chosen cyclic
permutations of `Fin n` has exactly `k` cycles:
`(1 + (-1) ^ (n - k)) / Nat.factorial (n + 1) * Nat.stirlingFirst (n + 1) k`.
Cyclicity is encoded as cycle-type-plus-fixed-points count equal to one.

Proof: We formalize the plane-permutation transposition and reflection bijections of
Chen and Reidys, arXiv:1502.07674, lines 786-1074, and their specialization to Zagier's
recurrence, lines 1167-1370. A generating-polynomial coefficient identity supplies the
matching Stirling recurrence; descending induction on the cycle count finishes.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Card perm cycle Count eq stirling First](../part-08/stirling/card-perm-cycle-count-eq-stirling-first.md)
- [Cycle Quotient Count](../part-08/stirling/cycle-quotient-count.md)
- [Cycle Quotient Count eq](../part-08/stirling/cycle-quotient-count-eq.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.ZagierCyclicPermutationProduct](../../../../../../sources/v2/MathlibExt.md)
- R. Cori and G. Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of Integer Sequences 28 (2025), Article 25.3.3, Theorem [Zagier], lines 351-359, <https://cs.uwaterloo.ca/journals/JIS/VOL28/Hetyei/hetyei2.tex>, quoting D. Zagier.
