# Pătraşcu's succincter rank and select

For every $t \ge 1$, rank and select queries on an $n$-bit array can be answered in $O(t)$ time on the word RAM with $w = \Theta(\log n)$ using $n + n / \left(\frac{\log n}{t}\right)^{t} + \tilde{O}(n^{3/4})$ bits of space.

## Proof sketch

Group the array into blocks and encode each block's popcount together with the block contents using an arithmetic-coding style *spillover* representation, so that the information-theoretic slack from all blocks is aggregated recursively in a tree of fan-out $\Theta(\log n / t)$ and depth $t$. Each level of the tree loses only a $1/(\log n/t)$ fraction of the remaining redundancy, and a query decodes one root-to-leaf path in $O(t)$ steps using lookup tables of $\tilde{O}(n^{3/4})$ bits.

## Depends on

- [Succinct rank with a probe budget](succinct-rank-tradeoff-problem.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- Mihai Pătraşcu, "Succincter", FOCS (2008).
