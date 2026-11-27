# Pătraşcu's succincter rank and select

For every $t \ge 1$, on a RAM with cells of $\Omega(\log n)$ bits, an array of $n$ bits can be stored in $n + n / \left(\frac{\log n}{t}\right)^{t} + \tilde{O}(n^{3/4})$ bits so that rank and select queries take $O(t)$ time. More generally, an array of $u$ bits containing $n$ ones fits in $\log_2 \binom{u}{n} + u/\left(\frac{\log u}{t}\right)^t + \tilde{O}(u^{3/4})$ bits with the same query time.

## Proof sketch

A *spill-over representation* stores a value as some memory bits plus a *spill* from a small universe that is kept by an outside entity. Blocks of the array are encoded as memory bits plus a spill; the spills of $B$ consecutive blocks are combined into a new spill-over representation of $O(w)$ memory bits and a new spill, and so on recursively for $t$ levels. Each level absorbs the slack of the level below, so only the final spills cost a bit of redundancy each, and a query decodes one root-to-leaf path in $O(t)$ steps using precomputed tables of $\tilde{O}(n^{3/4})$ bits.

## Depends on

- [Succinct rank with a probe budget](succinct-rank-tradeoff-problem.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- Mihai Pătraşcu, "Succincter", FOCS (2008).
