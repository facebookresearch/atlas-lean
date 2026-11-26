# Amortized bounds for splay-tree insertion, deletion and split

In a splay tree with $n$ keys and the unit-weight potential (sum of $\log_2$ subtree sizes), insertion, deletion and splitting at a key each have amortized cost $O(\log n)$ rotations plus a constant, and each preserves the set semantics and the search-tree order. Combined with the balance theorem, any sequence of $m$ dictionary operations starting from an empty splay tree costs $O(m \log n + m)$ in total, where $n \ge 1$ is the largest number of keys present.

## Proof sketch

Insertion splays the new leaf to the root after attaching it, raising the potential by $O(\log n)$ along the path; deletion splays the key and joins its subtrees by splaying the maximum of the left subtree. Each potential change is bounded using the access lemma with unit weights.

## Depends on

- [Splay operation](../splay-tree/splay.md)
- [Splay-tree potential](../splay-tree/potential.md)

## Proof depends on

- [Access lemma for splay trees](../splay-tree/access-lemma-weighted.md)

## Sources

- D. D. Sleator and R. E. Tarjan, "Self-Adjusting Binary Search Trees", Journal of the ACM 32(3), 1985.
