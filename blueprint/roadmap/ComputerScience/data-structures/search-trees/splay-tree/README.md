# Splay tree

A splay tree is a binary search tree that, after every access, moves the accessed node to the
root by splaying. Its amortized analysis uses a sum-of-logs potential built from arbitrary
positive item weights: the access lemma bounds the amortized cost of a splay by
$3 \log_2 (W / s(x)) + 1$, and the potential method turns it into bounds on access sequences,
the balance theorem (unit weights) and static optimality (weights equal to the access
frequencies) (Sleator and Tarjan, *Self-adjusting binary search trees*, J. ACM 32(3) (1985)).

- [Root key of a splay tree](root.md)
- [Splay operation](splay.md)
- [Splaying the empty tree](splay-nil.md)
- [Splaying preserves the inorder traversal](inorder-splay.md)
- [Splaying preserves membership](mem-splay.md)
- [Splaying preserves the number of nodes](num-nodes-splay.md)
- [Splaying preserves the search-tree property](ordered-splay.md)
- [Splaying a present key brings it to the root](root-splay-of-mem.md)
- [Root key after splaying a present key](root-splay-of-mem-2.md)
- [Search-path split at a key](split.md)
- [Splay-tree split parts contain only original keys](mem-of-mem-split.md)
- [Keys other than the split key survive a split](mem-split-of-mem.md)
- [Splitting an ordered tree separates the keys around the split key](all-split.md)
- [Both parts of a split search tree are search trees](ordered-split.md)
- [Splay-tree insertion](insert.md)
- [Splay-tree access](access.md)
- [Splay-tree membership test](contains.md)
- [The tree returned by a splay-tree access](access-snd.md)
- [Keys after splay-tree insertion](mem-insert.md)
- [Splay-tree insertion preserves the search-tree property](ordered-insert.md)
- [Splay-tree insertion puts the inserted key at the root](root-insert.md)
- [Correctness of the splay-tree membership test](contains-eq-true-iff.md)
- [Splay-tree potential](potential.md)
- [Number of rotations performed by splaying](rotations.md)
- [Cost of a splay](cost.md)
- [Subtree at the end of the search path](focus.md)
- [Access lemma for splay trees (unit weights)](access-lemma.md)
- [Amortized cost of a splay is at most $3 \log_2 n + 1$](amortized-cost-le.md)
- [The splay-tree potential is nonnegative](potential-nonneg.md)
- [Upper bound on the splay-tree potential](potential-le.md)
- [Trees of a run of splays](splay-run.md)
- [Splaying preserves the number of nodes along a run](num-nodes-splay-run.md)
- [Balance theorem for splay trees](balance-theorem.md)
- [Weight of a binary tree](weight.md)
- [Weighted splay-tree potential](potential-w.md)
- [Unit weights give the number of nodes](weight-one.md)
- [Unit-weight potential is the splay-tree potential](potential-eq-potential-w-one.md)
- [Splaying preserves the weight of a tree](weight-splay.md)
- [Access lemma for splay trees](access-lemma-weighted.md)
- [In a search tree the search for a present key ends at its node](focus-eq-node-of-mem.md)
- [Amortized cost of accessing a present key](amortized-cost-le-weighted.md)
- [Splay-tree access bound for arbitrary weights](access-sequence-le-weighted.md)
- [Access frequency](access-count.md)
- [Static optimality of splay trees](static-optimality.md)

## Related topics

- [Amortized analysis](../../amortized-analysis/README.md): the potential method used for the
  balance theorem and static optimality.
- [Binary search tree](../binary-search-tree/README.md): the underlying tree, inorder traversal
  and search-tree invariant.
- [Link-cut tree](../../disjoint-sets-and-dynamic-trees/link-cut-tree/README.md): Sleator and
  Tarjan's dynamic trees, whose amortized analysis uses splaying.
