# Balanced aggregation trees for dynamic prefix sums on the Word RAM

For $n = 2^h$, a complete binary tree whose leaves are $A_0, \dots, A_{n-1}$ and whose internal nodes store the sums of their subtrees, laid out in preorder in $2n - 1$ contiguous words, supports $\mathrm{sum}(\ell)$ (adding the left siblings along the path to leaf $\ell$) and $\mathrm{add}(i, \delta)$ (updating the path from the root to leaf $i$). A word-RAM program performs both operations in $O(\log n)$ instructions each, provided all sums fit in a word, and modifies no memory outside the tree.

## Proof sketch

Both operations follow a single root-to-leaf path determined by the bits of the index, doing constant work per level; a prefix query adds the stored total of each left subtree it passes, and an update adds $\delta$ to every node on the path.

## Depends on

- [Dynamic prefix sums problem](dynamic-prefix-sums.md)
- [The word-RAM model](../../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- P. M. Fenwick, "A New Data Structure for Cumulative Frequency Tables", Software: Practice and Experience 24(3), pp. 327-336, 1994.
- M. Patrascu and E. D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4), pp. 932-963, 2006.
