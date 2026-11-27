# Correctness of the range report

Let $t$ be a range tree satisfying the bounds-correctness
predicate: every node has two subtrees with at least one leaf each and caches the least and the
greatest leaf value of its subtree. For all integers $a$ and $b$, the range report of $t$ for
$[a, b]$ equals the list of leaf values $x$ of $t$ with $a \le x \le b$, in left-to-right order.
