# Membership in a range report

Let $t$ be a range tree satisfying the bounds-correctness
predicate: every node has two subtrees with at least one leaf each and caches the least and the
greatest leaf value of its subtree. For all integers $a$, $b$ and $x$, the value $x$ occurs in the
range report of $t$ for $[a, b]$ if and only if $x$ is a leaf value of $t$ and $a \le x \le b$.
