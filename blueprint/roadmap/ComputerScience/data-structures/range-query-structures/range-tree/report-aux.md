# Accumulator range report

For integers $a$, $b$ and a list $\mathit{acc}$ of integers, the
accumulator range report of a range tree for $[a, b]$ starting from $\mathit{acc}$ is defined by
recursion on the tree. The empty tree returns $\mathit{acc}$. A leaf with value $x$ returns $x$
followed by $\mathit{acc}$ if $a \le x \le b$, and $\mathit{acc}$ otherwise. A node with cached
interval $[l, h]$ returns $\mathit{acc}$ if $h < a$ or $b < l$; otherwise, if $a \le l$ and
$h \le b$, it returns the node's leaf values from left to right followed by $\mathit{acc}$;
otherwise it returns the report of the left child starting from the report of the right child
starting from $\mathit{acc}$.

The cached bounds make each pruning test constant-time.
