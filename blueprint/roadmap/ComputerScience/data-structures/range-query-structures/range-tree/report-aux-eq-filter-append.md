# Accumulator range report of a bounds-valid range tree

Let $t$ be a bounds-valid range
tree, let $a$ and $b$ be integers and let $\mathit{acc}$ be a list of integers. Then the
accumulator range report of $t$ for $[a, b]$ starting from $\mathit{acc}$ is the list of the leaf
values $x$ of $t$ with $a \le x \le b$, in left-to-right order and with repetitions, followed by
$\mathit{acc}$.
