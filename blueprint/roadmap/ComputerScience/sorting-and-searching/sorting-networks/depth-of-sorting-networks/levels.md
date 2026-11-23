# Comparator levels under earliest scheduling

Given a list of comparators on
$\mathbb{N}$-indexed wires, each a pair $(i, j)$ of wires, and a starting level $\ell(x)$ for
every wire $x$, process the comparators in order, keeping a current level for each wire, initially
$\ell$: a comparator $(i, j)$ whose wires currently have levels $a$ and $b$ sets the current levels
of both wires $i$ and $j$ to $\max(a, b) + 1$ and leaves every other level unchanged. The result
is the level of each wire after all the comparators, that is, when each comparator runs as early
as possible, one level after the later of its two wires.
