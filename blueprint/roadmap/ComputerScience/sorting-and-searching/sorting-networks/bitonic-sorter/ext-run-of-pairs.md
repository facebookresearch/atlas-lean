# Transported comparator lists agree with the original on Boolean inputs

Let
$N \in \mathbb{N}$ and let $P$ be a list of comparators on natural-number-indexed wires, each of
which joins two wires below $N$. For every Boolean input $v$ on the wires $0, \dots, N - 1$, run
the network on $N$ wires obtained from $P$ on $v$ and extend its output by $\mathrm{false}$ to
all wires in $\mathbb{N}$; the result equals the result of running $P$ on the extension of $v$ by
$\mathrm{false}$.
