# Linear-probing scan with a probe budget

Let $S$ be the set of occupied cells of a cyclic table of $N$ cells $0, \dots, N - 1$. Starting at
cell $h$, this counts the consecutive occupied cells $h, h + 1, h + 2, \dots$ (indices modulo $N$)
met before the first empty cell, examining at most a given number of cells (the budget). The
recursion is on the budget; the [displacement](displacement.md) uses the budget $N$.
