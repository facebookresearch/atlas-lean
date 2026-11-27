# Fenwick tree range sum

For a Fenwick tree $t$ over an additive commutative group and
natural numbers $\mathit{lo}$ and $\mathit{hi}$, the range sum of $t$ over
$[\mathit{lo}, \mathit{hi})$ is $0$ if $\mathit{hi} \le \mathit{lo}$, and otherwise the prefix sum
of length $\mathit{hi}$ of $t$ minus the prefix sum of length $\mathit{lo}$ of $t$.

When $t$ represents a list, this is the sum of its entries with indices in
$[\mathit{lo}, \mathit{hi})$. This is the only Fenwick tree operation that needs additive
inverses.
