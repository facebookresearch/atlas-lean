# Correctness of Fenwick tree range sums

Let $t$ be a Fenwick tree representing a list
$a = (a_0, \dots, a_{n-1})$ of elements of an additive commutative group. Then for all natural
numbers $\mathit{lo}$ and $\mathit{hi}$, the range sum of $t$ over $[\mathit{lo}, \mathit{hi})$
equals $\sum_{\mathit{lo} \le i < \min(\mathit{hi}, n)} a_i$; in particular it is $0$ when
$\mathit{hi} \le \mathit{lo}$.
