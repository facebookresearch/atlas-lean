# Rod cutting with reconstruction

Given a price vector $p$ of length $n$ with entries in an
additive commutative monoid carrying a linear order, where entry $\ell - 1$ is the price of a
piece of length $\ell$, first run the extended bottom-up rod-cutting algorithm to obtain the saved
first cuts $s_1, \dots, s_n$ (with $s_j$ stored as entry $j - 1$ of its cut vector). Then,
starting from the remaining length $L = n$, repeatedly emit a piece of length $s_L$ and replace
$L$ by $L - s_L$ until $L = 0$. The result is the composition of $n$ formed by the emitted pieces
in order. Its cost is the cost of the extended algorithm plus one event per emitted piece;
allocation and arithmetic are free.
