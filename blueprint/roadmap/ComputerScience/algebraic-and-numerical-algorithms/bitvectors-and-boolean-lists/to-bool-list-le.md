# Little-endian bits of a bitvector

Let $n$ be a natural number and $x$ a width-$n$ binary word, that is, a natural number $0 \le x < 2^n$ with binary digits $x = \sum_{i=0}^{n-1} x_i 2^i$, $x_i \in \{0, 1\}$. Its little-endian bit list is the list of Booleans

$$(x_0, x_1, \dots, x_{n-1})$$

of length $n$, least significant digit first; for $n = 0$ it is the empty list.
