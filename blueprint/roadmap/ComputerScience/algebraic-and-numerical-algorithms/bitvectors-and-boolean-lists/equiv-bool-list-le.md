# Little-endian Boolean lists are equivalent to bitvectors

Let $n$ be a natural number. The map sending a width-$n$ binary word $x = \sum_{i=0}^{n-1} x_i 2^i$ (with $x_i \in \{0, 1\}$) to its little-endian bit list $(x_0, \dots, x_{n-1})$ is a bijection from the set of width-$n$ words, i.e. the natural numbers below $2^n$, onto the set of Boolean lists of length exactly $n$. Its inverse sends a list $(b_0, \dots, b_{n-1})$ to the word $\sum_{i=0}^{n-1} b_i 2^i$, reading true as $1$ and false as $0$.
