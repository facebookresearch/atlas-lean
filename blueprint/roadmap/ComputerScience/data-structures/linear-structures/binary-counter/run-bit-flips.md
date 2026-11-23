# Flip counts of the individual bits

Let $k$, $i$ and $n$ be natural numbers
with $i < k$, and for each $t$ let $c_t$ be the bit vector returned by running $t$ increments
from the all-false bit vector of width $k$. Then the number of $t < n$ such that the bit at
position $i$ of $c_t$ (counting from the low-order bit, starting at $0$) differs from the bit at
position $i$ of $c_{t+1}$ is $\lfloor n / 2^i \rfloor$.
