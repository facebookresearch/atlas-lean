# Existential heap assertion

For a function $p$ assigning a heap assertion $p(n)$ to each
natural number $n$ (an address or a value), the assertion $\exists n,\ p(n)$ holds of a store $s$
and a heap $h$ exactly when $p(n)$ holds of $s$ and $h$ for some natural number $n$.
