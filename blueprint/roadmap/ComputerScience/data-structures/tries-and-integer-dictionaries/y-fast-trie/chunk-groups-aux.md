# Fuel-bounded chunking

Given a bound $B$, a fuel $n$ and a list $l$ of $w$-bit keys, the
fuel-bounded chunking is the empty list of chunks when $n = 0$ or $l$ is empty; otherwise it is
the chunk formed by the first $\min(B, |l|)$ elements of $l$, followed by the fuel-bounded
chunking with bound $B$ and fuel $n - 1$ of the remaining elements of $l$.
