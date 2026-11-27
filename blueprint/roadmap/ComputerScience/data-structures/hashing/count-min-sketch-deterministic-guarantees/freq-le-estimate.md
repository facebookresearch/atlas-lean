# Freq le estimate

Let $X$ be a finite universe of items with natural-number frequencies $f \colon X \to \mathbb{N}$, and let $H_0, \dots, H_{d-1}$ be $d > 0$ hash functions $X \to \mathbb{N}$. The estimate of $x$, the minimum of the counters of the buckets $H_j(x)$, is at least $f(x)$: the sketch never undercounts. This uses that the frequencies are nonnegative; with signed weights a colliding negative weight can make a counter smaller than $f(x)$.
