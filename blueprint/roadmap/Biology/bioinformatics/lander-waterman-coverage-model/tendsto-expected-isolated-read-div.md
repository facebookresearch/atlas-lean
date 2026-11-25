# Expected isolated reads per read tend to $e^{-2a}$ under sparsity

For every $N$, let $N$ reads have start positions on a circular genome of $G_N$ positions, with
windows $W_N$ such that $2W_N + 1 \le G_N$, and let $E_N$ be the sum over the positions of the
[normalized counts](normalized-count.md) of the start tuples in which the position holds an
[isolated read](isolated-read.md) for the window $W_N$ (the
[expected number of isolated reads](expected-isolated-read.md) for independent uniform starts).
If $N W_N / G_N \to a$ for a real number $a$ and $N / G_N \to 0$, then

$$\frac{E_N}{N} \to e^{-2a} \quad (N \to \infty).$$
