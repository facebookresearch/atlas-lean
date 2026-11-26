# Number of overlap-add blocks

For natural numbers $N$ and $L$, the number of blocks of hop $L$ covering a signal of length $N$ is

$$B(N, L) = \left\lfloor \frac{N + L - 1}{L} \right\rfloor,$$

with natural-number subtraction and $\lfloor n / 0 \rfloor = 0$. For $L \ge 1$ this is $\lceil N / L \rceil$.
