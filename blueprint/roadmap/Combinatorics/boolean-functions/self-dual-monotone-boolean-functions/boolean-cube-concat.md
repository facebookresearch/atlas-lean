# Concatenation of a list of Boolean functions

Let $n$ and $k$ be natural numbers and let
$W = (W_0, W_1, \dots, W_{m-1})$ be a finite list of Boolean functions on $n$ variables. The
concatenation $W_0 \cdot W_1 \cdots W_{m-1}$ on $n + k$ variables is the Boolean function that
sends $(x_0, \dots, x_{n-1}, y_0, \dots, y_{k-1})$ to $W_i(x_0, \dots, x_{n-1})$, where
$i = \sum_{j < k} y_j 2^j$ is the number whose binary digits are the last $k$ variables (true
counted as $1$ and false as $0$), and to false when $i \ge m$.

## Sources

- Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5, the concatenation representation of `D_n^{B^k}` before Theorem 10.
