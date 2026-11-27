# Evaluating a concatenation of Boolean functions

Let $n$ and $k$ be natural numbers and $W = (W_0, \dots, W_{m-1})$ a finite list of Boolean functions on $\{0,1\}^n$; write $W_i$ for the constant function $0$ when $i \ge m$. The concatenation of $W$ on $n + k$ variables sends $(x, y)$, with $x \in \{0,1\}^n$ and $y \in \{0,1\}^k$, to $W_{\iota(y)}(x)$, where $\iota(y) = \sum_{j < k} y_j 2^j$. That is, for all $x \in \{0,1\}^n$ and $y \in \{0,1\}^k$ the concatenation evaluated at the joined vector $(x_0, \dots, x_{n-1}, y_0, \dots, y_{k-1})$ equals $W_{\iota(y)}(x)$.

## Sources

- Bartłomiej Pawelski and Andrzej Szepietowski, *Counting Self-Dual Monotone Boolean Functions*, Journal of Integer Sequences 28 (2025), Article 25.6.5.
