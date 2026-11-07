# Hoey–Sloane transition of a digit pair

For natural numbers $n$ and $b$ and a pair
$e = (d_1, d_2)$ of natural numbers, the multi-edge of the $(n, b)$-Hoey–Sloane multigraph
carrying the label $e$ is $(c_1, c_2)$, where $c_1 = \lambda(d_1 + (b - n) d_2)$ with
$\lambda$ the least non-negative residue modulo $b$ (computed in the integers), and
$c_2 = \lfloor (n d_2 - d_1 + c_1) / b \rfloor$, replaced by $0$ when negative. For $b = 0$
the conventions are $x \bmod 0 = x$ and $x / 0 = 0$, and $c_1$ is likewise replaced by $0$
when negative.

For an edge $e$ of the $(n, b)$-mother graph with $1 < n < b$, the source shows that
$(c_1, c_2)$ is the unique solution of $b c_2 - c_1 = n d_2 - d_1$ with
$0 \le c_1, c_2 \le n - 1$, that is, the transition of the Hoey–Sloane machine with input $e$.

## Sources

- Benjamin V. Holt, *A Multigraph Characterization of Permutiple Strings*, INTEGERS 25 (2025), Article A111, Definition 6 and the proof of Theorem 6.
