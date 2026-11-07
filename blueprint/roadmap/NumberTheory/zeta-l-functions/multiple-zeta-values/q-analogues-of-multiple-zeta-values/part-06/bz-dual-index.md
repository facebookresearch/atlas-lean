# Bradley–Zhao dual index

For an index $k = (k_1, \dots, k_r)$ of natural numbers, form the
word $x^{k_1 - 1} y \cdots x^{k_r - 1} y$ in two letters $x$ and $y$ (each $k_i - 1$ truncated at
$0$); when all $k_i \ge 1$ this is $z_{k_1} \cdots z_{k_r}$ with $z_k = x^{k-1} y$. Apply the
anti-automorphism $\tau$ of words with $\tau(x) = y$ and $\tau(y) = x$, which reverses a word and
swaps its letters, and write the result as $x^{n_1} y \cdots x^{n_s} y \, x^e$. The BZ dual index
of $k$ is $(n_1 + 1, \dots, n_s + 1)$; the trailing $x^e$ is dropped. For an admissible index
($k_1 \ge 2$ and all $k_i \ge 1$, or empty) $e = 0$, so the dual index is the index of
$\tau(z_{k_1} \cdots z_{k_r})$.

Equivalently, it is the SZ dual index of $(k_1 - 1, \dots, k_r - 1)$ with every entry increased
by one.

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Theorem 7 (BZ duality, the map `τ`).
