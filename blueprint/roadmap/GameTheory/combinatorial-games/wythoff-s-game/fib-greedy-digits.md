# Greedy Fibonacci digits

Let $F_0 = 1$, $F_1 = 2$ and $F_{i+2} = F_{i+1} + F_i$. For
$k, n \in \mathbb{N}$, the greedy digits of $n$ at positions $k - 1, \dots, 0$ are the list of
$k$ digits, most significant first, computed with a remainder $r$ that starts at $n$: for
$j = k - 1, \dots, 0$ in turn, the digit at position $j$ is $1$ if $F_j \le r$, in which case
$F_j$ is subtracted from $r$, and $0$ otherwise. The digits $1$ and $0$ are encoded as the
booleans true and false.

## Sources

- Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026), Article 26.1.6, Definition `def:fib_rep` (greedy representation).
