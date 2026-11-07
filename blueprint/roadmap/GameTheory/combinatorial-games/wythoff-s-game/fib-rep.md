# Greedy Fibonacci representation

Let $F_0 = 1$, $F_1 = 2$ and $F_{i+2} = F_{i+1} + F_i$.
The greedy Fibonacci representation $\mathrm{rep}_F(n)$ of $n \in \mathbb{N}$ is the word of
digits $d_{k-1} \cdots d_0$, most significant first, where $k$ is the least integer with
$n < F_k$ and the digits are chosen greedily: starting from the remainder $n$, for
$j = k - 1, \dots, 0$ in turn, $d_j = 1$ and $F_j$ is subtracted from the remainder if $F_j$ is
at most the remainder, and $d_j = 0$ otherwise. It has no leading zero, and
$\mathrm{rep}_F(0)$ is the empty word. The digits $1$ and $0$ are encoded as the booleans true
and false.

## Sources

- Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6, Definition `def:fib_rep`.
