# Zeckendorf decomposition as a game state

Index the Fibonacci numbers as $F_1 = 1$,
$F_2 = 2$ and $F_{i+1} = F_i + F_{i-1}$, and record a game state as a finitely supported
function $s : \mathbb{N} \to \mathbb{N}$, where $s(i)$ is the number of copies of $F_i$. Every
$n \in \mathbb{N}$ has a unique Zeckendorf decomposition $n = F_{i_1} + \cdots + F_{i_r}$ with
$r \ge 0$, indices $i_1, \dots, i_r \ge 1$ and $i_t \ge i_{t+1} + 2$ for $1 \le t < r$. The
Zeckendorf state of $n$ is the game state with one copy of each $F_{i_t}$: $s(i) = 1$ if
$i \in \{i_1, \dots, i_r\}$ and $s(i) = 0$ otherwise.

## Sources

- Diego Garcia-Fernandezsesma, Steven J. Miller, Thomas Rascon, Risa Vandegrift, and Ajmain Yamin, *The Accelerated Zeckendorf Game*, The Fibonacci Quarterly 62 (2024), no. 1, Article milleretal04072023, Section 1.1 and Theorem 1.3.
