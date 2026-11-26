# The codes of the negative parts follow an orbit of addition modulo a Fibonacci number

Let $n \ge 1$, write $F_k$ for the Fibonacci numbers and $L_k$ for the Lucas numbers, and let
$c$ be a function from the natural numbers to the natural numbers such that
$c(N) = \sum_{i \in S,\, i < 0} F_{i+2n}$ (with $F_k$ read as $0$ for $k < 0$) whenever $S$ is a
base phi expansion of $N$. List the values $c(N)$ for $N = L_{2n-1} + 1, \dots, L_{2n+1}$ (the
interval $\Xi_n$) in increasing order of $N$, and merge every run of equal consecutive values
into a single entry. The resulting list is $(F_{2n} - 1 + j F_{2n-2}) \bmod F_{2n}$ for
$j = 0, 1, \dots, F_{2n} - 1$: the orbit of $F_{2n} - 1$ under addition of $F_{2n-2}$ in
$\mathbb{Z}/F_{2n}\mathbb{Z}$.

Here $c(N)$ is the paper's code $C(N)$ of the negative part $\beta^-(N)$ (the digits of $N$ at
negative positions), and the merged runs are its tridents.

## Sources

- F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24 (2024), Article A24, Theorem 11.
