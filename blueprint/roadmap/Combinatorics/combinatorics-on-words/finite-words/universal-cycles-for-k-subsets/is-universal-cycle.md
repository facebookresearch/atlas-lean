# Universal cycle for $k$-subsets

For natural numbers $n$ and $k$, let $N = \binom{n}{k}$.
A sequence $c_0, \dots, c_{N-1}$ of elements of $\{0, \dots, n-1\}$, read cyclically, is a
universal cycle for the $k$-subsets of $\{0, \dots, n-1\}$ when, for every starting position
$i < N$, the $k$ consecutive entries $c_i, c_{i+1}, \dots, c_{i+k-1}$ (indices taken modulo $N$)
are pairwise distinct, and every $k$-element subset of $\{0, \dots, n-1\}$ is the set of these
entries for exactly one starting position $i$.

## Sources

- Fan Chung, Persi Diaconis and Ron Graham, *Universal cycles for combinatorial structures*, Discrete Mathematics 110 (1992), 43–59.
- Listed in Cooper, *Combinatorial Problems I Like*, section Words and Codes, problem 78.
