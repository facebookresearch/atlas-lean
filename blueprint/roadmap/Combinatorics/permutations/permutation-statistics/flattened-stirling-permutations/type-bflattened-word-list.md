# The word of a set partition of $(-n, n)$, as a list

Let $n$ be a natural number and let
$P$ be a set partition of $[-n, n] = \{-n, \dots, n\}$. For a finite set $S$ of integers let
$h(S) = \{|i| + 1 : i \in S\}$, and for a finite set $T$ of natural numbers with elements
$t_1 < \dots < t_k$ let $f(T) = t_1 t_1 t_2 t_2 \cdots t_k t_k$ and
$g(T) = t_1 t_2 t_2 \cdots t_k t_k t_1$ (both empty when $T = \emptyset$). Let $P_0$ be the set of
nonnegative elements of the block of $P$ containing $0$. Let $p_1 < \dots < p_m$ be the integers $p$
with $1 \le p \le n$ such that every positive element of the block of $P$ containing $p$ is at
least $p$ and every negative element $q$ of that block satisfies $p < -q$, and let $N_i$ and $P_i$
be the sets of negative and of positive elements of the block containing $p_i$. The list of $P$ is
the list of natural numbers

$$g(h(P_0))\, f(h(N_1))\, g(h(P_1)) \cdots f(h(N_m))\, g(h(P_m)).$$

## Sources

- Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling Permutations*, INTEGERS 24 (2024), Article A104, Proposition 1 (map `φ`), with Definition 2.
