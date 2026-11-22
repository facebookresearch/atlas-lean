# Characterization of Motzkin humps

Write a path of length $n$ as a sequence of steps
$p_0, \dots, p_{n-1}$, and let $s(p_r) \in \{-1, 0, 1\}$ be the vertical displacement of the
step $p_r$ (down, flat or up). For a natural number $k$ and positions $i, j < n$, the pair
$(i, j)$ is a hump of height $k$ if and only if $i < j$, $s(p_i) = 1$, $s(p_j) = -1$,
$s(p_r) = 0$ for every $r$ with $i < r < j$, and $\sum_{r \le i} s(p_r) = k$.

## Sources

- Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal of Integer Sequences 28 (2025), Article 25.8.1, Section 1 (definitions).
