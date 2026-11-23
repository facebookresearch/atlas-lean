# Lucas tilings

Write $\Lambda_k = [\ell_k, h_k]$ for the Lucas interval with left end
$\ell_k$ and right end $h_k$. For natural numbers $a$, $b$ and a list $P$ of pairs $(k, t)$ of
natural numbers, $P$ is a Lucas tiling of $[a, b]$ when the translated Lucas intervals
$\Lambda_k + t$, $(k, t) \in P$, taken in the order of $P$, are adjacent and their union is
$[a, b]$. Precisely, it is defined by recursion on $P$: the empty list is a Lucas tiling of
$[a, b]$ exactly when $a = b + 1$, and the list consisting of $(k, t)$ followed by $P$ is a Lucas
tiling of $[a, b]$ exactly when $\ell_k + t = a$ and $P$ is a Lucas tiling of $[h_k + t + 1, b]$.

## Sources

- F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24 (2024), Article A24, Section 4 ("a union of adjacent translations" of Lucas intervals).
