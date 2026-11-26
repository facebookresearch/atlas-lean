# Stopping condition for a block of size $m + 2$

Write $F_j$ for the Fibonacci numbers
($F_1 = F_2 = 1$). For $r \in \mathbb{N}$ let $Z(r)$ be the set of indices in the Zeckendorf
representation $r = \sum_{j \in Z(r)} F_j$ (all indices $\ge 2$, no two consecutive), and let
$r_j = 1$ if $j \in Z(r)$ and $r_j = 0$ otherwise. Let $\mathbb{X} \subseteq \{0,1\}^{\mathbb{N}}$
be the set of Zeckendorf-adic integers (sequences with $x_0 = x_1 = 0$ and no two consecutive
ones), and write $x + n = T^n(x)$ for the $n$-th iterate of the Zeckendorf odometer $T$. Let
$x \in \mathbb{X}$, $\ell \ge 2$ and $m \in \mathbb{N}$ with $x_i = 0$ for
$i \in \{\ell, \ell+1, \ell+2, \ell+3, \ell+2m+4, \ell+2m+5, \ell+2m+6, \ell+2m+7\}$, and let
$r$ satisfy $r_{\ell+1} = r_{\ell+2m+7} = 0$ and $r_{\ell+2i+3} = 1$ for $i = 0, \dots, m+1$.
Let $\tilde r = \sum_{j \in Z(r),\, j \le \ell} F_j$ be the part of $r$ of index at most $\ell$,
and let $S = \sum_{i=0}^{m+1} F_{\ell+2i+3}$. Then
$(x + \tilde r + S)_k = (x + \tilde r)_k = x_k$ for every $k \ge \ell + 2m + 7$, and
$(x + r)_k = (x + \tilde r + S)_k$ for every $k$ with $2 \le k \le \ell + 2m + 2$.

## Sources

- Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation: An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27 (2024), Article 24.3.2, Corollary 14 (`jis-2024-24.3.2-cor-14`).
