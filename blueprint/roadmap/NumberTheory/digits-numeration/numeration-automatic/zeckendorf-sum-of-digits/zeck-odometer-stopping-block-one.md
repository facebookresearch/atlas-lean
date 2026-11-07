# Stopping condition for a block of size one

Write $F_j$ for the Fibonacci numbers
($F_1 = F_2 = 1$). For $r \in \mathbb{N}$ let $Z(r)$ be the set of indices in the Zeckendorf
representation $r = \sum_{j \in Z(r)} F_j$ (all indices $\ge 2$, no two consecutive), and let
$r_j = 1$ if $j \in Z(r)$ and $r_j = 0$ otherwise. Let $\mathbb{X} \subseteq \{0,1\}^{\mathbb{N}}$
be the set of Zeckendorf-adic integers (sequences with $x_0 = x_1 = 0$ and no two consecutive
ones), and write $x + n = T^n(x)$ for the $n$-th iterate of the Zeckendorf odometer $T$. Let
$x \in \mathbb{X}$ and $\ell \ge 2$ with $x_i = 0$ for $\ell \le i \le \ell + 5$, and let $r$
satisfy $r_{\ell+1} = r_{\ell+5} = 0$ and $r_{\ell+3} = 1$. Let
$\tilde r = \sum_{j \in Z(r),\, j \le \ell} F_j$ be the part of $r$ of index at most $\ell$. Then
$(x + \tilde r + F_{\ell+3})_k = (x + \tilde r)_k = x_k$ for every $k \ge \ell + 4$, and
$(x + r)_k = (x + \tilde r + F_{\ell+3})_k = (x + \tilde r)_k$ for every $k$ with
$2 \le k \le \ell + 2$.

## Sources

- Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation: An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27 (2024), Article 24.3.2, Corollary 12 (`jis-2024-24.3.2-cor-12`).
