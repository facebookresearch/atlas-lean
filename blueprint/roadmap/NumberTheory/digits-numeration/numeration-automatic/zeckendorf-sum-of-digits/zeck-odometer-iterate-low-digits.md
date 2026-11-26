# Adding $r$ without low digits leaves the low digits unchanged

Write $F_j$ for the
Fibonacci numbers ($F_1 = F_2 = 1$). For $r \in \mathbb{N}$ let $Z(r)$ be the set of indices in
the Zeckendorf representation $r = \sum_{j \in Z(r)} F_j$ (all indices $\ge 2$, no two
consecutive), and let $r_j = 1$ if $j \in Z(r)$ and $r_j = 0$ otherwise. Let
$\mathbb{X} \subseteq \{0,1\}^{\mathbb{N}}$ be the set of Zeckendorf-adic integers (sequences
with $x_0 = x_1 = 0$ and no two consecutive ones), and write $x + n = T^n(x)$ for the $n$-th
iterate of the Zeckendorf odometer $T$. Let $x \in \mathbb{X}$ and $\ell \ge 2$ with
$x_\ell = x_{\ell+1} = 0$, and let $r$ satisfy $r_j = 0$ for $2 \le j \le \ell + 1$. Then
$(x + r)_n = x_n$ for every $n$ with $2 \le n \le \ell - 2$.

## Sources

- Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation: An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27 (2024), Article 24.3.2, Corollary 9 (`jis-2024-24.3.2-cor-9`).
