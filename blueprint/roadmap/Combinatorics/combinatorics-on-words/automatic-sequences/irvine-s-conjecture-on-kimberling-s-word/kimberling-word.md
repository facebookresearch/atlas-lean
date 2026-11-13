# Kimberling's word

Let $K_n$ be the $n$-th Kimberling block, a finite word over
$\{0, 1\}$. Kimberling's word $k = k_1 k_2 k_3 \cdots = 1101101111\cdots$ (OEIS A285431) is the
infinite word over $\{0, 1\}$ whose letter $k_{i+1}$, for $i \ge 0$, is the $(i+1)$-th letter of
$K_m$, where $m = \lfloor \log_2 i \rfloor + 1$ for $i \ge 1$ and $m = 1$ for $i = 0$. The block
$K_m$ has length at least $2^m > i$, so this letter exists.

Every block $K_n$ is a prefix of $k$, so $k$ is the common extension of the blocks.

## Sources

- Jeffrey Shallit, *Proof of Irvine's Conjecture via Mechanized Guessing*, INTEGERS 24 (2024), Article A51, Section 2 (the limit word `k`) and Section 5 (`k'_n = k_{n+1}`).
