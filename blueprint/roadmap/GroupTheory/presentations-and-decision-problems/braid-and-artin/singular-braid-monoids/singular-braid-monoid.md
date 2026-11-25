# Singular braid monoids

For a natural number $n$, the singular braid monoid $SB_n$ is the monoid presented by the generators $\sigma_i, \sigma_i^{-1}, \tau_i$ ($1 \le i \le n - 1$) and Birman's relations: $\sigma_i\sigma_i^{-1} = \sigma_i^{-1}\sigma_i = 1$, $\sigma_i\tau_i = \tau_i\sigma_i$; $\sigma_i\sigma_j = \sigma_j\sigma_i$, $\sigma_i\tau_j = \tau_j\sigma_i$, $\tau_i\tau_j = \tau_j\tau_i$ for $|i - j| > 1$; and $\sigma_i\sigma_j\sigma_i = \sigma_j\sigma_i\sigma_j$, $\sigma_i\sigma_j\tau_i = \tau_j\sigma_i\sigma_j$ for $|i - j| = 1$ (the generators are indexed by $\{0, \dots, m - 1\}$ in the Lean, with $m = n - 1$ computed in $\mathbb{N}$, so $n = 0$ and $n = 1$ both give the trivial case).

Source: M. Bestvina, Questions in Geometric Group Theory (updated July 2004), Q 12.23 (Birman's conjecture), https://www.math.utah.edu/~bestvina/eprints/questions-updated.pdf.
