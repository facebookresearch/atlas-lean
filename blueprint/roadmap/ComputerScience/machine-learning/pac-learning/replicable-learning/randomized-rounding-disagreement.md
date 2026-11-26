# Randomized-threshold and random-grid rounding lemmas

1. (Threshold rounding.) For $a < b$ and $N \ge 1$, let $\theta_i = a + (b-a)i/N$ for $i$ uniform in $\{0, \dots, N-1\}$. For real $x_1, x_2$, the bits $[x_1 \ge \theta_i]$ and $[x_2 \ge \theta_i]$ differ with probability at most $|x_1 - x_2|/(b-a) + 1/N$; with a threshold uniform in $[a, b)$ the bound is $|x_1 - x_2|/(b-a)$.
2. (Random grid rounding.) For $w > 0$ and $N \ge 1$, round $x$ to the midpoint of its cell in the grid of width $w$ shifted by $iw/N$, $i$ uniform in $\{0, \dots, N-1\}$. Every rounded value is within $w/2$ of $x$, and $x_1, x_2$ fall in different cells with probability at most $|x_1 - x_2|/w + 1/N$; with a continuous uniform shift the bound is $|x_1 - x_2|/w$.

## Proof sketch

The bits differ exactly when a threshold falls between $x_1$ and $x_2$; at most $N|x_1-x_2|/(b-a) + 1$ of the $N$ grid thresholds do. For the grid, $x_1$ and $x_2$ are separated exactly when a shifted grid point lies between them; counting shifts uses Hermite's identity for sums of floors.

## Depends on

- [Replicable algorithms with shared randomness](replicable-algorithms-with-shared-seed.md)

## Sources

- R. Impagliazzo, R. Lei, T. Pitassi and J. Sorrell, "Reproducibility in Learning", Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing (STOC), 2022.
