# Randomized-threshold and random-grid rounding lemmas

1. (Threshold rounding.) For $a < b$ and a threshold $\theta$ uniform in $[a, b)$, and real $x_1, x_2$, the bits $[x_1 \ge \theta]$ and $[x_2 \ge \theta]$ differ exactly when $\theta$ lies between $x_1$ and $x_2$, hence with probability at most $|x_1 - x_2|/(b-a)$ (Impagliazzo, Lei, Pitassi and Sorrell, proof of Lemma 3.3: a threshold chosen uniformly from an interval lands in a given subinterval with probability proportional to its width).
2. (Random grid rounding.) For $w > 0$, round $x$ to the midpoint of its cell in the grid of width $w$ shifted by an offset uniform in $[0, w)$. Every rounded value is within $w/2$ of $x$, and $x_1, x_2$ fall in different cells exactly when some shifted grid point lies between them, hence with probability at most $|x_1 - x_2|/w$ (Impagliazzo, Lei, Pitassi and Sorrell, Algorithm 1 (rSTAT) and proof of Theorem 2.3).

## Proof sketch

For the threshold, the set of $\theta$ separating $x_1$ and $x_2$ is an interval of length at most $|x_1 - x_2|$. For the grid, the offsets placing a grid point between $x_1$ and $x_2$ form a set of measure at most $|x_1 - x_2|$ in $[0, w)$.

Derived (not stated in the cited source, which uses continuous thresholds and offsets): with $\theta_i = a + (b-a)i/N$ for $i$ uniform in $\{0, \dots, N-1\}$, the bits differ with probability at most $|x_1 - x_2|/(b-a) + 1/N$, since at most $N|x_1-x_2|/(b-a) + 1$ of the $N$ grid thresholds lie between $x_1$ and $x_2$. With the shift $iw/N$ for $i$ uniform in $\{0, \dots, N-1\}$, rounded values stay within $w/2$ of $x$ and $x_1, x_2$ fall in different cells with probability at most $|x_1 - x_2|/w + 1/N$, counting shifts with Hermite's identity for sums of floors.

## Depends on

- [Replicable algorithms with shared randomness](replicable-algorithms-with-shared-seed.md)

## Sources

- R. Impagliazzo, R. Lei, T. Pitassi and J. Sorrell, "Reproducibility in Learning", Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing (STOC), 2022, Algorithm 1, proof of Theorem 2.3 and proof of Lemma 3.3; open copy: <https://arxiv.org/abs/2201.08430>.
