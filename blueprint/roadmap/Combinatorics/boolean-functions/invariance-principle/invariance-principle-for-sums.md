# Invariance principle for sums of independent random variables

Let $X_1, \dots, X_n$ and $Y_1, \dots, Y_n$ be independent real random variables in $L^3$ with $\mathbb{E}X_i = \mathbb{E}Y_i$ and $\mathbb{E}X_i^2 = \mathbb{E}Y_i^2$, and let $\gamma = \sum_i (\mathbb{E}|X_i|^3 + \mathbb{E}|Y_i|^3)$. Then:
- for every $C^3$ function $\psi$ with $|\psi'''| \le C$: $\big|\mathbb{E}\psi(\sum_i X_i) - \mathbb{E}\psi(\sum_i Y_i)\big| \le \frac{C}{6}\gamma$;
- for every $K$-Lipschitz $\psi$: the same difference is at most $cK\gamma^{1/3}$;
- the Lévy distance between $\sum_i X_i$ and $\sum_i Y_i$ is at most $c\gamma^{1/4}$;

here $c$ is a universal constant (O'Donnell, Cor. 11.59 and Cor. 11.61).

The two families need not be defined on a common probability space.

## Proof sketch

Lindeberg replacement: swap $X_i$ for $Y_i$ one at a time; Taylor-expanding $\psi$ to third order around the sum of the other variables, the first two moments cancel and the remainder is at most $\frac{C}{6}(\mathbb{E}|X_i|^3 + \mathbb{E}|Y_i|^3)$. Lipschitz and step functions are smoothed by moving averages (resp. $C^3$ ramps) at a scale optimized against $\gamma$.

## Depends on

- [Lévy distance and the hypothesis of the basic invariance principle](levy-distance-and-invariance-hypothesis.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
