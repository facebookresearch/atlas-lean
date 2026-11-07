# Interval and congruence characterization of signed power-of-two sums

Let $m \ge 1$ and
$s \le t$ be natural numbers and put $L = t - s + 1$. An integer $n$ can be written as
$\sum_{j=s}^{t} \lambda_j 2^j$ with every $\lambda_j \in \{-1, m\}$ if and only if
$-2^s (2^L - 1) \le n \le 2^s m (2^L - 1)$ and $n \equiv -2^s (2^L - 1) \pmod{2^s (m + 1)}$.

## Sources

- Ross, *A Perfect Number Generalization and Some Euclid-Euler Type Results*, JIS 27 (2024), Article 24.7.5, Lemma 7 (`jis-2024-24.7.5-lem-7`): for `0 ≤ s ≤ t` and `m ≥ 1`, the integers of the form `∑_{j=s}^{t} λⱼ * 2^j` with `λⱼ ∈ {-1, m}` are precisely the integers `n` in the interval `[-2^s * (2^{t-s+1} - 1), 2^s * m * (2^{t-s+1} - 1)]` satisfying `n ≡ -2^s * (2^{t-s+1} - 1) [ZMOD 2^s * (m + 1)]`.
