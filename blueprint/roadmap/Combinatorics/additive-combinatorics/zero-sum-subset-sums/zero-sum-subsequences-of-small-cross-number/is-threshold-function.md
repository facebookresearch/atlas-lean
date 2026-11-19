# Threshold functions

Let $P : \mathbb{N} \times \mathbb{N} \to \mathbb{R}$, where
$P(k, s)$ is read as the probability of an event in the $k$-th space when $s$ random elements
are chosen. A function $t : \mathbb{N} \to \mathbb{R}$ is a *threshold function* for $P$ if
$t(k) > 0$ for all sufficiently large $k$ and, for every function $f : \mathbb{N} \to \mathbb{N}$,
$P(k, f(k)) \to 1$ as $k \to \infty$ whenever $t = o(f)$, and $P(k, f(k)) \to 0$ as
$k \to \infty$ whenever $f = o(t)$.

The source's thresholds are positive functions; since little-o ignores sign, without the
positivity condition $-t$ would be a threshold function whenever $t$ is.

## Sources

- Neal Bushaw and Glenn Hurlbert, *Thresholds for Zero-Sums with Small Cross Numbers in Abelian Groups*, INTEGERS 24 (2024), Article A93, Section 1.1 (definition of a threshold and of `τ(G)`).
