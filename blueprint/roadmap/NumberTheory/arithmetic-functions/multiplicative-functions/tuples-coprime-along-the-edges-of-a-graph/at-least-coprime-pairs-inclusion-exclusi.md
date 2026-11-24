# Inclusion–exclusion for at least $r$ coprime pairs

Let $k \ge 2$ and $r \ge 1$, and let
$n = (n_1, \dots, n_k)$ be a tuple of natural numbers (zero allowed). Let $\beta'_r(n)$ be $1$ if
$\gcd(n_a, n_b) = 1$ for at least $r$ pairs $a < b$, and $0$ otherwise. For a set $E$ of pairs
$(a, b)$ with $1 \le a < b \le k$, let $\delta_E(n)$ be $1$ if $\gcd(n_a, n_b) = 1$ for every
$(a, b) \in E$, and $0$ otherwise. Then

$$\beta'_r(n) = \sum_{j=r}^{k(k-1)/2} (-1)^{j-r} \binom{j-1}{r-1} \sum_{|E| = j} \delta_E(n),$$

where the inner sum runs over all sets $E$ of exactly $j$ such pairs.

## Sources

- László Tóth, *On the Asymptotic Density of k-tuples of Positive Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27 (2024), Article 24.8.5, Lemma 6 (`jis-2024-24.8.5-lem-6`).
