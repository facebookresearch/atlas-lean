# Inclusion–exclusion for tuples with exactly $r$ coprime pairs

Let $k \ge 2$, $r \ge 0$
and $n \in \mathbb{N}^k$, and let $\beta_r(n)$ be $1$ if $n$ has exactly $r$ coprime pairs and $0$
otherwise. For a set $E$ of pairs $(a, b)$ with $0 \le a < b < k$, let $\delta_E$ be the
coprimality indicator of the graph with edge set $E$. Then, as integers,

$$\beta_r(n) = \sum_{j=r}^{k(k-1)/2} (-1)^{j-r} \binom{j}{r} \sum_{|E| = j} \delta_E(n),$$

where the inner sum runs over the $j$-element sets $E$ of such pairs.

For $r = 0$ this is the paper's identity for $\beta = \beta_0$, the indicator of pairwise
non-coprime tuples.

## Sources

- László Tóth, *On the Asymptotic Density of k-tuples of Positive Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27 (2024), Article 24.8.5, Lemma 5 (`jis-2024-24.8.5-lem-5`).
