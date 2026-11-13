# Number of profiles with exactly $k$ soulmate pairs

For natural numbers $n$ and $k$, the
number $F(k, n)$ of preference profiles for $n$ men and $n$ women with exactly $k$ soulmate pairs
is

$$
\binom{n}{k}^2 k!\, ((n-1)!)^{2k}
\sum_{i=0}^{n-k} (-1)^i \binom{n-k}{i}^2 ((n-1)!)^{2i}\, i!\, (n!)^{2(n-k-i)}.
$$

When $k > n$ both sides are $0$.

The sum is the paper's $S(k, n)$ of Lemma 4, which counts the preferences of the people outside
the $k$ soulmate couples that create no further soulmate pair.

## Sources

- Borodin et al., *Sequences of the Stable Matching Problem*, Journal of Integer Sequences 27 (2024), Article 24.2.2, Theorem 6 (`jis-2024-24.2.2-thm-6`).
