# Amplification of locality-sensitive families by banding

Draw $rb$ hash functions independently from a family $\mathcal{H}$, group them into $b$ bands of $r$, and declare $x$ and $y$ a candidate pair if for some band all $r$ functions agree on $x$ and $y$. If a single function collides on the pair with probability $s$, the pair becomes a candidate with probability $1 - (1 - s^r)^b$. This is a multi-table candidate-generation scheme with $b$ hash tables, one keyed by each band, rather than a single hash family, since agreement in at least one band is not an equivalence relation. Since $s \mapsto 1 - (1 - s^r)^b$ is increasing on $[0, 1]$, for a $(d_1, d_2, p_1, p_2)$-sensitive family every pair at distance at most $d_1$ becomes a candidate with probability at least $1 - (1 - p_1^r)^b$, and every pair at distance at least $d_2$ with probability at most $1 - (1 - p_2^r)^b$.

## Depends on

- [Locality-sensitive hash families](locality-sensitive-hash-families.md)

## Sources

- J. Leskovec, A. Rajaraman and J. D. Ullman, *Mining of Massive Datasets*, 2nd ed., Cambridge University Press, 2014
