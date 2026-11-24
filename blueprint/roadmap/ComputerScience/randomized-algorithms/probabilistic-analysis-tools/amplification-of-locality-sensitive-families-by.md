# Amplification of locality-sensitive families by banding

Draw $rb$ hash functions independently from a family $\mathcal{H}$, group them into $b$ bands of $r$, and declare $x$ and $y$ a candidate pair if for some band all $r$ functions agree on $x$ and $y$. If a single function collides on the pair with probability $s$, the pair becomes a candidate with probability $1 - (1 - s^r)^b$. Since $s \mapsto 1 - (1 - s^r)^b$ is increasing on $[0, 1]$, a $(d_1, d_2, p_1, p_2)$-sensitive family becomes $(d_1, d_2, 1 - (1 - p_1^r)^b, 1 - (1 - p_2^r)^b)$-sensitive.

## Depends on

- [Locality-sensitive hash families](locality-sensitive-hash-families.md)

## Sources

- J. Leskovec, A. Rajaraman and J. D. Ullman, *Mining of Massive Datasets*, 3rd ed., Cambridge University Press, 2020
