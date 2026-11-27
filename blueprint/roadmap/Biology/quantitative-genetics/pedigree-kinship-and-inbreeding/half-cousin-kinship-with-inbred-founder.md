# Every kinship coefficient is realized by half cousins with an inbred founder

Members $a, b$ of a pedigree are half cousins with separation $m$ and founder inbreeding $f$ if they are joined by a single non-collapsing pedigree path of length $m$ whose top-most member has inbreeding coefficient $f$, with no other relationship or inbreeding among the path members (Definition 1); $m = 0$ means $a = b$ and $m = \infty$ means unrelated. For finite $m$,

$$\phi_{ab} = \frac{1 + f}{2^{m+1}}. \tag{7}$$

**Theorem** (Theorem 2 of the source). Every $\phi \in [0, 1]$ is the kinship coefficient of some half-cousin relationship with inbred founder. For $\phi \in (0,1)$ one may take $m = \lfloor \log_2(1/\phi) \rfloor$ and $f = 2^{m+1}\phi - 1$; $\phi = 1$ uses $(m, f) = (0, 1)$ and $\phi = 0$ uses $m = \infty$ with the founder coefficient $f$ arbitrary, since unrelated individuals have kinship $0$ whatever $f$ is (so $(\infty, 0)$ and $(\infty, 1)$ both work). For $\phi > 0$ the pair $(m, f)$ is unique except when $\phi = 2^{-k}$ with $k \ge 1$, where $(k-1, 0)$ and $(k, 1)$ both work.

**Stationary inbreeding** (Proposition 5). For each $m \in \mathbb N_0$ the map $f \mapsto (1 + f)/2^{m+1}$ has a unique fixed point $f^* \in (0, 1]$, namely $f^* = 1/(2^{m+1} - 1)$; half cousins of separation $m$ whose founder has inbreeding $f^*$ have kinship $f^*$, so a child of theirs again has inbreeding $f^*$. For $m = 2$ (half siblings) $f^* = 1/7$.

## Depends on

- [Kinship coefficient by Malécot's recursion](kinship.md)
- [Inbreeding coefficient under gene dropping](inbreeding.md)

## Proof depends on

- [Wright's path formula for kinship](kinship-eq-sum-paths.md)

## Expansion

Equation (7) is Wright's path formula with a single path of $m + 1$ individuals through the common ancestor. For fixed $m$, $f \mapsto (1 + f)/2^{m+1}$ maps $[0, 1]$ bijectively onto $[2^{-(m+1)}, 2^{-m}]$, and these intervals cover $(0, 1]$ as $m$ runs over $\mathbb N_0$; adjacent intervals share only the endpoints $2^{-k}$. The construction hides all infinite breeding in the founder's assigned inbreeding coefficient, so it does not by itself show that an individual with arbitrary $f$ exists; the source proves that separately (Theorem 3) with a possibly infinite chain of half-cousin relationships built from the binary expansion of $\phi$.

## Sources

- M. D. Vigeland, Relatedness coefficients in pedigrees with inbred founders, Journal of Mathematical Biology 81 (2020), 185-207. <https://doi.org/10.1007/s00285-020-01505-x> (PMCID PMC7363742)
