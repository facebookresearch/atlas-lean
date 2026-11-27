# Cole's paradox: annual and perennial growth rates

Consider breeding once a year, with no mortality at any age, maturity at age $1$ and unlimited lifespan, as in Cole's (1954) analysis. A semelparous annual producing $B$ offspring and then dying has annual growth factor $\lambda = B$. An iteroparous perennial producing $b > 0$ offspring every year from age $1$ on has growth factor given by the discrete Euler–Lotka equation $\sum_{x \ge 1} b\lambda^{-x} = 1$; for $\lambda > 1$ the sum is $b/(\lambda - 1)$, so the root is $\lambda = b + 1$. Hence an annual with $B = b + 1$ offspring grows exactly as fast as an immortal perennial with $b$: in Cole's words, changing to the perennial habit is "exactly equivalent to adding one individual to the average litter size" (for example, $b = 3$ offspring a year for ever against one litter of $B = 4$). This is Cole's paradox (Cole 1954).

## Depends on

- [Discrete Euler–Lotka equation](../../leslie-matrix-model/sum-fertility-mul-survivorship-div-pow-e.md)

## Expansion

1. The two life histories as Leslie-type models without mortality, and their growth factors.
2. The geometric series $\sum_{x \ge 1} b\lambda^{-x} = b/(\lambda - 1)$ for $\lambda > 1$, and the root $\lambda = b + 1$.
3. The equality of growth rates for $B = b + 1$.
4. The resolution with juvenile survival $c$ and adult survival $p$ (Charnov and Schaffer 1973): the annual grows by $cB$ and the perennial by $cb + p$, so the annual must produce $B = b + p/c$, stated separately.

## Sources

- Original result: L. C. Cole, The population consequences of life history phenomena, Q. Rev. Biol. 29 (1954), 103–137. <https://doi.org/10.1086/400074>
- Original result: E. L. Charnov and W. M. Schaffer, Life-history consequences of natural selection: Cole's result revisited, Am. Nat. 107 (1973), 791–793. <https://doi.org/10.1086/282877>
