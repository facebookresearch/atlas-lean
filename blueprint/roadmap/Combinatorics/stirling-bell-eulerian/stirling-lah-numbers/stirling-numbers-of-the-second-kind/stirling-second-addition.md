# Addition formula for Stirling numbers of the second kind

Write $S(n,k)$ for the Stirling
numbers of the second kind. For all natural numbers $u$, $v$ and $k$ with $u > 0$,

$$S(u+v,k) = \sum_{n=1}^{k} S(u,n) \sum_{m=k-n}^{v} \binom{v}{m} S(m,k-n)\, n^{v-m},$$

where an inner sum with $k - n > v$ is empty.

The source does not state the hypothesis $u > 0$, but the formula needs it: for $u = 0$ and
$v = k = 1$ the left side is $S(1,1) = 1$, while every term on the right has the factor
$S(0,1) = 0$.

## Sources

- Grzegorz Rządkowski, "Two Formulas for Successive Derivatives and Their Applications," Journal of Integer Sequences 12 (2009), Article 09.8.2, Theorem, equation (ex33), lines 198–204, https://cs.uwaterloo.ca/journals/JIS/VOL12/Rzadkowski/rzadkowski3.tex
