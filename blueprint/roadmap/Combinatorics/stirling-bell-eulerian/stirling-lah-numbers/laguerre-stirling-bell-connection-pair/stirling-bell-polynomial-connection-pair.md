# Laguerre–Stirling–Bell connection pair

Let $\alpha$, $\beta$ and $x$ be real numbers, and
let $n$ and $r$ be natural numbers. Write $\binom{k}{j}$ for the binomial coefficients, $c(n,k)$
for the unsigned Stirling numbers of the first kind, $S(n,k)$ for the Stirling numbers of the
second kind, and $y^{\overline{m}} = y(y+1)\cdots(y+m-1)$ for the rising factorial. For natural
numbers $m$, $s$ and real $y$, let $B_m(y) = \sum_{l=0}^{m} S(m,l)\, y^l$ be the Bell polynomial
and

$$L_{m,s}(y) = \sum_{k=0}^{m} \frac{1}{k!} \sum_{j=0}^{k} (-1)^{k-j} \binom{k}{j}
(\alpha s + \beta j)^{\overline{m}}\, y^k$$

the generalized Laguerre polynomial. Then

$$L_{n,r}(x) = \sum_{k=0}^{n} \sum_{j=0}^{k} c(n,k) \binom{k}{j} (\alpha r)^{k-j} \beta^j B_j(x)$$

and

$$\sum_{k=0}^{n} (-1)^{n-k} S(n,k)\, L_{k,r}(x) =
\sum_{k=0}^{n} \binom{n}{k} (\alpha r)^{n-k} \beta^k B_k(x).$$

## Sources

- Mark Shattuck, "Combinatorial Properties of a Generalized Class of Laguerre Polynomials," Journal of Integer Sequences 24 (2021), Article 21.2.1, Theorem (label `eqnpair`), equations (labels `eqnpaire1`) and (`eqnpaire2`), lines 330–339, https://cs.uwaterloo.ca/journals/JIS/VOL24/Shattuck/shattuck24.tex
