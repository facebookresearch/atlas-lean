# Faulhaber-type summation formula for Bernoulli polynomials

Let $B_i$ denote the
$i$-th Bernoulli number, with $B_1 = -1/2$, and let
$B_j(X) = \sum_{i=0}^{j} \binom{j}{i} B_i X^{j-i} \in \mathbb{Q}[X]$ be the $j$-th Bernoulli
polynomial. For all natural numbers $k$ and $n$, the following identity holds in $\mathbb{Q}[X]$:

$$\sum_{j=1}^{n} B_k(X + j) = \frac{1}{k+1} \sum_{r=0}^{k} \binom{k+1}{r+1}
\left(B_{r+1}(n+1) + (-1)^r B_{r+1}\right) B_{k-r}(X).$$

## Sources

- Claudio de J. Pita Ruiz V., *Carlitz-Type and Other Bernoulli Identities*, Journal of Integer Sequences 19 (2016), Article 16.1.8, <https://cs.uwaterloo.ca/journals/JIS/VOL19/Pita/pita23.tex>, Proposition [Faulhaber-type formula], equation (5.32), lines 1001-1007.
