# Majorization bounds on homozygosity given the most frequent allele

Let $p = (p_1, p_2, \dots)$ be allele frequencies at a locus, nonnegative, summing to $1$, finitely many nonzero, ordered $p_1 \ge p_2 \ge \cdots$, with largest frequency $M = p_1 \in (0,1]$. Write $\lfloor \cdot \rfloor$, $\lceil \cdot \rceil$ for floor and ceiling, $\{x\} = x - \lfloor x \rfloor$, and $K = \lceil 1/M \rceil$. For $f : [0,\infty) \to \mathbb R$ continuous and convex with $f(0) = 0$ and $f \ge 0$ on $[0,1]$, set $F(p) = \sum_i f(p_i)$.

1. **Unrestricted number of alleles.** If $M < 1$ and $F$ is bounded on frequency vectors, then

$$f(M) \le F(p) \le \lfloor 1/M \rfloor\, f(M) + f\bigl(\{1/M\}\, M\bigr),$$

with equality in the upper bound for $p = (M, \dots, M, 1 - (K-1)M, 0, \dots)$ ($K - 1$ entries equal to $M$).
2. **At most $I$ alleles.** If $p$ has length $I \ge 2$ and $1/I \le M \le 1$, then

$$f(M) + (I-1)\, f\Bigl(\frac{1 - M}{I - 1}\Bigr) \le F(p) \le \lfloor 1/M \rfloor\, f(M) + f\bigl(\{1/M\}\, M\bigr),$$

the lower bound attained at $p = \bigl(M, \tfrac{1-M}{I-1}, \dots, \tfrac{1-M}{I-1}\bigr)$.
3. **$\alpha$-homozygosity.** For $J_\alpha(p) = \sum_i p_i^\alpha$ with $\alpha > 1$,

$$M^\alpha \le J_\alpha(p) \le \lfloor 1/M \rfloor M^\alpha + \bigl(\{1/M\}\, M\bigr)^\alpha,$$

with equality above iff $p = (M,\dots,M, 1 - \lfloor 1/M \rfloor M, 0, \dots)$ and below iff $M = 1$. For $\alpha = 2$ (homozygosity $J$) the upper bound equals $1 - M(K - 1)(2 - KM)$, and with $I$ alleles the lower bound is $J \ge \dfrac{IM^2 - 2M + 1}{I - 1}$, attained iff $p_i = (1-M)/(I-1)$ for $i \ge 2$.

## Expansion

A vector $v$ majorizes $w$ ($v \succ w$) if they have the same sum and the partial sums of their decreasing rearrangements satisfy $\sum_{i \le k} v_{[i]} \ge \sum_{i \le k} w_{[i]}$ for all $k$. By Karamata's inequality, $v \succ w$ implies $\sum f(v_i) \ge \sum f(w_i)$ for convex $f$, i.e. $F$ is Schur-convex (Schur–Ostrowski criterion). Among vectors with first entry $M$ and entries at most $M$, the greedy vector $(M, \dots, M, 1 - (K-1)M, 0, \dots)$ majorizes every other one, while $(M, \tfrac{1-M}{I-1}, \dots)$ is majorized by every vector of length $I$ with first entry $M$; this gives the bounds in items 1–2. Without a length bound the remaining mass $1 - M$ can be spread arbitrarily thinly. The lower bound $F(p) \ge f(M)$ holds because $f \ge 0$ on $[0,1]$ makes every tail term $f(p_i)$, $i \ge 2$, nonnegative; the superadditivity estimate $f(\sum x_i) \ge \sum f(x_i)$, which follows from convexity and $f(0) = 0$, bounds the tail from above, $\sum_{i \ge 2} f(p_i) \le f(1 - M)$. When moreover $f'(0^+) = 0$, as for $f(x) = x^\alpha$ with $\alpha > 1$, spreading the remaining mass thinly drives $\sum_{i \ge 2} f(p_i)$ to $0$, so $f(M)$ is the infimum, approached but (for $M < 1$) not attained; without that condition the bound need not be sharp (for $f(x) = x$, $F \equiv 1 > f(M)$). Item 3 is the case $f(x) = x^\alpha$; for $\alpha = 2$ this recovers the earlier bounds on homozygosity as a function of the most frequent allele, both for an unrestricted and for a fixed number of alleles.

## Sources

- A. J. Aw, N. A. Rosenberg, "Bounding measures of genetic similarity and diversity using majorization", *Journal of Mathematical Biology* (2018), Sections 2–3 (Definition 2.2, Theorems 2.3, 2.5, 3.1, 3.2, Lemma 3.3, Corollary 3.5, Theorems 3.8–3.9), <https://doi.org/10.1007/s00285-018-1226-x> (PMC6133051).
