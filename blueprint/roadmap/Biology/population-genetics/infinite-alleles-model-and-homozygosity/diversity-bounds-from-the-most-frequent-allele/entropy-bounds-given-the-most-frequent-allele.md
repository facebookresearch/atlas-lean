# Rényi entropy bounds given the most frequent allele

Let $p = (p_1, \dots, p_I)$ be allele frequencies at a locus with a fixed number $I \ge 2$ of allele classes, $p_1 \ge \cdots \ge p_I \ge 0$, $\sum_i p_i = 1$, and largest frequency $M = p_1 \in [1/I, 1]$. Let $K = \lceil 1/M \rceil$ and define the extremal vectors

$$t = \bigl(\underbrace{M, \dots, M}_{\lfloor 1/M \rfloor},\ 1 - M\lfloor 1/M \rfloor,\ 0, \dots, 0\bigr), \qquad u = \Bigl(M, \frac{1-M}{I-1}, \dots, \frac{1-M}{I-1}\Bigr).$$

**Theorem.** For the Rényi entropy $H_\alpha(p) = \frac{1}{1-\alpha}\log \sum_i p_i^\alpha$ of order $\alpha \in (0,1) \cup (1,\infty)$,

$$H_\alpha(t) \le H_\alpha(p) \le H_\alpha(u),$$

where

$$H_\alpha(t) = \frac{1}{1-\alpha}\log\Bigl[\lfloor 1/M \rfloor M^\alpha + \bigl(1 - M\lfloor 1/M \rfloor\bigr)^\alpha\Bigr], \qquad H_\alpha(u) = \frac{1}{1-\alpha}\log\Bigl[M^\alpha + (I-1)\Bigl(\frac{1-M}{I-1}\Bigr)^\alpha\Bigr],$$

with equality above iff $p = u$, and equality below iff $p_i = M$ for $i \le K - 1$, $p_K = 1 - (K-1)M$ and $p_i = 0$ for $i > K$ (that is, $p = t$).

For $\alpha < 1$ the upper bound needs the fixed number $I$ of classes: without it $H_\alpha$ is unbounded above for every $M < 1$. For $\alpha > 1$ it is not needed, since $\sum_i p_i^\alpha \ge M^\alpha$ gives $H_\alpha(p) \le \frac{\alpha}{\alpha-1}\log\frac1M$ for any number of classes.

## Depends on

- [Majorization bounds on homozygosity given the most frequent allele](majorization-bounds-on-homozygosity-given-the-most-frequent-allele.md)

## Expansion

Among length-$I$ frequency vectors with largest entry $M$, $t$ majorizes every vector and every vector majorizes $u$. For $\alpha > 1$, $x \mapsto x^\alpha$ is convex, so $\sum_i p_i^\alpha$ is Schur-convex and lies between its values at $u$ and $t$; the map $J \mapsto \frac{1}{1-\alpha}\log J$ is decreasing, which reverses the order. For $\alpha < 1$, $x \mapsto x^\alpha$ is concave, so $\sum_i p_i^\alpha$ is Schur-concave, and $J \mapsto \frac{1}{1-\alpha}\log J$ is increasing. In both cases the concentrated vector $t$ minimizes $H_\alpha$ and the even vector $u$ maximizes it, and strict convexity or concavity gives the equality cases. For small $I$, the bounds tie $H_\alpha$ tightly to $M$, so entropy-based and homozygosity-based diversity comparisons across loci are partly driven by the most frequent allele.

## Sources

- A. J. Aw, N. A. Rosenberg, "Bounding measures of genetic similarity and diversity using majorization", *Journal of Mathematical Biology* (2018), Section 3 (Theorem 3.9, Eqs. 3.11–3.12 and 3.17–3.18, Corollary 3.19), <https://doi.org/10.1007/s00285-018-1226-x> (PMC6133051).
