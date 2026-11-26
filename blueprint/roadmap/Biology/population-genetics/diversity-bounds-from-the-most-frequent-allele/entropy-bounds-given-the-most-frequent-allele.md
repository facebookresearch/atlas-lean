# Entropy bounds given the most frequent allele

Let $p = (p_1, \dots, p_I)$ be allele frequencies at a locus with a fixed number $I \ge 2$ of allele classes, $p_1 \ge \cdots \ge p_I \ge 0$, $\sum_i p_i = 1$, and largest frequency $M = p_1 \in [1/I, 1]$. Let $K = \lceil 1/M \rceil$ and define the extremal vectors

$$t = \bigl(\underbrace{M, \dots, M}_{\lfloor 1/M \rfloor},\ 1 - M\lfloor 1/M \rfloor,\ 0, \dots, 0\bigr), \qquad u = \Bigl(M, \frac{1-M}{I-1}, \dots, \frac{1-M}{I-1}\Bigr).$$

1. **Shannon–Weaver index** $H(p) = \sum_i p_i \log(1/p_i)$ (with $0 \log(1/0) = 0$):

$$\lfloor 1/M \rfloor\, M \log\frac1M + \bigl(1 - M\lfloor 1/M \rfloor\bigr)\log\frac{1}{1 - M\lfloor 1/M \rfloor} \;\le\; H(p) \;\le\; M \log\frac1M + (1 - M)\log\frac{I-1}{1-M}.$$

Equality above holds iff $p = u$; equality below holds iff $p_i = M$ for $i \le K - 1$, $p_K = 1 - (K-1)M$, $p_i = 0$ for $i > K$ (that is, $p = t$). If $1/M$ is an integer the lower bound is $\log(1/M)$.
2. **Rényi entropy** $H_\alpha(p) = \frac{1}{1-\alpha}\log \sum_i p_i^\alpha$ for $\alpha > 0$ ($H_1 = H$ as a limit): $H_\alpha(t) \le H_\alpha(p) \le H_\alpha(u)$, with the same equality cases.

Without a bound on the number of alleles, $H$ is unbounded above for every $M < 1$, so fixing $I$ is necessary for the upper bounds.

## Depends on

- [Majorization bounds on homozygosity given the most frequent allele](majorization-bounds-on-homozygosity-given-the-most-frequent-allele.md)

## Expansion

Among length-$I$ frequency vectors with largest entry $M$, $t$ majorizes every vector and every vector majorizes $u$. The function $x \mapsto x\log(1/x)$ is continuous, concave, nonnegative on $[0,1]$ and vanishes at $0$, so $H$ is Schur-concave and the convex-function bounds reverse: the concentrated vector $t$ minimises entropy and the even vector $u$ maximises it. For $\alpha \ne 1$, $H_\alpha$ is a decreasing (for $\alpha > 1$) or increasing (for $\alpha < 1$) transform of the Schur-convex or Schur-concave sum $\sum p_i^\alpha$, and in either case the order reverses consistently, giving $H_\alpha(t) \le H_\alpha(p) \le H_\alpha(u)$. For small $I$, the bounds tie $H$ tightly to $M$, so entropy-based and homozygosity-based diversity comparisons across loci are partly driven by the most frequent allele.

## Sources

- A. J. Aw, N. A. Rosenberg, "Bounding measures of genetic similarity and diversity using majorization", *Journal of Mathematical Biology* (2018), Section 3 (Theorem 3.9, Eqs. 3.11–3.12, Corollaries 3.16 and 3.19), <https://doi.org/10.1007/s00285-018-1226-x> (PMC6133051).
