# The semicircle distribution is determined by its moments

Let $\nu$ be a finite measure on $\mathbb{R}$ such that $x \mapsto x^{2k}$ is $\nu$-integrable for
every $k$, and suppose that $\int x^k \, d\nu = \int x^k \, d\sigma$ for every $k \in \mathbb{N}$,
where $\sigma$ is the semicircle distribution. Then $\nu = \sigma$.

This is the uniqueness step of the moment method: once
$\frac{1}{n}\mathbb{E}\operatorname{tr}(W_n/\sqrt{n})^k$ is shown to converge to the moments of
$\sigma$, any limit law must be $\sigma$. Proof: the even moments of $\nu$ are the Catalan numbers
$C_k \le 4^k$, which by Markov's inequality confines $\nu$ to $[-2, 2]$; two measures supported in
a common compact interval with the same moments are equal.

## Informally uses

- [The even moments of the semicircle distribution are the Catalan numbers](integral-pow-two-mul-semicircle-real.md):
  the moments that $\nu$ is assumed to share.

## Sources

- T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, American Mathematical Society, 2012, §2.4.2 and §2.2.3 (the moment method).
