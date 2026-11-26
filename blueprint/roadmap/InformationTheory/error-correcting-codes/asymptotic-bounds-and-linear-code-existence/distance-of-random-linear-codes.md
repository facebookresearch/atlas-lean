# Random linear codes have distance near the Gilbert-Varshamov bound with high probability

Let $H_2(\delta) = -\delta\log_2\delta - (1-\delta)\log_2(1-\delta)$ be the binary entropy in bits. Let $k, n, d, t \in \mathbb{N}$ with $2d \le n$ and $k + t \le n\,(1 - H_2(d/n))$. If $G$ is a uniformly random $k \times n$ matrix over $\mathbb{F}_2$, then with probability greater than $1 - 2^{-t}$ the linear code $\{x G : x \in \mathbb{F}_2^k\}$ has every two distinct messages encoded at Hamming distance at least $d$ (in particular $G$ has full rank $k$ and the code has minimum distance at least $d$).

## Proof sketch

For a fixed nonzero $x$, the map $G \mapsto xG$ is additive and onto, so $xG$ is uniform on $\mathbb{F}_2^n$. Hence it has weight below $d$ with probability at most $\mathrm{Vol}_2(n, d-1)/2^n \le 2^{-n(1 - H_2(d/n))}$ by the entropy bound on the ball volume. A union bound over the $2^k - 1$ nonzero messages gives failure probability below $2^{k - n(1 - H_2(d/n))} \le 2^{-t}$.

## Depends on

- [Linear code](../linear-codes/linear-code.md)
- [Minimum distance](../linear-codes/min-dist.md)

## Proof depends on

- [Volume of a Hamming ball, entropy upper bound](../bounds-on-code-size/sum-choose-mul-pow-le-exp.md)
- [Gilbert–Varshamov bound for linear codes](../bounds-on-code-size/exists-linear-code-finrank-eq.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
