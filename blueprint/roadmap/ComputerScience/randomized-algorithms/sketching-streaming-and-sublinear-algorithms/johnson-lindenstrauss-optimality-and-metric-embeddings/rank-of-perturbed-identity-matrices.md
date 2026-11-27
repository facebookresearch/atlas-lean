# Rank lower bound for perturbed identity matrices

There is an absolute constant $c > 0$ such that every real $n \times n$ matrix $B$ with $b_{ii} = 1$ for all $i$ and $|b_{ij}| \le \varepsilon$ for all $i \ne j$, where $1/\sqrt{n} \le \varepsilon < 1/2$, satisfies

$$
\operatorname{rank}(B) \ge \frac{c\,\log n}{\varepsilon^{2}\log(1/\varepsilon)}.
$$

Applied to the Gram matrix of the images of $0, e_1, \dots, e_n$ under a map with distortion $1 + \varepsilon$, this gives $m(n + 1, n, \varepsilon) = \Omega(\varepsilon^{-2}\log n/\log(1/\varepsilon))$ for $\varepsilon \ge 1/\sqrt{n}$.

## Proof sketch

First, a symmetric matrix $A$ with unit diagonal and off-diagonal entries at most $\varepsilon$ in absolute value has rank at least $n/(1 + (n-1)\varepsilon^2)$, by comparing $(\operatorname{tr} A)^2 \le \operatorname{rank}(A)\operatorname{tr}(A^2)$. Then apply this to the entrywise power $B^{\circ k}$ (symmetrized), whose rank is at most $\binom{\operatorname{rank}(B) + k - 1}{k}$ and whose off-diagonal entries are at most $\varepsilon^k$; choosing $k \approx \log n/(2\log(1/\varepsilon))$ and comparing the two bounds yields the claim.

## Depends on

- [Distortion of a metric embedding and the Euclidean dimension-reduction function](bi-lipschitz-distortion-of-metric-embeddings.md)

## Sources

- Noga Alon, "Perturbed identity matrices have high rank: proof and applications", Combin. Probab. Comput. 18 (2009).
