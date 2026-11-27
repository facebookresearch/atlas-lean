# Ailon-Chazelle fast Johnson-Lindenstrauss transform via randomized Hadamard preconditioning

Let $d$ be a power of $2$, let $H$ be the $d \times d$ Walsh–Hadamard matrix scaled by $d^{-1/2}$, let $D$ be a diagonal matrix of independent uniform signs, and let $P$ be a $k \times d$ matrix whose entries are independently $0$ with probability $1 - q$ and otherwise Gaussian with variance $1/q$, where $q = \min\{\Theta(\log^2 n/d), 1\}$. Set $\Phi = PHD$. For every $n$-point set $X \subset \mathbb{R}^d$, $0 < \varepsilon < 1$ and $k = \Theta(\varepsilon^{-2}\log n)$, with probability at least $2/3$ the map $x \mapsto k^{-1/2}\Phi x$ embeds $X$ into $\ell_2^k$ with distortion $1 + \varepsilon$; a variant embeds into $\ell_1^k$ with $k = \Theta(\varepsilon^{-2}\log n)$. The expected time to compute $\Phi x$ is

$$
O\big(d\log d + \min\{d\,\varepsilon^{-2}\log n, \; \varepsilon^{p-4}\log^{p+1} n\}\big) \quad (p = 1, 2),
$$

for instance $O(d\log d + \varepsilon^{-2}\log^3 n)$ for $\ell_2$.

## Proof sketch

$HD$ is an isometry computed by the fast Walsh–Hadamard transform in $O(d\log d)$ time. For a unit vector $x$, each coordinate of $HDx$ is a Rademacher sum with coefficients $\pm x_i/\sqrt{d}$, so Hoeffding's inequality and a union bound give $\|HDx\|_\infty = O(\sqrt{\log(nd)/d})$ for all difference vectors with high probability. On such flattened vectors the sparse Gaussian matrix $P$ behaves like a dense Gaussian projection: each coordinate of $Px$ is a Gaussian mixture whose variance concentrates, and a moment computation shows $\|Px\|_p$ concentrates within $1 \pm \varepsilon$ with failure probability $n^{-3}$; the expected number of nonzeros of $P$ gives the running time.

## Depends on

- [Distortion of a metric embedding and the Euclidean dimension-reduction function](bi-lipschitz-distortion-of-metric-embeddings.md)
- [Hadamard matrix](../../../../LinearAlgebra/special-matrices/hadamard-matrices/is-hadamard-matrix.md)

## Proof depends on

- [Hoeffding's inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- Nir Ailon, Bernard Chazelle, "Approximate Nearest Neighbors and the Fast Johnson-Lindenstrauss Transform", STOC (2006); SIAM J. Comput. 39 (2009).
