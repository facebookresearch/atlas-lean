# Ailon-Chazelle fast Johnson-Lindenstrauss transform via randomized Hadamard preconditioning

Let $0 < \varepsilon < 1$, let $p \in \{1, 2\}$ and $k = \Theta(\varepsilon^{-2}\log n)$, and work in Ailon and Chazelle's regime: $d = 2^m$ is a power of $2$ with $k < d \le n$ and $d = \Omega(\varepsilon^{-1/2})$ (Ailon and Chazelle assume this without loss of generality: zero padding makes $d$ a power of $2$, and outside this regime the target dimension $k$ is not smaller than linear in $d$). Let $H$ be the $d \times d$ Walsh–Hadamard matrix scaled by $d^{-1/2}$, let $D$ be a diagonal matrix of independent uniform signs, and let $P$ be a $k \times d$ matrix whose entries are independently $0$ with probability $1 - q$ and otherwise Gaussian with variance $1/q$, where $q = \min\{\Theta(\varepsilon^{p-2}\log^p n/d), 1\}$ for the target norm $\ell_p$. Set $\Phi = PHD$. For every set $X \subset \mathbb{R}^d$ of $n$ vectors, with probability at least $2/3$ every $x \in X$ satisfies $(1 - \varepsilon)\alpha_p\|x\|_2 \le \|\Phi x\|_p \le (1 + \varepsilon)\alpha_p\|x\|_2$ for a normalizing factor $\alpha_p$ depending only on $p$ and $k$; applied to the differences of an $n$-point set (with $\log n$ replaced by $\log n^2$), $\Phi/\alpha_p$ embeds it into $\ell_p^k$ with distortion $(1 + \varepsilon)/(1 - \varepsilon)$. The expected time to compute $\Phi x$ is

$$
O\big(d\log d + \min\{d\,\varepsilon^{-2}\log n, \; \varepsilon^{p-4}\log^{p+1} n\}\big) \quad (p = 1, 2),
$$

for instance $O(d\log d + \varepsilon^{-2}\log^3 n)$ for $\ell_2$.

## Proof sketch

$HD$ is an isometry computed by the fast Walsh–Hadamard transform in $O(d\log d)$ time. For a unit vector $x$, each coordinate of $HDx$ is a Rademacher sum with coefficients $\pm x_i/\sqrt{d}$, so Hoeffding's inequality and a union bound over the $nd \le n^2$ coordinates (here $d \le n$ is used) give $\|HDx\|_\infty = O(\sqrt{\log n/d})$ for all $x \in X$ with probability at least $19/20$. On such flattened vectors the sparse Gaussian matrix $P$ behaves like a dense Gaussian projection: each coordinate of $Px$ is a Gaussian mixture whose variance concentrates, and a moment-generating-function computation shows that $\|Px\|_p$ deviates from its mean by a factor outside $1 \pm \varepsilon$ with probability $e^{-\Omega(\varepsilon^2 k)}$, small enough for a union bound over $X$ at $k = \Theta(\varepsilon^{-2}\log n)$; the expected number of nonzeros of $P$ gives the running time.

## Depends on

- [Distortion of a metric embedding and the Euclidean dimension-reduction function](bi-lipschitz-distortion-of-metric-embeddings.md)
- [Hadamard matrix](../../../../LinearAlgebra/special-matrices/hadamard-matrices/is-hadamard-matrix.md)

## Proof depends on

- [Hoeffding's inequality for averages of bounded variables](../../../../Probability/concentration-inequalities/hoeffding-s-inequality/measure-real-avg-sub-ge-le.md)

## Sources

- Nir Ailon, Bernard Chazelle, "Approximate Nearest Neighbors and the Fast Johnson-Lindenstrauss Transform", STOC (2006); SIAM J. Comput. 39 (2009), Section 2 and Lemma 1.
