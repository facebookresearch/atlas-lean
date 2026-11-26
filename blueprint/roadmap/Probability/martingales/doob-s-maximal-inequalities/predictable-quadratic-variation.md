# Predictable quadratic variation

Let $\mu$ be a measure on $\Omega$, let
$(\mathcal{F}_k)_{k \in \mathbb{N}}$ be a filtration and let $(f_k)_{k \in \mathbb{N}}$ be a
real-valued process. The predictable quadratic variation of $f$ with respect to
$(\mathcal{F}_k)$ and $\mu$ is the process defined pointwise by
$A_n(\omega) = \sum_{k=0}^{n-1} \mathbb{E}_\mu[(f_{k+1} - f_k)^2 \mid \mathcal{F}_k](\omega)$,
so $A_0 = 0$. For a square-integrable martingale this is the predictable part of $f^2$ in Doob's
decomposition.
