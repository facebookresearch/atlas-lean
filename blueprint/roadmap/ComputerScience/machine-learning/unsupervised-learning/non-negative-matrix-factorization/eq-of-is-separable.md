# Essential uniqueness of NMF when both factors are separable

Let $k$ be a finite index set, $X$ a real $m \times n$ matrix, and suppose $X = W H$ with
$W \in \mathbb{R}^{m \times k}$ and $H \in \mathbb{R}^{k \times n}$, where $W$ has a pure row for
every factor ($W^\top$ is [separable](is-separable.md): for each $a$ a row $i$ with
$W_{i\cdot} = e \, e_a^\top$, $e > 0$) and $H$ has a pure column for every factor ($H$ is
separable). Then every factorization $X = W' H'$ with $W', H' \ge 0$ entrywise and the same inner
dimension agrees with $(W, H)$ up to a permutation $\sigma$ of $k$ and positive scalings $d$ of
the factors: $W'_{ia} = d_a W_{i \sigma(a)}$ and $H'_{aj} = d_a^{-1} H_{\sigma(a) j}$ for all
$i, a, j$. The signs of $W$ and $H$ are not used. Proof: the anchor rows and columns of $X$ form a
positive diagonal block, so the matching block of $W'$ is a nonnegative matrix with a nonnegative
inverse, hence [monomial](exists-perm-of-mul-eq-one.md).
