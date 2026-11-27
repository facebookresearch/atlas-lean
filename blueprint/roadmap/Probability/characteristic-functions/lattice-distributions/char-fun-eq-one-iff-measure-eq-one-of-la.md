# A characteristic function equal to one detects lattice support

Let $\mu$ be a
probability measure on $\mathbb{R}$ with characteristic function
$\varphi(t) = \int e^{itx} \, d\mu(x)$, and let $l \ne 0$ be real. Then $\varphi(l) = 1$ if and
only if $\mu$ gives mass $1$ to the lattice $\{(2\pi / l) k : k \in \mathbb{Z}\}$.

Forward direction: $\operatorname{Re} \varphi(l) = \int \cos(lx) \, d\mu(x) = 1$ forces
$\int (1 - \cos(lx)) \, d\mu(x) = 0$, hence $\cos(lx) = 1$ almost everywhere, hence
$lx \in 2\pi\mathbb{Z}$ almost everywhere. Backward direction: on the lattice the integrand
$e^{ilx}$ is identically $1$.
