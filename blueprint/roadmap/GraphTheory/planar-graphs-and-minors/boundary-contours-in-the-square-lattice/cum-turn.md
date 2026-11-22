# Cumulative turn along a boundary-tracing orbit

Let $K \subseteq \mathbb{Z}^2$, let $e$ be a dart of the square lattice and $k$ a natural number. Let $\sigma_K$ be the successor map on darts along the boundary of $K$, and for a dart $f$ with direction $u$ let $r = (u_1, -u_0)$ be $u$ rotated clockwise by a quarter turn and let the turn $t_K(f) \in \mathbb{Z}/4\mathbb{Z}$ be $1$ if $\mathrm{head}(f) + r \in K$, $0$ if $\mathrm{head}(f) + r \notin K$ but $\mathrm{tail}(f) + r \in K$, and $3$ otherwise. The cumulative turn over the first $k$ steps of the orbit of $e$ is

$$\sum_{i=0}^{k-1} t_K\big(\sigma_K^i(e)\big) \in \mathbb{Z}/4\mathbb{Z}.$$
