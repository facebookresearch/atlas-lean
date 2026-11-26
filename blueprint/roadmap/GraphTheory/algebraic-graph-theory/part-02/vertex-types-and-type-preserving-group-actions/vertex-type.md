# Type of a vertex relative to a base vertex

Let $\mathcal{T}$ be a simple graph on a vertex set $W$ and let $w_0 \in W$ be a base vertex. The type of a vertex $w$ relative to $w_0$ is the parity of the graph distance from $w_0$ to $w$, as an element of $\mathbb{Z}/2\mathbb{Z}$:

$$\operatorname{type}_{w_0}(w) = d_{\mathcal{T}}(w_0, w) \bmod 2,$$

where $d_{\mathcal{T}}(w_0, w)$ is the length of a shortest walk from $w_0$ to $w$, taken to be $0$ when $w$ is not reachable from $w_0$ (so such $w$ have type $0$).
