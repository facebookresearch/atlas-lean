# One FFT butterfly

For a commutative ring $R$, an element $\omega \in R$, vectors
$q, r \in R^m$, a state $(w, y)$ with $w \in R$ and $y \in R^{2m}$, and an index $k < m$, the
butterfly at $k$ returns the state $(w \omega, y')$, where $y'$ is obtained from $y$ by setting
entry $k$ to $q_k + w r_k$ and entry $k + m$ to $q_k - w r_k$, at a time cost of $8$.
