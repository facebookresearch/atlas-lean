# Radon design entry of a basis function

For functions $\varphi_i \colon \mathbb{R}^2 \to \mathbb{R}$ (a basis indexed by $i$), a vector
$\xi \in \mathbb{R}^2$ and a real level $p$, the design entry of $\varphi_i$ is its Euclidean Radon
transform

$$a_i(\xi, p) = \int_{L} \varphi_i(y)\, d\mathcal{H}^1(y),$$

the integral of $\varphi_i$ over the set $L = \{y \in \mathbb{R}^2 : \langle y, \xi \rangle = p\}$
for the one-dimensional Hausdorff (length) measure $\mathcal{H}^1$. For $\xi \ne 0$ this set is a
line, and $p$ is its signed distance from the origin when $|\xi| = 1$. For $\xi = 0$ the set is
empty when $p \ne 0$, giving the entry $0$, and the whole plane when $p = 0$. A function that is not
integrable on the set gets the entry $0$, by the convention for the integral of a non-integrable
function.
