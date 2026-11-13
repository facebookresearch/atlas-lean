# The inverse of Parisse's matrix $B(n)$

Let $n \in \mathbb{N}$. Let $e_{j,i}(n)$ be the
elementary symmetric polynomial of degree $i$ in $n + 1, \dots, n + j$, let
$b_{j,k}(n) = (-1)^k e_{j,j-k}(n)$ for $k \le j$ and $b_{j,k}(n) = 0$ for $k > j$, let
$p_{\ell,m}(x, y) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (k x + y)^\ell$ for complex $x, y$, and let
$c_{\ell,m}(n) = p_{\ell,m}(1, n + 1) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (k + n + 1)^\ell$.
Then for all $j, m \in \mathbb{N}$, with $\delta_{j,m}$ the Kronecker delta,
$\sum_{k=0}^{j} b_{j,k}(n) \, \frac{c_{k,m}(n)}{m!} = \delta_{j,m}$ and
$\sum_{k=0}^{j} \frac{c_{j,k}(n)}{k!} \, b_{k,m}(n) = \delta_{j,m}$.

In matrix form, with $B(n) = (b_{j,k}(n))$, $C(n) = (c_{\ell,m}(n))$ and $D$ the diagonal matrix
of the factorials $j!$, this says $B(n)^{-1} = C(n) D^{-1}$.

## Sources

- Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums II*, INTEGERS 26 (2026), Article A36, Corollary 1, Equation (2.9).
