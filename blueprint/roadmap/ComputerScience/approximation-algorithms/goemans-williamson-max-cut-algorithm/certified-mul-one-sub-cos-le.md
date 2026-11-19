# The Goemans–Williamson inequality with a certified constant

For every $\theta \in [0, \pi]$,

$$0.878565 \cdot \frac{1 - \cos \theta}{2} \le \frac{\theta}{\pi}.$$

The proof follows Goemans and Williamson's proof of Lemma 3.5. On $[0, \pi/2]$ the chord bound
$1 - \cos\theta \le 2\theta/\pi$ gives the stronger inequality with constant $1$. On
$[\pi/2, \pi]$ the function $1 - \cos$ is concave, so it lies below its tangent at
$\theta_0 = \pi - \varphi$; with $\varphi = 0.810472$, just to the right of
$\pi - 2.331122\ldots$, the tangent has negative intercept, which gives
$1 - \cos\theta \le \theta \sin\varphi$ and then the claim, because
$0.878565 \cdot \pi \sin \varphi \le 2$. The values of $\sin\varphi$ and $\cos\varphi$ are certified by
Taylor bounds of degree up to $9$, and $\pi$ by rational bounds to 20 digits. The constant is within $3 \times 10^{-6}$ of the true value
$0.8785672\ldots$ of $\alpha$.

## Sources

- M. X. Goemans and D. P. Williamson, "Improved approximation algorithms for maximum cut and satisfiability problems using semidefinite programming", *J. ACM* 42(6) (1995), 1115–1145 (journal version), proof of Lemma 3.5 (p. 1122).
