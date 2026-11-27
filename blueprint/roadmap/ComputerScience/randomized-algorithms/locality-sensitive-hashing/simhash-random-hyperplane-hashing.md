# Charikar's SimHash collision law

Let $E$ be a finite-dimensional real inner product space and draw $r$ from the standard Gaussian measure on $E$. SimHash maps $u \in E$ to the bit $[\langle u, r\rangle \ge 0]$. For nonzero $u, v$ with angle $\theta(u, v) \in [0, \pi]$,

$$
\Pr_r\bigl[\mathrm{sign\ bits\ of\ } u, v \text{ agree}\bigr] = 1 - \frac{\theta(u, v)}{\pi},
$$

which is $1 - \arccos\langle u, v\rangle/\pi$ for unit vectors. Hence SimHash is $(\theta_1, \theta_2, 1 - \theta_1/\pi, 1 - \theta_2/\pi)$-sensitive for the angular distance on nonzero vectors, and $(1 - \arccos s_1/\pi,\, 1 - \arccos s_2/\pi)$-sensitive for cosine similarity on unit vectors (near: similarity at least $s_1$; far: at most $s_2$). The same holds with i.i.d. standard normal coordinates in Euclidean space.

## Proof sketch

The bits disagree exactly when the threshold $0$ lies between $\langle u, r\rangle$ and $\langle v, r\rangle$, i.e. when the random hyperplane separates $u$ and $v$, which by Sheppard's formula has probability $\theta/\pi$. Sensitivity follows from monotonicity of $\theta \mapsto 1 - \theta/\pi$ and of $\arccos$.

## Depends on

- [Locality-sensitive hash families](locality-sensitive-hash-families.md)
- [A random hyperplane separates two unit vectors with probability angle over π](../../../Probability/distributions/continuous/multivariate-normal-distribution/sheppard-formula/std-gaussian-sign-ne.md)

## Proof depends on

- [A random hyperplane separates two unit vectors with probability angle over π](../../../Probability/distributions/continuous/multivariate-normal-distribution/sheppard-formula/std-gaussian-sign-ne.md)

## Sources

- M. S. Charikar, "Similarity Estimation Techniques from Rounding Algorithms", Proceedings of the 34th ACM Symposium on Theory of Computing, 2002.
