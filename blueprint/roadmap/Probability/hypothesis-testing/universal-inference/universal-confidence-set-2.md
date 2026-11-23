# Universal confidence set with real densities

Let $p_\theta : X_0 \to \mathbb{R}$, $\theta \in \Theta$, be real functions on the inference split
(its likelihoods in the intended use), let $\hat\theta_1 : X_1 \to \Theta$ be an estimator computed
from the estimation split and let $\alpha$ be a real number. At a sample
$z = (z_0, z_1) \in X_0 \times X_1$, the universal confidence set at level $\alpha$ is

$$C_\alpha(z) = \bigl\{\theta : \alpha\, p_{\hat\theta_1(z_1)}(z_0) \le p_\theta(z_0)\bigr\} .$$

Where $p_\theta(z_0) > 0$ and $\alpha > 0$, the condition is $T(\theta) \le 1/\alpha$ for the split
likelihood ratio $T(\theta) = p_{\hat\theta_1(z_1)}(z_0) / p_\theta(z_0)$. For $\alpha > 0$ and
nonnegative $p$, a parameter with $p_\theta(z_0) = 0$ belongs to the set only if
$p_{\hat\theta_1(z_1)}(z_0) = 0$. This is the [universal confidence set](universal-confidence-set.md)
with real-valued densities and the level as a multiplier.

## Sources

- L. Wasserman, A. Ramdas and S. Balakrishnan, *Universal inference*, Proc. Natl. Acad. Sci. USA 117 (2020), equation (4).
