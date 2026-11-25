# Coverage of the universal confidence set with real densities

Let $X_0$ and $X_1$ be measurable spaces, $\nu_0$ an s-finite measure on $X_0$ and $\nu$ a probability
measure on $X_1$. Let $p_\theta : X_0 \to \mathbb{R}$, $\theta \in \Theta$, satisfy $p_\theta \ge 0$
and $\int p_\theta \, d\nu_0 \le 1$ for every $\theta$, let $\hat\theta_1 : X_1 \to \Theta$ and
$\theta^* \in \Theta$, and suppose that $p_{\theta^*}$ and the split likelihood ratio
$z \mapsto p_{\hat\theta_1(z_1)}(z_0) / p_{\theta^*}(z_0)$ (read as $0$ where
$p_{\theta^*}(z_0) = 0$) are measurable. Then for every $\alpha > 0$,

$$\bigl(p_{\theta^*} \nu_0 \otimes \nu\bigr)\bigl(\{z : \theta^* \notin C_\alpha(z)\}\bigr) \le \alpha ,$$

where $C_\alpha(z) = \{\theta : \alpha\, p_{\hat\theta_1(z_1)}(z_0) \le p_\theta(z_0)\}$ is the
universal confidence set. When moreover $\int p_{\theta^*} \, d\nu_0 = 1$, the measure
$p_{\theta^*} \nu_0 \otimes \nu$ is the law of an independent pair $(z_0, z_1)$ with $z_0$ of density
$p_{\theta^*}$ and $z_1 \sim \nu$, and the bound says that the true parameter lies outside the set
with probability at most $\alpha$. Unlike
[the finite-sample validity of the universal confidence set](measure-not-mem-universal-confidence-set.md),
the densities are real-valued and only $p_{\theta^*}$ and the split likelihood ratio are assumed
measurable.

## Sources

- L. Wasserman, A. Ramdas and S. Balakrishnan, *Universal inference*, Proc. Natl. Acad. Sci. USA 117 (2020), Theorem 1.
