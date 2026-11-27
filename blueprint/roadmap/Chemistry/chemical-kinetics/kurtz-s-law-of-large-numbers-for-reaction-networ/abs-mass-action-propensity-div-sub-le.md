# A c/N bound for scaled mass-action propensities on bounded sets

Let $G$ be a [chemical reaction network](../../../Dynamics/smooth-dynamics/reaction-network.md) with
finite species set $S$ and reaction set $\rho$, let $\kappa \in \mathbb{R}^\rho$ be any real rate
constants (nonnegative in the model), $r$ a reaction with source complex $k = \mathrm{src}(r)$, and
$R$ real. There is a real constant $c$, depending on $G$, $\kappa$, $r$ and $R$ but not on $N$ or
$z$, such that for every natural number $N \ge 1$ and every $z \in \mathbb{N}^S$ whose
[scaled state](scaled.md) has sup norm $\|z/N\|_\infty \le R$,

$$\left|\frac{\lambda^N_r(z)}{N} - \kappa_r \prod_{s \in S} \left(\frac{z_s}{N}\right)^{k_s}\right|
\le \frac{c}{N},$$

where $\lambda^N_r$ is the [stochastic mass-action propensity](mass-action-propensity.md) at system
size $N$ and the product is the
[mass-action rate](../../../Biology/systems-biology/complex-balancing-and-the-deficiency-zero-theore/rate.md)
of $r$ at $z/N$. So the scaled propensities converge to the mass-action rates uniformly on bounded
sets of scaled states, with error $O(1/N)$. For $R < 0$ no $z$ qualifies. The proof takes
$c = |\kappa_r|\, |S|\, |k|^2 M^{|k| (|S| + 1)}$, where $|k| = \sum_s k_s$, $|S|$ is the number of
species and $M = \max(R, 0) + |k| + 1$.
