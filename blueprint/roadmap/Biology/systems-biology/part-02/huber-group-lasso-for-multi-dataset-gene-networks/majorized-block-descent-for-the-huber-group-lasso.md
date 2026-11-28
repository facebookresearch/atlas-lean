# Majorized block descent for the Huber group lasso

**Problem.** For one target gene, minimize the convex function

$$J(\mathbf b) = f(\mathbf b) + \lambda\sum_{\ell=1}^{p}\|\mathbf b_\ell\|_2, \qquad f(\mathbf b) = \sum_{j=1}^{n}\omega_j H_\delta\big(y_j - \mathbf x_j^{\mathsf T}\mathbf b\big),$$

over $\mathbf b = (\mathbf b_1^{\mathsf T},\dots,\mathbf b_p^{\mathsf T})^{\mathsf T}$ with blocks $\mathbf b_\ell \in \mathbb R^{m}$, where $\omega_j > 0$, $\lambda > 0$ and $H_\delta$ is the Huber loss ($\theta^2$ for $|\theta| \le \delta$, $2\delta|\theta| - \delta^2$ otherwise). Let $\gamma$ be the largest eigenvalue of $\sum_j\omega_j\mathbf x_j\mathbf x_j^{\mathsf T}$.

**Auxiliary function.** A function $Q(\mathbf b\mid\mathbf b^{(k)})$ is an auxiliary function for $J$ if $J(\mathbf b^{(k)}) = Q(\mathbf b^{(k)}\mid\mathbf b^{(k)})$ and $J(\mathbf b) \le Q(\mathbf b\mid\mathbf b^{(k)})$ for all $\mathbf b$. Since $H_\delta'$ is $2$-Lipschitz, $\big(H_\delta'(\theta_1) - H_\delta'(\theta_2)\big)(\theta_1 - \theta_2) \le 2(\theta_1 - \theta_2)^2$, the choice

$$Q(\mathbf b\mid\mathbf b^{(k)}) = f(\mathbf b^{(k)}) - \sum_{j=1}^{n}\omega_j H_\delta'\big(y_j - \mathbf x_j^{\mathsf T}\mathbf b^{(k)}\big)\mathbf x_j^{\mathsf T}(\mathbf b - \mathbf b^{(k)}) + 2\gamma\|\mathbf b - \mathbf b^{(k)}\|_2^2 + \lambda\sum_{\ell=1}^{p}\|\mathbf b_\ell\|_2$$

is an auxiliary function.

**Block update.** Cycling over blocks $\ell = 1,\dots,p$, with $\mathbf b^{(k)}(\ell-1)$ the vector whose first $\ell-1$ blocks are already updated, the exact minimizer of $Q$ in block $\ell$ is the group soft-threshold

$$\mathbf b_\ell^{(k+1)} = \frac{1}{4\gamma}\Big(1 - \frac{\lambda}{\|\mathbf v_\ell\|_2}\Big)_{+}\mathbf v_\ell, \qquad \mathbf v_\ell = \sum_{j=1}^{n}\omega_j H_\delta'\big(y_j - \mathbf x_j^{\mathsf T}\mathbf b^{(k)}(\ell-1)\big)\mathbf x_{j,\ell} + 4\gamma\,\mathbf b_\ell^{(k)},$$

where $\mathbf x_{j,\ell}$ is the part of $\mathbf x_j$ matching block $\ell$ and $(\cdot)_+ = \max(\cdot,0)$.

**Lemma 1 (descent).** The iterates satisfy $J(\mathbf b^{(k)}) \ge J(\mathbf b^{(k+1)})$.

**Lemma 2 (limit points are minima).** If the iterates are bounded and, along every convergent subsequence, successive differences tend to $\mathbf 0$, then every limit point $\mathbf b^\infty$ satisfies $\liminf_{\alpha\downarrow0}\big(J(\mathbf b^\infty + \alpha\boldsymbol\delta) - J(\mathbf b^\infty)\big)/\alpha \ge 0$ for every direction $\boldsymbol\delta$, i.e. it is a minimum of $J$.

**Theorem 3 (convergence).** If the data lie in a compact set and no column of the design is identically $\mathbf 0$, the iterates satisfy the sufficient-decrease inequality

$$J(\mathbf b^{(k)}) - J(\mathbf b^{(k+1)}) \ge 2\gamma\,\|\mathbf b^{(k)} - \mathbf b^{(k+1)}\|_2^2,$$

successive differences tend to $\mathbf 0$, and every limit point of $(\mathbf b^{(k)})$ minimizes $J$; the whole sequence converges when $J$ has a unique minimizer. (The source concludes convergence to the minimum point without uniqueness, which can fail: two genes with identical expression profiles give a continuum of minimizers.)

## Expansion

Majorization: $f$ has Hessian (where it exists) at most $2\sum_j\omega_j\mathbf x_j\mathbf x_j^{\mathsf T} \preceq 2\gamma I$, so $f(\mathbf b) \le f(\mathbf b^{(k)}) + \nabla f(\mathbf b^{(k)})^{\mathsf T}(\mathbf b - \mathbf b^{(k)}) + \gamma\|\mathbf b - \mathbf b^{(k)}\|_2^2$, and the coefficient $2\gamma$ in $Q$ is a valid, looser curvature bound. Block $\ell$ of $Q$ is $2\gamma\|\mathbf b_\ell\|_2^2 - \mathbf v_\ell^{\mathsf T}\mathbf b_\ell + \lambda\|\mathbf b_\ell\|_2$ up to constants; its subgradient condition $4\gamma\mathbf b_\ell + \lambda\mathbf s = \mathbf v_\ell$ with $\mathbf s \in \partial\|\mathbf b_\ell\|_2$ gives the soft-threshold. Lemma 1 chains $J(\mathbf b^{(k)}) = Q(\mathbf b^{(k)}\mid\mathbf b^{(k)}) \ge Q(\mathbf b^{(k)}(1)\mid\mathbf b^{(k)}) \ge \dots \ge J(\mathbf b^{(k+1)})$. The sufficient decrease follows blockwise from the optimality condition, a mean-value step and the $2$-Lipschitz bound on $H_\delta'$, and summing over $k$ shows $\sum_k\|\mathbf b^{(k)} - \mathbf b^{(k+1)}\|_2^2 < \infty$, so successive differences vanish. Since $\lambda > 0$ the group penalty makes $J$ coercive, so the descending iterates stay in a bounded sublevel set, and Lemma 2 makes every limit point a global minimizer of the convex $J$. Convergence of the whole sequence is immediate when the minimizer is unique; the source infers it from convergence of $J(\mathbf b^{(k)})$, which by itself yields only the statements above.

The same scheme with squared loss solves the group lasso without requiring orthonormal groups.

## Depends on

- [Huber group lasso for shared-topology gene regulatory networks](huber-group-lasso-for-shared-topology-gene-regulatory-networks.md)

## Sources

- L.-Z. Liu, F.-X. Wu, W. J. Zhang, "A group LASSO-based method for robustly inferring gene regulatory networks from multiple time-course datasets", BMC Systems Biology 8 (Suppl 3) (2014) S1, Method: Equations (10)-(22), Lemma 1, Lemma 2 and Theorem 3, <https://doi.org/10.1186/1752-0509-8-S3-S1>, PMCID PMC4243122.
