# Small-mutation limit of a supercritical multi-type branching diffusion

Let $\mathbf X(t)=(X_1(t),\dots,X_d(t))$ be the neutral multi-type branching diffusion with generator

$$\mathcal L_{\mathbf X}=\frac12\sum_{i=1}^dx_i\frac{\partial^2}{\partial x_i^2}+\alpha\sum_{i=1}^dx_i\frac{\partial}{\partial x_i}+\sum_{i,j=1}^d\gamma_{ji}x_j\frac{\partial}{\partial x_i},$$

where $\alpha>0$ (supercritical) and $\gamma$ is a mutation rate matrix ($\gamma_{ij}\ge0$ for $i\ne j$, rows summing to $0$), parametrized as $\gamma_{ij}=\frac12\theta Q_{ij}$ with $-1\le\min_iQ_{ii}\le0$, so that $\theta$ is a small mutation parameter. The total $\sum_iX_i$ is a Feller diffusion. Let $\mathbf Z(t)=\mathbf X(t)e^{-\alpha t}$, and let $f_{\text{1-allele}}(t,z;x_0)$ be the density of the exponentially scaled one-type Feller diffusion started at $x_0$: an atom $e^{-x_0\mu(t)}$ at $0$ plus a Poisson$(x_0\mu(t))$ mixture of Gamma densities with rate $\mu(t)$, where $\mu(t)=\frac{2\alpha e^{\alpha t}}{e^{\alpha t}-1}$.

**Leading order.** As $\theta\to0$, with critical time $t_c=-\alpha^{-1}\log\theta$, the density of $\mathbf Z(t)$ started from $\mathbf x(0)$ is

$$f(t,\mathbf z;\mathbf x(0))=\begin{cases}\prod_{i=1}^d f_{\text{1-allele}}\big(t,z_i;x_i(0)\big)+O(\theta), & t<t_c,\\[1ex] \det\big(e^{-\gamma(t-t_c)}\big)\prod_{i=1}^d f_{\text{1-allele}}\big(\infty,(\mathbf z^{\mathsf T}e^{-\gamma(t-t_c)})_i;x_i(0)\big)+O(\theta), & t>t_c.\end{cases}$$

Before $t_c$ the types evolve as independent Feller diffusions; after $t_c$, the time at which a growing population of size of order $e^{\alpha t}$ has accumulated order-one mutation flux, the frozen exponentially scaled composition is mixed linearly by $e^{\gamma(t-t_c)}$, so as $t\to\infty$ the density collapses onto the ray spanned by the stationary left eigenvector of $\gamma$.

**First order, single ancestor.** For a population founded by one ancestor of type $i$ and conditioned to survive, the Laplace transform $\zeta(t,\boldsymbol\phi)=\mathbb E[e^{-\boldsymbol\phi\cdot\mathbf Z(t)}]$ equals $\zeta^{(0)}(1-\theta\,\xi^{(1)}+O(\theta^2))$ with explicit $\xi^{(1)}$, and its inverse is $f^{\text{1-ancestor}}(t,\mathbf z)=\mu(t)^dF(\mu(t)\mathbf z)$, where $F$ is, to order $\theta$, a sum of line densities along the $i$-th axis and the other axes and surface densities on the coordinate planes through the $i$-th axis, with the zeroth-order term $e^{-u_i}$.

## Expansion

The Laplace transform satisfies the first-order PDE $\partial_t\zeta=\big(-\frac12e^{-\alpha t}\sum_i\phi_i^2\partial_{\phi_i}+\sum_{i,j}\gamma_{ji}\phi_i\partial_{\phi_j}\big)\zeta$, solvable by characteristics. For one type, $\zeta_{\text{1-allele}}=\exp\{-x_0\phi/(1+\phi/\mu(t))\}$. For small $\theta$ the branching term dominates while $e^{-\alpha t}\gg\theta$, i.e. for $t<t_c$, and the mutation term dominates afterward, where the noise has died out and the scaled process evolves deterministically as $\dot{\mathbf z}^{\mathsf T}=\mathbf z^{\mathsf T}\gamma$; matching the two regimes gives the leading-order formula. Expanding the characteristics to first order in $\theta$ gives the correction, and inverting the Laplace transform term by term gives the line and surface densities.

## Sources

- Conrad J. Burden, "Multi-type branching diffusions with small mutation rates", arXiv:2610.05804 (2026), Proposition 1, Lemma 1 and Theorem 1, <https://doi.org/10.48550/arXiv.2610.05804>
