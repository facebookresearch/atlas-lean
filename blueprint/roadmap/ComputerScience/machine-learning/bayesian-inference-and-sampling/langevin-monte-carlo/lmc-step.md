# One step of the Langevin Monte Carlo algorithm, on laws

Let $E$ be a finite-dimensional real inner product space, $f : E \to \mathbb{R}$, $h \in \mathbb{R}$ and $\mu$ a probability measure on $E$. The Langevin Monte Carlo step sends $\mu$ to

$$
\mathrm{LMC}_{f,h}(\mu) = (\mu \otimes \mathcal N(0, I))\circ T^{-1}, \qquad T(\vartheta, \xi) = \vartheta - h\nabla f(\vartheta) + \sqrt{2h}\,\xi :
$$

if $\vartheta \sim \mu$ and $\xi$ is an independent standard Gaussian vector, it is the law of $\vartheta - h\nabla f(\vartheta) + \sqrt{2h}\,\xi$. Iterating it from the law $\nu_0$ of $\vartheta_0$ gives the laws $\nu_k$ of the iterates of the update rule $\vartheta_{k+1} = \vartheta_k - h\nabla f(\vartheta_k) + \sqrt{2h}\,\xi_{k+1}$ with i.i.d. standard Gaussian $\xi_k$ independent of $\vartheta_0$. The image is again a probability measure. Here
$\nabla f(\vartheta)$ is taken to be $0$ where $f$ is not differentiable, and $\sqrt{2h} = 0$ for $h < 0$; the
algorithm uses $h > 0$.

## Background

- [Gradient descent](../../../../Analysis/convex-analysis-and-variations/gradient-descent/README.md): without the noise term the step is a gradient step on $f$ with step $h$.

## Sources

- A. S. Dalalyan, *Further and stronger analogy between sampling and optimization: Langevin Monte Carlo and gradient descent*, arXiv:1704.04752v2 (COLT 2017), update rule (2).
