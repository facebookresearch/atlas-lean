# Integral equation for the first passage time of one component of a bivariate diffusion

**Setting.** Let $\mathbf{X}(t) = (X_1(t), X_2(t))$ be a bivariate diffusion with $\mathbf{X}(0) = \mathbf{0}$, and let $T = \inf\{t > 0 : X_1(t) \ge S\}$ be the first passage time of the first component through a constant boundary $S > 0$, with density $g(\vartheta \mid \mathbf{0}, 0)$. Let $Z(\vartheta)$ denote the value of $X_2$ at the passage time, conditionally on $T = \vartheta$.

**Theorem.** If $\mathbb{P}(X_1(t) \ge S \mid X_1(\vartheta) = S, X_2(\vartheta) = z)$ and its $t$-derivative are continuous for $0 \le \vartheta \le t$, $z \in \mathbb{R}$, then $g$ is the unique solution of

$$
\mathbb{P}\bigl(X_1(t) \ge S \mid \mathbf{X}(0) = \mathbf{0}\bigr) = \int_0^t g(\vartheta \mid \mathbf{0}, 0)\; \mathbb{E}_{Z(\vartheta)}\Bigl[\mathbb{P}\bigl(X_1(t) \ge S \mid X_1(\vartheta) = S, X_2(\vartheta)\bigr)\Bigr]\,d\vartheta .
$$

For a Gauss–Markov process $d\mathbf{X} = (\mathbf{A}(t)\mathbf{X} + \mathbf{M}(t))\,dt + \mathbf{G}(t)\,d\mathbf{B}(t)$, with conditional mean $m^{(1)}$ and variance $Q^{(11)}$ of the first component, this becomes

$$
1 - \operatorname{Erf}\Bigl(\frac{S - m^{(1)}(t)}{\sqrt{2Q^{(11)}(t)}}\Bigr) = \int_0^t g(\vartheta \mid \mathbf{0}, 0)\; \mathbb{E}_{Z(\vartheta)}\Bigl[1 - \operatorname{Erf}\Bigl(\frac{S - m^{(1)}(t \mid (S, X_2(\vartheta)), \vartheta)}{\sqrt{2Q^{(11)}(t \mid (S, X_2(\vartheta)), \vartheta)}}\Bigr)\Bigr]\,d\vartheta .
$$

Discretizing the integral on a grid of step $h$ and estimating the expectation over $Z$ by Monte Carlo with error of order $h^2$ yields an algorithm whose error at the grid points is $O(h)$ under a Lipschitz-type condition on the kernel.

Examples include integrated Brownian motion and the integrated Ornstein–Uhlenbeck process, which model a neuron's membrane potential driven by a correlated (colored-noise) input current.

## Proof sketch

This is the bivariate analogue of the Fortet equation: to be above $S$ at time $t$, the path must have crossed $S$ for the first time at some $\vartheta \le t$, and then, by the strong Markov property, moved from $(S, X_2(\vartheta))$ to above $S$ in time $t - \vartheta$. In one dimension the restart point is just $S$; in two dimensions the unobserved second coordinate at the crossing must be averaged, which is why the distribution of $Z(\vartheta)$ enters. For a neuron, $X_1$ is the membrane potential, $X_2$ the input current or another slow variable, and $T$ is the interspike interval in the absence of reset.

## Related topics

- [Leaky integrate-and-fire neuron](../../leaky-integrate-and-fire-neuron/README.md)

## Sources

- Elisa Benedetto, Laura Sacerdote and Cristina Zucca, "A first passage problem for a bivariate diffusion process: Numerical solution with an application to neuroscience when the process is Gauss–Markov", *Journal of Computational and Applied Mathematics* 242 (2013), 41–52, <https://doi.org/10.1016/j.cam.2012.10.014>. Preprint version: arXiv:1204.5307 (2012), Theorem 2, Corollary 3, Theorem 4, <https://doi.org/10.48550/arXiv.1204.5307>.
