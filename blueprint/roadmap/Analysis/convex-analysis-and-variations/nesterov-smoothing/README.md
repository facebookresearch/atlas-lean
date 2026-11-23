# Nesterov smoothing

Many nonsmooth convex functions are maxima of linear functions over a convex set, $f_0(x) = \max_{u \in Q} (\langle A x, u\rangle - \varphi(u))$. Subtracting $\mu$ times a strongly convex prox-function $d$ of $Q$ inside the maximum gives a function $f_\mu$ that is uniformly within $\mu \max_Q d$ of $f_0$ and has a Lipschitz gradient with constant $\|A\|^2/(\mu\sigma)$. Minimising $f_\mu$ with an optimal method for smooth functions then solves the nonsmooth problem in $O(1/\varepsilon)$ iterations, against $O(1/\varepsilon^2)$ for subgradient methods (Nesterov, 2005).

- [Nesterov's smoothed max-type function](smoothed-max.md)
- [Uniform approximation by the smoothed function](smoothed-max-approximation.md)
- [The smoothed max-type function has a Lipschitz gradient](smoothed-max-lipschitz-gradient.md)

## Related topics

- [Accelerated gradient methods](../accelerated-gradient-methods/README.md): the optimal smooth method that the smoothing technique feeds.
- [Lipschitz regularization by inf-convolution](../lipschitz-regularization-by-inf-convolution/README.md): another regularization by inf-convolution; with $\varphi = 0$, $A = I$, $d = \frac{1}{2}\|\cdot\|^2$ and $Q$ compact and convex, $f_\mu$ is the Moreau envelope of the support function of $Q$, its inf-convolution with $\frac{1}{2\mu}\|\cdot\|^2$.
- [Gradient descent](../gradient-descent/README.md): the subgradient method, whose $O(1/\varepsilon^2)$ complexity smoothing improves.
