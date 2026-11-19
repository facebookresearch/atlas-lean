# Restricted eigenvalue condition

A design matrix $X \in \mathbb{R}^{n \times d}$ satisfies the *restricted eigenvalue condition*
with constant $\kappa$ over the cone $\mathcal{C}(S; \alpha)$ if $\kappa > 0$ and

$$\frac1n \|X\Delta\|_2^2 \ge \kappa \|\Delta\|_2^2 \quad \text{for every } \Delta \in \mathcal{C}(S; \alpha).$$

When $d > n$ the matrix $X^\top X / n$ is singular, so the condition can only hold on a cone and
not on the whole space.

## Sources

- T. Hastie, R. Tibshirani and M. J. Wainwright, *Statistical Learning with Sparsity: The Lasso and Generalizations*, CRC Press, 2015: <https://hastie.su.domains/StatLearnSparsity/>, eq. (11.10).
- M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University Press, 2019, §7.3.1 (restricted eigenvalue condition).
