# Distortion Feasible

Let $\sigma^2 \ge 0$ and $D \in \mathbb{R}$. The set of distortion-feasible joint laws is the set of probability measures $\mu$ on $\mathbb{R}^2$, the joint laws of a source $X$ and a reconstruction $\hat{X}$, such that

- $D \ge 0$;
- the first marginal of $\mu$ is $\mathcal{N}(0, \sigma^2)$;
- $\displaystyle \int (x - \hat{x})^2 \, d\mu(x, \hat{x}) \le D$, the integral of a nonnegative function, possibly infinite.

For $D < 0$ the set is empty.
