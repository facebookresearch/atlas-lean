# Least squares and the normal equations

Let $X$ be a real design matrix with $m$ rows and
columns indexed by a finite type $\iota$, let $y \in \mathbb{R}^m$, and write $S$ for the residual
sum of squares. A vector $\theta_0 \in \mathbb{R}^\iota$ satisfies $S(\theta_0) \le S(\theta)$ for
every $\theta \in \mathbb{R}^\iota$ if and only if $X^\top X \theta_0 = X^\top y$.

## Background

- [Stationary points of convex functions are global minimizers](../../../../Analysis/convex-analysis-and-variations/first-order-conditions-for-convexity/is-min-on-of-has-fderiv-at-eq-zero.md):
  background, the general principle behind the normal equations: $S$ is convex and
  $X^\top X \theta_0 = X^\top y$ says its gradient vanishes at $\theta_0$.
