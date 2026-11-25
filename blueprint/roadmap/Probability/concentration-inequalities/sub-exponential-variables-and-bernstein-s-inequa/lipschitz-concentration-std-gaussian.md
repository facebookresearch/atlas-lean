# Concentration of Lipschitz functions of Gaussian variables

Let $X$ be a standard Gaussian vector in $\mathbb{R}^n$ and $f : \mathbb{R}^n \to \mathbb{R}$
be $L$-Lipschitz for the Euclidean norm. Then $f(X) - \mathbb{E}[f(X)]$ is sub-Gaussian with
variance proxy $L^2$, and hence for every $t \ge 0$

$$\mathbb{P}\big(|f(X) - \mathbb{E}[f(X)]| \ge t\big) \le 2 e^{-t^2/(2L^2)}.$$

The bound does not depend on the dimension $n$.

## Sources

- M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*, Cambridge University Press, 2019, §2.3 (Lipschitz functions of Gaussian variables).
- R. Vershynin, *Introduction to the non-asymptotic analysis of random matrices*, in *Compressed Sensing: Theory and Applications*, Cambridge University Press, 2012, arXiv:1011.3027, Proposition 5.34 (the one-sided tail bound).

## Background

- [Hoeffding's inequality](../hoeffding-s-inequality/README.md): the same sub-Gaussian tail for sums of bounded variables, a dimension-free counterpart for Lipschitz functions of Gaussians.
