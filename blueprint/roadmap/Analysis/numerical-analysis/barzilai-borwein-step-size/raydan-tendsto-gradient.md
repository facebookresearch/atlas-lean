# Raydan's theorem

Let $A$ be a symmetric positive definite operator on a finite-dimensional real inner product space
and $f(x) = \tfrac12 x^\top A x - b^\top x$, whose gradient is $Ax - b$. Run the two-point step-size
gradient method $x_{k+1} = x_k - \alpha_k (A x_k - b)$ from any $x_0$, with any $\alpha_0 > 0$ and the
[Barzilai–Borwein step](bb-step.md) $\alpha_{k+1} = s^\top s / s^\top y$, where
$s = x_{k+1} - x_k$ and $y = A s$. Then $A x_k - b \to 0$, that is, $x_k \to A^{-1} b$.

The method is not monotone: $f(x_k)$ can increase. For $n = 2$ Barzilai and Borwein proved
R-superlinear convergence; Raydan's later nonmonotone line search extends the method to
non-quadratic functions (both as reported in Section 1 of the source below).

## Background

- [Barzilai–Borwein steps on a quadratic lie between the inverse curvature bounds](bb-step-mem-icc.md):
  on this quadratic every step lies in $[1/\lambda_{\max}, 1/\lambda_{\min}]$.

## Sources

- M. Raydan, *On the Barzilai and Borwein choice of steplength for the gradient method*, IMA J.
  Numer. Anal. 13 (1993), 321–326, as reported in Y. H. Dai, J. Y. Yuan and Y. Yuan, *Modified two-point stepsize gradient methods for unconstrained optimization*, Comput. Optim. Appl. 22 (2002), 103–109; https://lsec.cc.ac.cn/pub/home/yyx/papers/daiyuanyuan.pdf, Section 1.
