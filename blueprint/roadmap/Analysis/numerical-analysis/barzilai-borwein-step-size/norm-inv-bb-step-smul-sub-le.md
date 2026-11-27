# The first Barzilai–Borwein step is a least-squares secant fit

For all vectors $s, y$ and every real $t$,

$$\Bigl\| \frac{s^\top y}{s^\top s}\, s - y \Bigr\| \le \| t s - y \|,$$

where $s^\top y / s^\top s = \alpha^{-1}$ is the inverse of the
[first Barzilai–Borwein step](bb-step.md): among scalar matrices, $\alpha^{-1} I$ best satisfies the
secant equation $B s = y$. For $n = 1$ this is the secant method.

Proof: $\|ts - y\|^2 - \|t^\star s - y\|^2 = \|s\|^2 (t - t^\star)^2$ with $t^\star = s^\top y / s^\top s$.

## Background

- [The BFGS update satisfies the secant equation](../quasi-newton-methods/bfgs-update-apply-self.md):
  the matrix secant equation that the Barzilai–Borwein step fits with a multiple of the identity.

## Sources

- Y. H. Dai, J. Y. Yuan and Y. Yuan, *Modified two-point stepsize gradient methods for unconstrained optimization*, Comput. Optim. Appl. 22 (2002), 103–109; https://lsec.cc.ac.cn/pub/home/yyx/papers/daiyuanyuan.pdf, Section 1 (derivation of (1.5) by minimising $\|H_k^{-1} s_{k-1} - y_{k-1}\|_2$).
