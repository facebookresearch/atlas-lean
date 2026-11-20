# First Barzilai–Borwein step size

For the step $s = x_k - x_{k-1}$ and the gradient change $y = \nabla f(x_k) - \nabla f(x_{k-1})$,
the first Barzilai–Borwein step size is

$$\alpha = \frac{s^\top s}{s^\top y},$$

used in the gradient iteration $x_{k+1} = x_k - \alpha\, \nabla f(x_k)$. It makes $\alpha^{-1} I$ the
[best scalar fit](norm-inv-bb-step-smul-sub-le.md) of the secant equation $B s = y$.

## Sources

- Y. H. Dai, J. Y. Yuan and Y. Yuan, *Modified two-point stepsize gradient methods for unconstrained optimization*, Comput. Optim. Appl. 22 (2002), 103–109; https://lsec.cc.ac.cn/pub/home/yyx/papers/daiyuanyuan.pdf, formula (1.5).
