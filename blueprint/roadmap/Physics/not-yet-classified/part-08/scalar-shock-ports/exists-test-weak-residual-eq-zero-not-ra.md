# A single zero test does not certify a weak solution

There is a smooth test function $\varphi(t,x)$, supported in a bounded rectangle, with time and space partial derivatives $\varphi_t$, $\varphi_x$, such that for Burgers' flux $f(u) = u^2/2$ and the stationary step $u = 2$ for $x < 0$, $u = 0$ for $x \ge 0$, the weak residual

$$\iint \big(u\,\varphi_t + f(u)\,\varphi_x\big)\,dt\,dx$$

vanishes, although the Rankine-Hugoniot condition fails at speed $0$: $0\cdot(0 - 2) \ne 0^2/2 - 2^2/2$.
