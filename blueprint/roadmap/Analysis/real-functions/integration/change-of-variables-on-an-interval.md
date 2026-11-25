# Change of variables in the Lebesgue integral on an interval

Let $-\infty\le\alpha<\beta\le\infty$ and let $\varphi:(\alpha,\beta)\to\mathbb R$ be continuously differentiable with $\varphi'(t)\ne0$ for every $t$, so that $\varphi$ is strictly monotone and $J=\varphi((\alpha,\beta))$ is an open interval. For every Lebesgue measurable $f:J\to[0,\infty]$,

$$\int_Jf(x)\,dx=\int_\alpha^\beta f(\varphi(t))\,\lvert\varphi'(t)\rvert\,dt .$$

Consequently a measurable $f:J\to\mathbb R$ is integrable on $J$ if and only if $(f\circ\varphi)\,\lvert\varphi'\rvert$ is integrable on $(\alpha,\beta)$, and then the same identity holds. For example, $\varphi(s)=e^{-s}$ maps $(0,\infty)$ onto $(0,1)$ with $\lvert\varphi'(s)\rvert=e^{-s}$, so $\int_0^1f(x)\,dx=\int_0^\infty f(e^{-s})\,e^{-s}\,ds$.

## Expansion

A proof page must establish the identity for indicators of intervals, where it is the fundamental theorem of calculus for $\varphi$, extend it to Borel sets by the $\pi$–$\lambda$ theorem and to Lebesgue measurable sets through null sets (images of null sets under $\varphi^{-1}$ are null since $\varphi^{-1}$ is locally Lipschitz), then to nonnegative measurable functions by monotone convergence, and to integrable functions by splitting into positive and negative parts.

## Sources

- W. Rudin, *Real and Complex Analysis*, 3rd ed., McGraw-Hill, 1987, Chapter 7.
- G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed., Wiley, 1999, Chapter 2.
