# Truncation error of the upwind scheme for a traveling sine wave

Let $L > 0$, $\Delta t > 0$, a positive number $N$ of uniform periodic cells on $[0, L)$ with $\Delta x = L/N$, and Courant number $\nu = v\,\Delta t/\Delta x \ge 0$. Let $w_j^n = c(n\Delta t, j\Delta x)$ be the point samples of the traveling wave $c(t, x) = c_0 + a\sin(2\pi(x - vt)/L)$, with node indices taken modulo $N$. Then at every node $j$ (including the wrapped neighbour of $j = 0$) and every time level $n$,

$$\bigl|w_j^{n+1} - \bigl((1 - \nu)w_j^n + \nu w_{j-1}^n\bigr)\bigr| \le \frac{\Delta t\, M\,(v^2\Delta t + v\,\Delta x)}{2}, \qquad M = |a|\left(\frac{2\pi}{L}\right)^2.$$
