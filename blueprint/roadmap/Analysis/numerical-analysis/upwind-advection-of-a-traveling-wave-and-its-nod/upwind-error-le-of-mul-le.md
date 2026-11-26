# Upwind scheme error bound at final time

Take $n \ge 1$ periodic cells on $[0, L)$ with $L > 0$ and $dx = L/n$, a time step $dt > 0$, and Courant number $\nu = v\,dt/dx$ with $0 \le \nu \le 1$. Let $u^k_j$ satisfy the upwind scheme $u^{k+1}_j = (1 - \nu) u^k_j + \nu u^k_{j-1}$ (indices mod $n$), and let $w^k_j = c_0 + a \sin\!\big(2\pi (j\,dx - v k\,dt)/L\big)$ be the samples of the traveling wave. If $N\,dt \le T$, then in the maximum norm over cells

$$\|u^N - w^N\| \le \|u^0 - w^0\| + \frac{T M (v^2 dt + v\,dx)}{2}, \qquad M = |a| \left(\frac{2\pi}{L}\right)^2.$$
