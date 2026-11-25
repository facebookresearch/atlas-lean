# Error bound for the upwind scheme on a sine wave

Let $n \ge 1$ periodic cells cover a domain of length $L > 0$, with cell width $\Delta x = L/n$, time step $\Delta t > 0$, speed $v$ and Courant number $\nu = v \Delta t / \Delta x$ satisfying $0 \le \nu \le 1$. Let $w_j^k = c_0 + a \sin\!\big(2\pi (j \Delta x - v k \Delta t)/L\big)$ be the traveling sine wave sampled at the nodes, and let $u_j^k$ (indices $j$ modulo $n$) satisfy the upwind recurrence $u_j^{k+1} = (1 - \nu) u_j^k + \nu u_{j-1}^k$. Then for every $N$, the nodal error $E_k = \max_j |u_j^k - w_j^k|$ satisfies

$$E_N \le E_0 + N \cdot \frac{\Delta t\, M\, (v^2 \Delta t + v \Delta x)}{2}, \qquad M = |a| (2\pi/L)^2.$$
