# Initial pair mismatch

On a periodic grid of $N$ cells with spacing $h$, for functions $u, v$ of $(t, x)$, time step $\Delta t$ and initial grid data $u^0, v^0 \in \mathbb R^N$, the initial pair mismatch is

$$\sqrt{h\sum_j \left(u(0, jh) - u^0_j\right)^2 + h\sum_j \left(v(-\Delta t/2, jh - h/2) - v^0_j\right)^2},$$

with the convention $\sqrt{x} = 0$ for $x < 0$, so for $h < 0$ (when the radicand is nonpositive) the value is $0$. For $h \ge 0$ it is the Euclidean pair norm of the difference between the exact staggered samples at step $0$ and the initial data, a genuine weighted norm for $h > 0$.
