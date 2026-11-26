# Energy error of the P1 bar reconstruction

Let $P$ be a partition of $[0,1]$ with mesh size $h$ (its largest cell length), let $I_P$ be the continuous piecewise-linear nodal interpolant on $P$, and let $\hat u(\xi) = \xi(1-\xi)$. For $EA, L, q \in \mathbb{R}$ set $\alpha = \dfrac{q L^2}{2\,EA}$, $u(x) = \dfrac{q\,x\,(L - x)}{2\,EA}$ (the fixed-fixed bar displacement under uniform load $q$), $u_h(x) = \alpha\,(I_P \hat u)(x/L)$, and $e = u - u_h$. If $L > 0$ and $EA > 0$, then

$$\int_0^L EA\, e'(x)^2 \, dx \;\le\; \frac{EA}{L}\, \alpha^2 \cdot 4 \left(\frac{h}{\pi}\right)^2,$$

where $e'$ is the derivative of $e$, taken to be $0$ at the finitely many points where $e$ is not differentiable.
