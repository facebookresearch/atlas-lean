# First spatial derivative of the heat kernel

Let $\Phi$ be the one-dimensional heat kernel. The real power is the one used for the kernel: $(4\pi t)^{-1/2}$ is the usual positive root for $t > 0$, and it is $0$ for $t \le 0$ (at a negative base the real power $y^{-1/2}$ is $\lvert y\rvert^{-1/2}\cos(-\pi/2) = 0$, and $0^{-1/2} = 0$). So in dimension one $\Phi(t, x)$ is the Gaussian $(4\pi t)^{-1/2} e^{-x^2/(4t)}$ for $t > 0$ and $0$ for $t \le 0$.

The first spatial derivative kernel is $\Phi_x(t, x) = -\frac{x}{2t}\,\Phi(t, x)$ for all real $t$ and $x$, with real division ($a/0 = 0$); it is $0$ for $t \le 0$. For every real $t$ it is the derivative of $\Phi(t, \cdot)$ at $x$.
