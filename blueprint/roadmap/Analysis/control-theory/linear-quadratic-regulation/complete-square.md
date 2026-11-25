# Completing the square for one LQR stage

Let $P, Q$ be positive semidefinite and $R$ positive definite, let $K = (R + B^\top P B)^{-1} B^\top P A$ and let $P'$ be the Riccati step $Q + A^\top P A - A^\top P B (R + B^\top P B)^{-1} B^\top P A$. Then every state $x$ and input $u$ satisfy

$$x^\top Q x + u^\top R u + (Ax + Bu)^\top P (Ax + Bu) = x^\top P' x + (u + Kx)^\top (R + B^\top P B)(u + Kx).$$
