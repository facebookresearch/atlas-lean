# Effect of residuals on the meat matrix

Let $x_0, x_1, \dots \in \mathbb{R}^k$, $u_0, u_1, \dots \in \mathbb{R}$, $\delta \in \mathbb{R}^k$ and $n \ge 1$, and let $\hat\Omega_n(u) = \frac1n\sum_{i<n}u_i^2x_ix_i^\top$. Replacing the errors $u_i$ by residuals $u_i - x_i^\top\delta$ changes each entry by at most

$$\big|\hat\Omega_n(u - x^\top\delta)_{ab} - \hat\Omega_n(u)_{ab}\big| \le 2k\|\delta\|\,\frac1n\sum_{i<n}\|x_i\|^3|u_i| + k^2\|\delta\|^2\,\frac1n\sum_{i<n}\|x_i\|^4,$$

where $\|\cdot\|$ is the sup norm on $\mathbb{R}^k$.
