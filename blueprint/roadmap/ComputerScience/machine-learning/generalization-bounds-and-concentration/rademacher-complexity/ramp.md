# The ramp cost

For $\theta > 0$, the ramp cost is

$$\rho_\theta(u) = \min\big(1, \max(0, 1 - u/\theta)\big),$$

equal to $1$ for $u \le 0$, to $0$ for $u \ge \theta$, and linear in between. It sits between the zero-one loss and the margin error ([lower bound](indicator-le-ramp.md), [upper bound](ramp-le-indicator.md)) and is $1/\theta$-Lipschitz ([Lipschitz bound](lipschitz-with-ramp.md)), which is what a margin bound needs.

## Sources

- P. L. Bartlett and S. Mendelson, "Rademacher and Gaussian complexities: risk bounds and structural results", *J. Mach. Learn. Res.* 3 (2002), 463–482, <https://jmlr.csail.mit.edu/papers/volume3/bartlett02a/bartlett02a.pdf>, Theorem 7 (a Lipschitz cost $\varphi$ with $\varphi(\alpha) \ge \mathbf{1}(\alpha \le 0)$).
