# Chapman–Kolmogorov equation for the Wright–Fisher diffusion

For all real $s \ge 0$ and $t \ge 0$, the [Wright–Fisher transition kernels](wf-transition-kernel.md) satisfy

$$K_{s+t}(x, A) = \int K_t(y, A)\, K_s(x, dy)$$

for every $x \in [0, 1]$ and every measurable $A \subseteq [0, 1]$: evolving for time $s + t$ is evolving for time $s$ and then for time $t$.
