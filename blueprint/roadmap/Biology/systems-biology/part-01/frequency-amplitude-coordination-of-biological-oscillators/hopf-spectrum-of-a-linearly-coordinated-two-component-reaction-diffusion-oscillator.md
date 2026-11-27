# Hopf spectrum of a linearly coordinated two-component reaction–diffusion oscillator

**Setting.** Consider a two-component reaction–diffusion system on $x \in [0,\pi]$, written around a homogeneous steady state moved to the origin, with a linear coordinator $F = (f_{ij})$ added to the reaction part:

$$\partial_t u = L(\epsilon)u + g(u,\epsilon),\qquad L(\epsilon) = D(\epsilon)\,\partial_x^2 + A(\epsilon) + F,$$

where $u = (u_1,u_2)$, $D = \mathrm{diag}(d_1,d_2)$ with $d_i \ge 0$ not both zero, $A = (a_{ij})$, $g(0,\epsilon) = 0$ collects nonlinear terms, and $\epsilon$ is the bifurcation parameter. Under Neumann, Dirichlet or periodic boundary conditions the Laplacian has eigenvalues $-k_i^2$ with $0 \le k_0^2 < k_1^2 < \cdots$, and every eigenvalue of $L$ solves, for some $i$,

$$\lambda^2 + c_1(k_i)\lambda + c_0(k_i) = 0,$$

$$c_1(k) = (d_1+d_2)k^2 - a_{11} - a_{22} - f_{11} - f_{22},$$

$$c_0(k) = d_1d_2k^4 - [d_1(a_{22}+f_{22}) + d_2(a_{11}+f_{11})]k^2 + (a_{11}+f_{11})(a_{22}+f_{22}) - (a_{21}+f_{21})(a_{12}+f_{12}).$$

**Theorem.**
1. The Hopf bifurcation of $u \equiv 0$ occurs at the same parameter values with and without the coordinator if and only if $f_{11} + f_{22} = 0$.
2. If at $\epsilon = \epsilon^*$ the operator $L$ has a unique pair of purely imaginary eigenvalues and all others lie in the open left half-plane, then $c_0(k_i) > 0$ for all $i$, the imaginary pair comes from the lowest mode $k_0$, and $\epsilon^*$ is determined by $c_1(k_0) = 0$ (so a stable bifurcating oscillation can only arise from the $k_0$ mode).
3. With $f_{11} + f_{22} = 0$, near $\epsilon^*$ the critical eigenvalues are $\mu(\epsilon) \pm i\omega(\epsilon)$ with

$$\mu = \tfrac12\big(a_{11} + a_{22} - k_0^2(d_1+d_2)\big),\qquad \omega^2 = -(a_{12}+f_{12})(a_{21}+f_{21}) - \xi^2,$$

$$\xi = f_{11} + \tfrac12\big(a_{11} - a_{22} + k_0^2(d_2 - d_1)\big),$$

so the oscillation frequency near onset is tuned by the coordinator intensities $f_{11}$, $f_{12}$, $f_{21}$, while the amplitude follows from the first Lyapunov coefficient of the Poincaré normal form.

## Expansion

Projecting onto the Laplacian eigenfunctions reduces $L$ to the $2\times2$ matrices $M(k_i) = -k_i^2D + A + F$, whose characteristic polynomial is the quadratic above with $c_1 = -\operatorname{tr}M$ and $c_0 = \det M$. A purely imaginary pair requires $c_1 = 0 < c_0$ for some mode, and stability of all other modes forces $c_0 > 0$ everywhere and, since $c_1(k)$ increases with $k^2$, the critical mode to be $k_0$. The Hopf condition $\operatorname{tr}M(k_0) = 0$ is unchanged by $F$ exactly when $F$ is traceless. For a $2\times2$ matrix, $\omega^2 = \det M - (\tfrac12\operatorname{tr}M)^2 = -m_{12}m_{21} - \tfrac14(m_{11} - m_{22})^2$, which with $f_{22} = -f_{11}$ gives the stated formula. Numerically, energy-optimal coordinators strengthen all four endogenous linear interactions (in the same direction as $a_{ij}$) to raise frequency or amplitude and weaken them to lower it.

## Sources

- B.-W. Qin, L. Zhao, W. Lin, "A frequency-amplitude coordinator and its optimal energy consumption for biological oscillators", Nature Communications 12:5894 (2021), Methods, Eqs (11)–(13), Propositions 1–2 and Theorems 1–4, <https://doi.org/10.1038/s41467-021-26182-2>, PMCID PMC8501100.
