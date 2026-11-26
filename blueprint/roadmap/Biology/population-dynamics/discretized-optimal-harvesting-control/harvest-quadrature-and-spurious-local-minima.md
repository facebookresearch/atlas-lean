# Harvest quadrature and spurious local minima in discretized harvesting control

**Pure harvesting.** A population with initial density $y^0>0$ is harvested with effort $u^n\in[0,U_{\max}]$ on steps of length $\tau$, catchability $q>0$, over $N$ steps. The positivity-preserving (Patankar-type) update is
$$y^{n+1}=\frac{y^n}{1+\tau qu^n},\qquad y^n-y^{n+1}=\tau qu^ny^{n+1},$$
so the catch on step $n$ is exactly $\tau qu^ny^{n+1}$. Compare two harvest quadratures in the cost (effort penalty $\lambda>0$, harvest reward $\eta\ge0$):
$$j_1(u)=\frac{\lambda\tau}2\sum_{n<N}(u^n)^2-\eta\tau q\sum_{n<N}u^ny^{n+1}\quad\text{(flux / new-state rule)},$$
$$j_0(u)=\frac{\lambda\tau}2\sum_{n<N}(u^n)^2-\eta\tau q\sum_{n<N}u^ny^{n}\quad\text{(old-state rule)}.$$

**Proposition.**

1. For every $N$, $\lambda>0$ and $\eta\ge0$, $j_1$ is strictly convex on $[0,U_{\max}]^N$. Its unique minimizer is constant in time, and an interior value $s$ solves $\lambda s=\eta qy^0(1+\tau qs)^{-N-1}$. At $u=0$ the Hessians are $H_1(0)=\lambda I+\eta\tau q^2y^0(\mathbf 1\mathbf 1^{\mathsf T}+I)$ and $H_0(0)=\lambda I+\eta\tau q^2y^0(\mathbf 1\mathbf 1^{\mathsf T}-I)$, so the old-state rule has a negative curvature mode once $\eta\tau q^2y^0>\lambda$.
2. For $N=2$, set $x=\tau qu^0$, $z=\tau qu^1$ and $c=\eta\tau q^2y^0/\lambda$. If $1<c\le\tau qU_{\max}$, then $(x,z)=(0,c)$ is a strict constrained local minimizer of $j_0$ whose cost is strictly above the global minimum, while $j_1$ has a unique global minimizer.
3. With total effort $E$ split as $(a,E-a)$ over two steps, the flux cost has the unique minimizer $a=E/2$, which agrees with the exact continuous-removal model. If $\lambda\tau<\eta\tau^2q^2y^0/(1+\tau qE)^2$, the old-state cost is strictly concave in $a$ and has exactly two global minimizers $a\in\{0,E\}$.

**Predator–prey with diffusion.** For the system $\partial_tv_1-\mu_1\Delta v_1=v_1(-m+\alpha v_2)$, $\partial_tv_2-\mu_2\Delta v_2=v_2(r-\beta v_1)-quv_2$ with Neumann conditions, discretized by the positive transfer-implicit step $(I-\tau\mu_2L_h+\tau\operatorname{diag}(\beta v_1^n+qu^n))v_2^{n+1}=(1+\tau r)v_2^n$ and $(I-\tau\mu_1L_h+\tau mI)v_1^{n+1}=v_1^n+\tau\alpha v_1^n\circ v_2^{n+1}$, iterates stay nonnegative for every $\tau>0$. The weighted mass $\beta\langle v_1^n,\mathbf 1\rangle+\alpha\langle v_2^n,\mathbf 1\rangle$ obeys an exact discrete balance law. The two quadratures differ uniformly by $\sup_u|j_1(u)-j_0(u)|\le C\tau$, and in one space dimension with $H^1$-bounded data their gradients and Hessians also differ by $O(\tau)$, uniformly in the mesh.

## Expansion

The old-state rule over-counts the catch on step $n$ by $\tau qu^ny^n-(y^n-y^{n+1})=\tau^2q^2(u^n)^2y^{n+1}$. This extra reward is convex in $u^n$, so subtracting it from the cost adds concave terms that favor concentrating effort in a single step. The defect is $O(\tau)$ in value, yet it changes the qualitative landscape: it can create strict local minima, and minimizers can jump between extreme allocations. Gradient-based optimal control can then stall at an artifact of the quadrature rather than of the biology. Counting the actual flux removed by the positive scheme restores convexity and is consistent with the continuous harvesting model; both rules share the same variational limit as $h,\tau\to0$.

## Sources

- Alexandre Autran, "Quadrature-Induced Local Minima in Structure-Preserving Lotka-Volterra Control", arXiv:2611.20131 (2026), Theorem 4.1, Proposition 6.3, Propositions 7.1–7.3 and Theorem 8.1, <https://doi.org/10.48550/arXiv.2611.20131>.
