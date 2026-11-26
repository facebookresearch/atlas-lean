# Impulsive Goodwin model with a releasable hormone pool

**Setting.** The impulsive Goodwin oscillator models pulsatile endocrine feedback in a three-hormone axis (for example GnRH, LH and testosterone). A releasable pool of the hypothalamic hormone, of size $x_r\ge0$, is replenished and degraded between pulses, $\dot x_r=-a_rx_r+v$ with $a_r,v>0$. Downstream, a linear cascade

$$\dot x_1=-a_1x_1,\qquad \dot x_2=-a_2x_2+g_1x_1,\qquad \dot x_3=-a_3x_3+g_2x_2,\qquad y=x_3,$$

with $a_i,g_i>0$, gives the feedback output $y$. Pulses occur at times $t_{k+1}=t_k+\Phi(y(t_k))$ with a continuous, nondecreasing *frequency modulation* $\Phi:\mathbb R_+\to(0,\infty)$ (higher output delays the next pulse). At $t_k$ an amount $\lambda_k=F(x_r(t_k^-),y(t_k^-))$ leaves the pool and enters the first compartment: $x_r\mapsto x_r-\lambda_k$, $x_1\mapsto x_1+\beta\lambda_k$ ($\beta>0$), other states unchanged. The *amplitude modulation* $F:\mathbb R_+^2\to\mathbb R_+$ is admissible if $0<F(\xi,\theta)\le\xi$ for $\xi>0$ and $F(0,\theta)=0$ (one cannot release more than is available). A **1-cycle** is a periodic solution with exactly one pulse per period; write $y^*$, $\lambda^*$ and $T^*$ for its output at pulse times, released dose and period.

**Theorem 1 (existence, uniqueness and monotonicity of the 1-cycle).** If $\Phi$ is continuous, positive and nondecreasing and $F$ is continuous and admissible, the system has at least one positive 1-cycle. If moreover $F$ is continuously differentiable with $0<\partial_\xi F\le1$ and $\partial_\theta F\le0$, the positive 1-cycle is unique, and as functions of the pool parameters:
1. $y^*$, $\lambda^*$ and $T^*$ are nondecreasing in the synthesis rate $v$ for fixed $a_r$;
2. $y^*$, $\lambda^*$ and $T^*$ are nonincreasing in the pool degradation rate $a_r$ for fixed $v$.

If $\partial_\xi F>0$ the monotonicity of $y^*$ and $\lambda^*$ is strict, and if $\Phi$ is also strictly increasing so is that of $T^*$.

**Proposition 2 (orbital stability).** For continuously differentiable $F$ and $\Phi$, the Jacobian of the pulse-to-pulse return map at the fixed point corresponding to the 1-cycle is given explicitly in terms of $\partial_\xi F$, $\partial_\theta F$, $\Phi'(y^*)$, $e^{-a_rT^*}$ and the matrix exponential of the cascade over one period; the 1-cycle is orbitally asymptotically stable when this Jacobian is Schur stable.

## Expansion

Sampling the state just before each pulse turns the hybrid system into a discrete return map; a 1-cycle is a fixed point. Between pulses everything is linear, so the pool level and the cascade state at the next pulse are explicit functions of the dose and the period. Eliminating them reduces the fixed-point problem to a single scalar equation in $y^*$ (Proposition 1), whose solvability follows from continuity and the admissibility bound $F\le\xi$, and whose uniqueness follows from monotonicity of both sides under the derivative conditions on $F$. Faster synthesis fills the pool more, raising the dose and output and, through $\Phi$, lengthening the period; faster pool degradation does the opposite. Positivity facts about $C\,f(TA)B$ for the cascade's state-space realization with convex $f$ (Corollary 1) supply the needed sign information.

## Sources

- A. V. Proskurnikov, A. Medvedev, "Pulsatile endocrine regulation with a releasable hormone pool: impulsive feedback model", arXiv preprint (2026), Proposition 1, Theorem 1, Proposition 2, Corollary 1, <https://doi.org/10.48550/arXiv.2611.13277>.
