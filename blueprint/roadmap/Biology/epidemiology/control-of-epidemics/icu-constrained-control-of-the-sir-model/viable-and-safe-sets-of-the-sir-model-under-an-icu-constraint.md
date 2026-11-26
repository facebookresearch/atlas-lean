# Viable and safe sets of the SIR model under an ICU constraint

**Model.** Normalized susceptible and infectious densities $s,i$ evolve under a contact-reducing control $u(t)\in[0,u_{\max}]$, $0\le u_{\max}<\beta$:

$$\dot s=-(\beta-u)\,s\,i,\qquad \dot i=(\beta-u)\,s\,i-\gamma i,\qquad s(0)=s_0,\ i(0)=i_0,$$

with $\beta,\gamma>0$, on the triangle $\mathbb T=\{(s,i)\in(0,1]^2:\ s+i\le1\}$, which is invariant. An ICU capacity $i_M\in(0,1)$ imposes $i(t)\le i_M$ for all $t\ge0$.

**Proposition (asymptotics).** For every measurable control, $s$ is strictly decreasing, $i(t)\to0$, and $s_\infty=\lim_{t\to\infty}s(t)\in(0,1)$ satisfies $s_\infty<\gamma/(\beta-u_{\max})$. If moreover $u\in L^1(0,\infty)$, then $s_\infty<\gamma/\beta$ (the herd-immunity threshold is crossed).

**Theorem (viable and safe sets).** Let $\mathcal B$ (viable set) be the initial states for which some admissible control keeps $i\le i_M$ forever, and $\mathcal A$ (safe set) those for which $u\equiv0$ already does. Then

$$\mathcal B=\{(s,i)\in\mathbb T:\ 0<i\le\Phi_{\max}(s)\},\qquad \mathcal A=\{(s,i)\in\mathbb T:\ 0<i\le\Phi_0(s)\},$$

where, with $\sigma_c=\gamma/(\beta-c)$,

$$\Phi_c(s)=\begin{cases} i_M, & 0<s<\sigma_c,\\ \sigma_c+i_M-s+\sigma_c\log(s/\sigma_c), & s\ge\sigma_c,\end{cases}$$

$\Phi_0$ corresponding to $c=0$ and $\Phi_{\max}$ to $c=u_{\max}$.

## Expansion

Under a constant control $c$ the quantity $s+i-\sigma_c\log s$ is conserved, so trajectories are the level curves of the SIR first integral and $i$ peaks exactly when $s=\sigma_c$. The boundary curve $\Phi_c$ for $s\ge\sigma_c$ is the level curve whose peak value is $i_M$; for $s<\sigma_c$, $i$ is already decreasing, so $i\le i_M$ suffices. Larger $c$ gives flatter level curves ("laminar flow": trajectories under different constant controls do not cross in the wrong direction), so applying $u_{\max}$ from below $\Phi_{\max}$ keeps the trajectory below $i_M$, while from above $\Phi_{\max}$ even the strongest control overshoots. The integro-differential identity $s+i-s_0-i_0=\gamma\int_0^t\frac{\dot s}{(\beta-u)s}$ is the time-varying version of the first integral.

## Depends on

- [Solutions of the Kermack–McKendrick SIR model](../../kermack-mckendrick-sir-model/is-solution.md)

## Sources

- Lorenzo Freddi, Dan Goreac, "Infinite horizon optimal control of a SIR epidemic under an ICU constraint", arXiv:2306.10513: Theorem 2.1 (well-posedness and invariance), Lemma 2.3 (integro-differential identity), Proposition 2.4 and Theorem 2.6 (asymptotics), Definition 3.1 and Theorems 3.2–3.3 (viable and safe sets). <https://doi.org/10.48550/arXiv.2306.10513> Published version: Journal of Convex Analysis, 31(4), 2024.
