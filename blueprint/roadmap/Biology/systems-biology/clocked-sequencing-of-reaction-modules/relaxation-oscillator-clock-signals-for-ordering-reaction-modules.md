# Relaxation-oscillator clock signals for ordering chemical reaction modules

**Problem.** A reaction module $\mathcal M_j$ is a mass-action network whose stable equilibrium encodes a computation (for example $S_1\to S_1+S_2$, $S_3\to S_3+S_2$, $S_2\to\emptyset$ computes $s_2^*=s_1^*+s_3^*$; $S_2\to S_1+S_2$, $S_1\to\emptyset$ computes $s_1^*=s_2^*$; alternating them implements the increment $s_1\leftarrow s_1+1$). Executing modules in order requires **symmetrical clock signals** $V_1,\dots,V_m$: species oscillating with a common period $T$ split into $m$ equal segments, with only $V_j$ appreciably positive in segment $j$. Each reaction of $\mathcal M_j$ is catalyzed by $V_j$, so it runs only in its segment.

**Oscillator.** A relaxation oscillator with truncated-subtraction readout,
$$\epsilon_1\dot x=\eta_1(\varphi(x)-y)x,\qquad \dot y=\eta_1(x-\ell)y,$$
$$\epsilon_1\epsilon_2\dot u=\eta_1\big(\epsilon_1(p-u)-uv\big),\qquad \epsilon_1\epsilon_2\dot v=\eta_1\big(\epsilon_1(x-v)-uv\big),$$
with cubic critical manifold $\varphi(x)=-x^3+bx^2+cx+d$ and $0<\epsilon_1,\epsilon_2\ll1$, produces square-wave-like $u,v$ that switch with the jumps of $x$ (the uv pair computes truncated differences, so one is near zero while the other is high). It is realizable by mass action and oscillates when $b>0$, $c<0$, $-3c<b^2<-4c$, $d$ exceeds an explicit threshold $d_0$, and the nullcline parameter $\ell$ lies between the fold points $x_m<\ell<x_M$. During the low phase $|v_j|<\frac{x_m}{p-x_m}\epsilon_1=O(\epsilon_1)$.

**Theorem (duty ratio is unbounded).** The ratio $T_1/T_2$ of time spent on the two slow branches decreases in $\ell$ and is approximated by an explicit integral ratio $R(b,c,d)$; at the boundary $c=-b^2/4$, $d\downarrow d_0$, a regularized version satisfies $\lim_{\alpha,\beta\to0}R(b,\alpha,\beta)=\infty$ for every $b>0$ whenever $\beta/\alpha\not\to0$. Hence the duty ratio can be tuned over the range needed to split the period into $m$ segments, giving clock signals for regulating an arbitrary number of modules.

**Theorem (error control).** Module equilibria must be stable, which forces $\partial h_{i,j}/\partial s_i\le0$ for the module vector fields. The terminal error accumulated in a segment, caused by the non-zero low phase of the other clock signals, is bounded, with bound proportional to $H_0T/m$ ($H_0$ bounding the interfering vector fields), when a module updates one species, when $I-\rho H_1$ is positive definite for linear modules ($\rho=(x_h-p)T/m$), or under positive definiteness of two explicit comparison matrices in general.

## Depends on

- [Chemical reaction network theory](../chemical-reaction-network-theory/README.md)

## Expansion

Relaxation oscillations alternate slow drift along the two attracting branches of the cubic critical manifold with fast jumps between them, so $x$ is close to a two-level signal; the fast $u,v$ subsystem converts it into complementary signals that are $O(\epsilon_1)$ in their low phase. Branch residence times are integrals of $\varphi'(x)/((x-\ell)\varphi(x))$ along each branch, and pushing the lower fold point towards the $x$-axis makes the lower-branch time blow up relative to the upper, which tunes duty cycles to $1/m$. The residual low-phase signal makes off-segment modules leak; linearizing the leak and comparing with the stable module dynamics gives the matrix inequalities and the $T/m$ scaling of the error.

## Sources

- X. Shi, C. Gao, D. Dochain, "Controlling the occurrence sequence of reaction modules through biochemical relaxation oscillators", arXiv:2401.02061 (2024), Section 3 (Example 3.1, Definition 3.2, Lemmas 3.3-3.4, Theorem 3.5) and Section 4 (Lemmas 4.1, 4.2, 4.4, Theorem 4.5), <https://doi.org/10.48550/arXiv.2401.02061>.
