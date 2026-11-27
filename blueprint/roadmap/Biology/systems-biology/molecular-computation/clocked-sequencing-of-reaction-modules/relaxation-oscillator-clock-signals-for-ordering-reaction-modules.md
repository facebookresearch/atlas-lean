# Relaxation-oscillator clock signals for ordering chemical reaction modules

**Problem.** A reaction module $\mathcal M_j$ is a mass-action network whose stable equilibrium encodes a computation (for example $S_1\to S_1+S_2$, $S_3\to S_3+S_2$, $S_2\to\emptyset$ computes $s_2^*=s_1^*+s_3^*$; $S_2\to S_1+S_2$, $S_1\to\emptyset$ computes $s_1^*=s_2^*$; alternating them implements the increment $s_1\leftarrow s_1+1$). Executing modules in order requires **symmetrical clock signals** $V_1,\dots,V_m$: species oscillating with a common period $T$ split into $m$ equal segments, with only $V_j$ appreciably positive in segment $j$. Each reaction of $\mathcal M_j$ is catalyzed by $V_j$, so it runs only in its segment.

**Oscillator.** A relaxation oscillator with truncated-subtraction readout,

$$\epsilon_1\dot x=\eta_1(\varphi(x)-y)x,\qquad \dot y=\eta_1(x-\ell)y,$$

$$\epsilon_1\epsilon_2\dot u=\eta_1\big(\epsilon_1(p-u)-uv\big),\qquad \epsilon_1\epsilon_2\dot v=\eta_1\big(\epsilon_1(x-v)-uv\big),$$

with cubic critical manifold $\varphi(x)=-x^3+bx^2+cx+d$ and $0<\epsilon_1,\epsilon_2\ll1$, produces square-wave-like $u,v$ that switch with the jumps of $x$ (the uv pair computes truncated differences, so one is near zero while the other is high). It is realizable by mass action and oscillates when $b>0$, $c<0$, $-3c<b^2<-4c$, $d>d_0=\big(-b(b-\sqrt{b^2+3c})^2-6c(b-\sqrt{b^2+3c})\big)/27$, and the nullcline parameter $\ell$ lies between the fold points $x_m<x_M$, the roots of $\varphi'(x)=-3x^2+2bx+c$. The relaxation orbit has vertices $(x_l,\varphi(x_M))$, $(x_m,\varphi(x_m))$, $(x_M,\varphi(x_M))$ and $(x_h,\varphi(x_m))$ with $x_l<x_m<x_M<x_h$, and these conditions keep it in the open first quadrant. During the low phase $|v_j|<\frac{x_m}{p-x_m}\epsilon_1=O(\epsilon_1)$.

**Theorem (duty ratio is unbounded).** To leading order in $\epsilon_1$, the times $T_1$ and $T_2$ spent on the slow branches $x_l\le x\le x_m$ and $x_M\le x\le x_h$ are $\int_{x_l}^{x_m}\frac{\varphi'(x)\,dx}{\eta_1(x-\ell)\varphi(x)}$ and $\int_{x_h}^{x_M}\frac{\varphi'(x)\,dx}{\eta_1(x-\ell)\varphi(x)}$, and their ratio decreases in $\ell$ on $(x_m,x_M)$. As $\ell\downarrow x_m$ the source approximates it by

$$R(b,c,d)=\frac{\int_{x_l}^{x_m}\frac{x_M-x}{\varphi(x)}\,dx}{\int_{x_h}^{x_M}\frac{x_M-x}{\varphi(x)}\,dx}.$$

At the boundary $c=-b^2/4$, $d=d_0$ (where $x_l=0$, $x_m=b/6$, $x_M=b/2$, $x_h=2b/3$ and $\varphi(x)=-(x-\frac b6)^2(x-\frac{2b}3)$), the perturbed ratio

$$R(b,\alpha,\beta)=\frac{\int_0^{b/6}\frac{b/2-x}{-((x-b/6)^2+\alpha)(x-2b/3-\beta)}\,dx}{\int_{2b/3}^{b/2}\frac{b/2-x}{-((x-b/6)^2+\alpha)(x-2b/3-\beta)}\,dx},\qquad 0<\alpha,\beta,$$

satisfies $\lim_{\alpha,\beta\to0}R(b,\alpha,\beta)=\infty$ for every $b>0$ whenever $\lim\beta/\alpha\ne0$. Hence the duty ratio can be tuned over the range needed to split the period into $m$ segments, giving clock signals for regulating an arbitrary number of modules.

**Theorem (error control).** In segment $j$, module $\mathcal M_j$ updates species $s_1,\dots,s_{l_j}$ with kinetics $\dot s_i=h_{i,j}(\mathbf s)\,v_j$, while the other modules contribute $H_i(\mathbf s)=\sum_{k\ne j}h_{i,k}(\mathbf s)$ weighted by their clock signals, which are $O(\epsilon)$ in this segment. Module equilibria must be stable, which forces $\partial h_{i,j}/\partial s_i\le0$. Write the solution at the end $t_2$ of the segment as $\mathbf s(t_2)=\mathbf s_0(t_2)+\epsilon\,(\mathbf P(t_2),\mathbf Q(t_2))$, where $\mathbf s_0$ solves the system with the other clock signals set to zero, $\mathbf P$ collects the updated species and $\mathbf Q$ the others, and let $H_0$ bound $|H_i(\mathbf s)|$ along the trajectory. Then $|\mathbf Q(t_2)|\le H_0T/m$ componentwise, and $\mathbf P(t_2)$ is bounded by a constant multiple of $H_0T/m$ in two cases: when the module updates one species ($l_j=1$), and when the module kinetics are linear, $\mathbf h(\mathbf s)=\mathbf H\mathbf s+\mathbf c$, and $I-\rho\mathbf H_1$ is positive definite, where $\mathbf H_1$ is the leading $l_j\times l_j$ principal submatrix of $\mathbf H$ and $\rho=(x_h-p)T/m$.

## Depends on

- [Chemical reaction network theory](../../chemical-reaction-network-theory/README.md)

## Expansion

Relaxation oscillations alternate slow drift along the two attracting branches of the cubic critical manifold with fast jumps between them, so $x$ is close to a two-level signal; the fast $u,v$ subsystem converts it into complementary signals that are $O(\epsilon_1)$ in their low phase. Branch residence times are integrals of $\varphi'(x)/((x-\ell)\varphi(x))$ along each branch, and pushing the lower fold point towards the $x$-axis makes the lower-branch time blow up relative to the upper, which tunes duty cycles to $1/m$. The residual low-phase signal makes off-segment modules leak; linearizing the leak and comparing with the stable module dynamics gives the matrix inequalities and the $T/m$ scaling of the error.

## Sources

- X. Shi, C. Gao, D. Dochain, "Controlling the occurrence sequence of reaction modules through biochemical relaxation oscillators", *Automatica* 176 (2025), 112261, Section 3 (Example 3.1, Definition 3.2, Lemmas 3.3-3.4, Theorem 3.5) and Section 4 (Lemmas 4.1, 4.2, 4.4, Theorem 4.5), <https://doi.org/10.1016/j.automatica.2025.112261> (preprint arXiv:2401.02061).
