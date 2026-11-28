# Tolerance as competition between transients approaching a stable node

**Setting.** Consider a planar system $\dot x=f(x,y)$, $\dot y=g(x,y)$ with $f,g$ locally Lipschitz and a stable node at the origin with real negative eigenvalues (A1). A *reference* trajectory $\phi$ starts at $(x_r,y_r)$ and a *pre-conditioned* trajectory $\psi$ starts at $(x_p,y_p)$. Both stay in the closed positive quadrant and in the basin of the origin (A2), and the pre-conditioned trajectory starts ahead, $x_p\ge x_r$ (A3). The system **exhibits tolerance** for $\langle(x_r,y_r),(x_p,y_p)\rangle$ if $\psi_1(\tau)<\phi_1(\tau)$ for some $\tau>0$: the first component of the pre-conditioned solution overtakes, and falls below, that of the reference solution on the way to equilibrium. This abstracts endotoxin tolerance, where a prior stimulus lowers the later inflammatory response.

**Results.**

*(1) Robustness.* Tolerance persists on an open time interval around $\tau$ and under small perturbations of either initial condition. At the first crossing time $t_1$ one has $\psi_1(t_1)=\phi_1(t_1)$ and $f(\psi(t_1))\le f(\phi(t_1))$.

*(2) Obstruction.* If $\phi_1,\psi_1\to0$ monotonically and $(x_p,y_p)$ lies on the backward orbit of $(x_r,y_r)$, so that $\psi$ is a time-shift of $\phi$, there is no tolerance. If $x_p>M=\max_{t\ge0}\phi_1(t)$, the graph of $\psi$ is bounded above by that of $\phi$ ($\psi_2(s_2)<\phi_2(s_1)$ whenever $\psi_1(s_2)=\phi_1(s_1)$) and $y$ inhibits $x$ ($f$ is decreasing in $y$) in a region containing both trajectories, there is no tolerance either. If instead the graph of $\psi$ is bounded below by that of $\phi$ ($\psi_2(s_2)>\phi_2(s_1)$ whenever $\psi_1(s_2)=\phi_1(s_1)$), tolerance requires a region of inhibition containing points $\psi(s_2)$, $\phi(s_1)$ with $\psi_1(s_2)=\phi_1(s_1)$.

*(3) Linear systems, distinct eigenvalues.* For $\dot{\mathbf x}=A\mathbf x$ with eigenvalues $\lambda_2<\lambda_1<0$ and eigenvectors $v$, $w$, write $(x_r,y_r)=c_1v+c_2w$ and $(x_p,y_p)=d_1v+d_2w$.

*(3a)* If $v_1=0$ (the slow eigenvector is vertical) or $w_1=0$, tolerance never occurs.

*(3b)* If $v_1=w_1=1$, tolerance holds for all $t>T$ iff $c_1>d_1$ and $c_2<d_2$, with

$$T=\frac{\ln\big[(d_2-c_2)/(c_1-d_1)\big]}{\lambda_1-\lambda_2}.$$

*(4) Linear systems, repeated eigenvalue.* If $\lambda_1=\lambda_2<0$ with two independent eigenvectors, tolerance is impossible. With a one-dimensional eigenspace, tolerance is decided explicitly by the coefficients along the eigenvector and the generalized eigenvector.

## Expansion

For a linear node, $\psi_1(t)-\phi_1(t)=(d_1-c_1)e^{\lambda_1t}+(d_2-c_2)e^{\lambda_2t}$. The fast mode $e^{\lambda_2t}$ dominates early and the slow mode $e^{\lambda_1t}$ dominates late, so the sign of the difference changes exactly once when the two coefficients have opposite signs. A pre-conditioned state that starts ahead in the fast direction but behind in the slow direction therefore ends up below the reference: tolerance is a competition between transients rather than a property of the equilibrium. In nonlinear systems the same mechanism is localized. Crossing requires the vector field to slow $x$ more along $\psi$ than along $\phi$ at the crossing point, which in biological networks means that the variable $y$ primed by the first stimulus inhibits $x$.

## Sources

- Judy Day, Jonathan Rubin, Carson C. Chow, "Competition between transients in the rate of approach to a fixed point", arXiv:0804.0248 (2008), Section 2 (definitions of tolerance, assumptions (A1)–(A3), robustness propositions), Section 3 (sufficient and necessary conditions, regions of inhibition) and Section 4 (complete analysis of planar linear systems), <https://doi.org/10.48550/arXiv.0804.0248>.
