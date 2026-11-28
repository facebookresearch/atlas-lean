# Network Turing instability of coupled Hindmarsh-Rose neurons

**Model.** Let $n$ Hindmarsh-Rose neurons with membrane potential $x_i$, recovery variable $y_i$ and slow bursting variable $z_i$ be coupled through a symmetric adjacency matrix $A$, with linearized diffusive coupling of strengths $d_1,d_2\ge 0$ and an optional delay $\tau\ge0$ in the slow feedback:

$$\begin{aligned}
\dot x_i&=y_i-ax_i^3+bx_i^2+I-z_i(t-\tau)+d_1\sum_j L_{ij}x_j,\\
\dot y_i&=c-dx_i^2-y_i+d_2\sum_j L_{ij}y_j,\\
\dot z_i&=r\big(s(x_i-x_r)-z_i\big),
\end{aligned}$$

where $L_{ij}=A_{ij}-q\,\delta_{ij}\sum_k A_{ik}$ is a (generalized) network Laplacian with real eigenvalues $\Lambda_k$ and orthonormal eigenvectors $v^k$. A homogeneous equilibrium $(x_0,y_0,z_0)$ solves $y_0-ax_0^3+bx_0^2+I-z_0=0$, $y_0=c-dx_0^2$, $z_0=s(x_0-x_r)$.

**Modal characteristic equation.** Writing perturbations as $\sum_k c_k e^{\lambda t}v^k$ decouples the linearization into one $3\times3$ problem per Laplacian eigenvalue. With $u_k=3ax_0^2-2bx_0-d_1\Lambda_k$ and $w_k=1-d_2\Lambda_k$, the characteristic equation of mode $k$ is

$$(\lambda+u_k)(\lambda+w_k)(\lambda+r)+2dx_0(\lambda+r)+rs\,(\lambda+w_k)\,e^{-\lambda\tau}=0 .$$

**Theorem 1 (Turing instability, $\tau=0$).** For $\tau=0$ write mode $k$'s equation as $\lambda^3+a_1\lambda^2+(a_2+a_3)\lambda+(a_4+a_5)=0$, with $a_3=rs$ and $a_5=rs\,w_k$. Suppose the uncoupled equilibrium ($\Lambda=0$) satisfies the Routh-Hurwitz conditions

$$a_1>0,\qquad a_2+a_3>0,\qquad a_4+a_5>0,\qquad a_1(a_2+a_3)-(a_4+a_5)>0 .$$

Mode $k$ is linearly stable iff the same four inequalities hold at $\Lambda=\Lambda_k$, and the network destabilizes the homogeneous state (network-driven Turing instability) if for some Laplacian eigenvalue $\Lambda_k$ one of

$$H_1:\ a_2+a_3<0,\qquad H_2:\ a_4+a_5<0,\qquad H_3:\ a_1(a_2+a_3)-(a_4+a_5)<0$$

holds at $\Lambda=\Lambda_k$. Write $a_2+a_3=b_1\Lambda^2+b_2\Lambda+b_3$ and $a_4+a_5=c_1\Lambda^2+c_2\Lambda+c_3$ as polynomials in $\Lambda=\Lambda_k$, with $b_1=d_1d_2$ and $c_1=rd_1d_2$. Then $H_1$ (resp. $H_2$) holds at $\Lambda_k$ iff $\Lambda_k$ lies in the set where $b_1\Lambda^2+b_2\Lambda+b_3$ (resp. $c_1\Lambda^2+c_2\Lambda+c_3$) is negative; for $d_1d_2>0$ this set is an open interval, nonempty iff the quadratic is negative at its vertex $-b_2/(2b_1)$ (resp. $-c_2/(2c_1)$). Since the $\Lambda_k$ form a discrete set, a nonempty interval need not contain any of them.

**Delay.** For $\tau>0$, substituting $\lambda=i\omega$ into mode $k$'s equation and eliminating $\cos\omega\tau$ and $\sin\omega\tau$ gives a quartic equation in $x=\omega^2$; each positive root $x_i$ gives $\omega_i=\sqrt{x_i}$ and a delay $\tau_i$ at which $\pm i\omega_i$ are roots. Let $\tau_0=\min_i\tau_i$ for the uncoupled system ($d_1=d_2=0$) and $\tau_c=\min_i\tau_i$ for the coupled one ($d_1\ne0$ or $d_2\ne0$), with frequencies $\omega_0$ and $\omega_c$. If the transversality condition $\mathrm{Re}\,\frac{d\lambda}{d\tau}>0$ holds at $\tau=\tau_c$, $\omega=\omega_c$, Turing instability occurs for $\tau_c<\tau<\tau_0$: below $\tau_0$ the uncoupled system is stable, and above $\tau_c$ the network destabilizes it.

## Proof depends on

- [Routh–Hurwitz criterion for cubic polynomials](../../../../Analysis/control-theory/feedback-stability-and-classical-design/routh-hurwitz-criterion-for-cubic-polynomials.md)

## Expansion

Expanding the determinant of $\lambda I-J_k$, with $J_k$ the Jacobian of the reaction terms plus $\mathrm{diag}(d_1\Lambda_k,d_2\Lambda_k,0)$, along the first row gives the modal equation above; the delayed feedback multiplies only the $z\to x$ entry by $e^{-\lambda\tau}$. Expanding it yields $a_1=u_k+w_k+r$, a coefficient $a_2+a_3$ of $\lambda$ that is quadratic in $\Lambda_k$ with leading coefficient $d_1d_2$, and a constant term $a_4+a_5$ that is quadratic with leading coefficient $rd_1d_2$. The Routh-Hurwitz criterion for cubics shows all roots of mode $k$ have negative real part iff the four inequalities hold, so instability of some nonzero mode, with the zero mode stable, is the Turing condition. Because the $\Lambda_k$ are determined by the network topology, changing the network (for example the link probability of a random graph) moves the spectrum into or out of the unstable band.

## Sources

- Zheng Q, Shen J, Zhang R, Guan L, Xu Y, "Spatiotemporal Patterns in a General Networked Hindmarsh-Rose Model", Front Physiol 2022 Jun 28;13:936982, Model (1), linearization (3), characteristic equations (5)-(8), conditions H1-H3, the critical delays $\tau_0,\tau_c$ and the transversality condition derived from Eq. (9), and Theorem 1 (whose delay interval, written $(\tau_0,\tau_c)$ there, is $\tau_c<\tau<\tau_0$ in the derivation before it), <https://doi.org/10.3389/fphys.2022.936982>, PMCID PMC9273822.
