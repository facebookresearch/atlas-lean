# Global dynamics of predator-mediated apparent competition

**Setting.** Two prey species that do not compete directly, a native prey $u$ and an invasive prey $v$, share a predator $w$:

$$\dot u=u\Bigl(1-\frac u{K_1}\Bigr)-wf_1(u),\qquad \dot v=v\Bigl(1-\frac v{K_2}\Bigr)-wf_2(v),\qquad \dot w=w\bigl(\beta_1f_1(u)+\beta_2f_2(v)-\theta\bigr),$$

with positive initial data, carrying capacities $K_i>0$, conversion efficiencies $\beta_i>0$ and predator mortality $\theta>0$. The functional responses are Holling type I, $f_i(s)=\alpha_is$, or Holling type II, $f_i(s)=\gamma_is/(1+\gamma_ih_is)$. Let $L_i=\beta_if_i(K_i)$, the predator's growth rate on prey $i$ at carrying capacity, $L=L_1+L_2$, and for type I

$$\theta_0=\max\Bigl\{\Bigl(1-\frac{\alpha_1}{\alpha_2}\Bigr)L_1,\ \Bigl(1-\frac{\alpha_2}{\alpha_1}\Bigr)L_2\Bigr\}\in[0,L),$$

with $\theta_0=0$ iff $\alpha_1=\alpha_2$. Equilibria include the predator-free state $E_{uv}=(K_1,K_2,0)$, the semi-coexistence states $P_1=\bigl(\theta/(\alpha_1\beta_1),0,(L_1-\theta)/(\alpha_1L_1)\bigr)$ (prey $v$ excluded) and $P_2$ (prey $u$ excluded), and a coexistence state $P_*$.

**Theorem 2.1 (Holling type I).**
1. If $\alpha_1<\alpha_2$ (respectively $\alpha_1>\alpha_2$) and $0<\theta\le\theta_0$, then $P_1$ (respectively $P_2$) is globally asymptotically stable: the prey that is captured less efficiently excludes the other through the shared predator.
2. If $\theta_0<\theta<L$, the unique coexistence equilibrium $P_*$ is globally asymptotically stable.
3. If $\theta\ge L$, the predator-free equilibrium $E_{uv}$ is globally asymptotically stable.

**Theorem 2.2 (Holling type II).** Let $f_i(s)=\gamma_is/(1+\gamma_ih_is)$, so $L_i=\beta_i\gamma_iK_i/(1+\gamma_ih_iK_i)$, and put $\lambda_i=1/(\gamma_ih_i)$. For $0<\theta<L_1$ the semi-coexistence state $Q_1=(u_{Q_1},0,w_{Q_1})$ has

$$u_{Q_1}=\frac{\theta}{(\beta_1-h_1\theta)\gamma_1},\qquad w_{Q_1}=\frac{\beta_1(L_1-\theta)}{\gamma_1f_1(K_1)(\beta_1-h_1\theta)^2},$$

and $Q_2=(0,v_{Q_2},w_{Q_2})$ is given symmetrically for $0<\theta<L_2$. Let $(u_0,v_0,w_0)$ be the initial data.
1. If $0<\theta<L_1$ and $(K_1,K_2)\in\Lambda_1:=\{K_1\le\lambda_1+u_{Q_1},\ K_2/f_2(K_2)\le w_{Q_1}\}$, with equality in the second condition allowed only when $v_0\le K_2$, then $Q_1$ is globally asymptotically stable.
2. If $0<\theta<L_2$ and $(K_1,K_2)\in\Lambda_2:=\{K_2\le\lambda_2+v_{Q_2},\ K_1/f_1(K_1)\le w_{Q_2}\}$, with equality in the second condition allowed only when $u_0\le K_1$, then $Q_2$ is globally asymptotically stable.
3. If $0<\theta<L$, a coexistence equilibrium $Q_*=(u_*,v_*,w_*)$ exists, and $(K_1,K_2)\in\Lambda_*:=\{K_1\le\lambda_1+u_*,\ K_2\le\lambda_2+v_*\}$, then $Q_*$ is globally asymptotically stable.
4. If $\theta\ge L$, $E_{uv}$ is globally asymptotically stable.

The sets $\Lambda_1,\Lambda_2,\Lambda_*$ are mutually disjoint; for $(K_1,K_2)$ outside their union and $0<\theta<L$ the global dynamics are left open, and a coexistence equilibrium need not exist for $\theta<L$.

## Expansion

For $\theta\ge L$ the predator cannot grow even when both prey are at carrying capacity, so $w\to0$ and the prey decouple. Below $L$, the predator persists; with linear responses, the classical Volterra-type Lyapunov function $V=\sum_i c_i(x_i-x_i^*-x_i^*\log(x_i/x_i^*))$ with suitable weights $c_i$ has a negative semidefinite derivative, and LaSalle's principle gives global convergence to whichever equilibrium is saturated (no species absent from it can invade). The threshold $\theta_0$ is where the excluded prey's invasion rate into the semi-coexistence state changes sign: low predator mortality means a high predator density at $P_1$ or $P_2$, which suppresses the prey with the larger capture rate below its viability. Thus an invasive prey that is less palatable can drive a native prey extinct purely through apparent competition, and raising predator mortality can restore coexistence.

## Sources

- Y. Lou, W. Tao, Z.-A. Wang, "Effects and biological consequences of the predator-mediated apparent competition I: ODE models", *Journal of Mathematical Biology* 91(5) (2025), 47, Theorem 2.1, Theorem 2.2 and Remark 2.2, Table 1, Section 5, <https://doi.org/10.1007/s00285-025-02286-x> (preprint arXiv:2502.00410).
