# Linear noise approximation of density-dependent reaction networks

**Setting.** A reaction network with $n$ species and $r$ reactions has copy-number process $Y(t)\in\mathbb Z_{\ge0}^n$ that jumps by the stoichiometric vector $\nu_j$ at rate $\pi_j(Y)$, $j=1,\dots,r$; equivalently $Y(t)=Y(0)+\sum_j\nu_jN_j\bigl(\int_0^t\pi_j(Y(s))\,ds\bigr)$ with independent unit-rate Poisson processes $N_j$. Assume density dependence with system size $\Omega$: $\pi_j(y)=\Omega\rho_j(y/\Omega)$ with smooth macroscopic rates $\rho_j$, and set $X(t)=Y(t)/\Omega$. The reaction rate equation (RRE) is

$$\dot x=F(x)=\sum_{j=1}^r\nu_j\rho_j(x),$$

with Jacobian $J(x)=\partial F/\partial x$, stoichiometry matrix $S=[\nu_1\cdots\nu_r]$ and $E(x)=S\,\mathrm{diag}\bigl(\sqrt{\rho_1(x)},\dots,\sqrt{\rho_r(x)}\bigr)$.

**Statement.** Let $x(t)$ solve the RRE with $x(0)=x_0$. The linear noise approximation (LNA) is the ansatz

$$X(t)=x(t)+\Omega^{-1/2}\xi(t),\qquad d\xi=J(x(t))\,\xi\,dt+E(x(t))\,dB_t,$$

with $B$ an $r$-dimensional Wiener process. Its solution is Gaussian with explicit transitions: for $0\le s<t$,

$$\xi(t)=C(s,t)\,\xi(s)+\eta(s,t),\qquad \eta(s,t)\sim\mathrm{MVN}\bigl(0,D(s,t)\bigr),$$

where the fundamental matrix and the covariance solve

$$\partial_tC=J(x(t))\,C,\quad C(s,s)=I,\qquad \partial_tD=J(x(t))\,D+D\,J(x(t))^\top+E(x(t))E(x(t))^\top,\quad D(s,s)=0 .$$

Thus, from a Gaussian initial fluctuation $\xi(0)$, the LNA distribution of $X(t)$ is $\mathrm{MVN}\bigl(x(t)+\Omega^{-1/2}C(0,t)\,\mathbb E\xi(0),\ \Omega^{-1}[C(0,t)\mathrm{Cov}(\xi(0))C(0,t)^\top+D(0,t)]\bigr)$, obtained by solving ordinary differential equations only. By Kurtz's theorems, $X\to x$ in probability as $\Omega\to\infty$ on compact time intervals and $\sqrt\Omega\,(X-x)$ converges to the Gaussian process $\xi$.

## Depends on

- [Chemical reaction network](../../../../Dynamics/smooth-dynamics/reaction-network.md)

## Expansion

Writing the scaled jump equation $X(t+dt)-X(t)=\sum_j\frac{\nu_j}{\Omega}N_j\bigl(\Omega\rho_j(X(t))\,dt\bigr)$, the law of large numbers for Poisson variables gives the RRE in the limit. The centered Poisson increments have variance $\Omega\rho_j\,dt$, so after scaling by $\Omega^{-1/2}$ they become independent Gaussian increments $\sqrt{\rho_j}\,dB_j$, which produces the diffusion matrix $E E^\top=S\,\mathrm{diag}(\rho)\,S^\top$. Linearizing the drift $F(x+\Omega^{-1/2}\xi)$ around $x(t)$ gives the drift $J\xi$, and the Gaussian transition law follows from variation of constants for linear SDEs. For the SIR network $S+I\to2I$, $I\to R$ with rates $\tilde c_1x_1x_2$ and $c_2x_2$, the RRE is the classical SIR system and the LNA gives its Gaussian fluctuations. The approximation is accurate over long times only when the dynamics are close to linear: for oscillatory or multistable RREs the stochastic path drifts away in phase from $x(t)$ while the LNA keeps linearizing around $x(t)$.

## Sources

- Frederick Truman-Williams, Giorgos Minas, "Simulating stochastic population dynamics: The Linear Noise Approximation can capture non-linear phenomena", *SIAM Journal on Applied Dynamical Systems* 25(3) (2026), 1911–1938, Section "System Size Expansion", Section "The Linear Noise Approximation (LNA)" and Supplementary Section "The derivation of the Linear Noise Approximation (LNA)", <https://doi.org/10.1137/25m1789792> (preprint arXiv:2504.15166).
- N. G. van Kampen, "Stochastic Processes in Physics and Chemistry", North-Holland (1992)
