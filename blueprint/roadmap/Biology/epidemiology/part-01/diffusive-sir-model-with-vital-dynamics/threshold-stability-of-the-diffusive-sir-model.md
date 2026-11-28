# Threshold stability of the diffusive SIR model with vital dynamics

**Model.** On a bounded domain $\Omega\subset\mathbb R^m$ with smooth boundary, let $S,I,R\ge 0$ be the local densities of susceptible, infected and removed individuals, with common diffusion (mobility) rate $\varepsilon>0$, recruitment $\Lambda>0$, transmission $\beta>0$, recovery $\gamma>0$, natural death $\mu>0$ and a constant intervention factor $\Theta\in(0,1]$:

$$\begin{aligned}
\partial_t S&=\varepsilon\Delta S+\Lambda-\beta\Theta SI-\mu S,\\
\partial_t I&=\varepsilon\Delta I+\beta\Theta SI-(\gamma+\mu)I,\\
\partial_t R&=\varepsilon\Delta R+\gamma I-\mu R,
\end{aligned}$$

with nonnegative, not identically zero initial data and homogeneous Neumann conditions $\partial_n S=\partial_n I=\partial_n R=0$ on $\partial\Omega$.

**Theorem 1 (positivity and boundedness).** Solutions stay nonnegative, and $N=S+I+R$ satisfies $\limsup_{t\to\infty}\sup_{x\in\Omega}N(t,x)\le\Lambda/\mu$.

**Equilibria.** Set

$$\mathcal R_0=\frac{\Lambda\beta\Theta}{\mu(\mu+\gamma)}.$$

The disease-free equilibrium is $E_1=(\Lambda/\mu,0,0)$. If $\mathcal R_0>1$ there is a unique endemic equilibrium $E_2=(S^*,I^*,R^*)$ with

$$S^*=\frac{\gamma+\mu}{\beta\Theta},\qquad I^*=\frac{\Lambda}{\gamma+\mu}-\frac{\mu}{\beta\Theta},\qquad R^*=\frac{\gamma}{\mu}I^*.$$

**Theorems 2-5 (threshold dynamics).** If $\mathcal R_0<1$, $E_1$ is locally and globally asymptotically stable (and it is unstable if $\mathcal R_0>1$). If $\mathcal R_0>1$, $E_2$ is locally and globally asymptotically stable among positive solutions.

## Depends on

- [Next-generation matrix basic reproduction number](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [Routh–Hurwitz criterion for cubic polynomials](../../../../Analysis/control-theory/feedback-stability-and-classical-design/routh-hurwitz-criterion-for-cubic-polynomials.md)

## Informally uses

- [Forward invariance of compact sublevel sets and LaSalle's principle for differential equations](../../../../Analysis/ordinary-differential-equations/forward-invariance-of-compact-sublevel-sets-and-lasalle-s-principle.md)

## Expansion

Local stability: expanding perturbations in the Neumann eigenfunctions of $-\Delta$ with eigenvalues $k^2\ge0$ gives, at $E_1$, the factors $\lambda+\varepsilon k^2+\mu$ (twice) and $\lambda+\varepsilon k^2+(\gamma+\mu)(1-\mathcal R_0)$, so all modes decay iff $\mathcal R_0<1$; at $E_2$ a cubic whose Routh-Hurwitz coefficients are positive when $\mathcal R_0>1$. Global stability uses Volterra-type Lyapunov functionals

$$L_1=\int_\Omega\Big(S-\tfrac{\Lambda}{\mu}-\tfrac{\Lambda}{\mu}\ln\tfrac{\mu S}{\Lambda}+I\Big)\,dx,\qquad
L_2=\int_\Omega\Big(S-S^*-S^*\ln\tfrac{S}{S^*}+I-I^*-I^*\ln\tfrac{I}{I^*}\Big)\,dx.$$

The reaction terms give the familiar nonpositive ODE derivative, and by the divergence theorem with Neumann conditions each diffusion term contributes $-\varepsilon c\int_\Omega\|\nabla u\|^2/u^2\,dx\le0$, so diffusion cannot destabilize either equilibrium; LaSalle's invariance principle concludes.

## Sources

- Li R, Song Y, Wang H, Jiang GP, Xiao M, "Reactive-diffusion epidemic model on human mobility networks: Analysis and applications to COVID-19 in China", Physica A 2022 Nov 21;609:128337, Equations (4)-(6), Theorems 1-5 and the Lyapunov functionals (28), <https://doi.org/10.1016/j.physa.2022.128337>, PMCID PMC9677564.
