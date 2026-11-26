# Competitive exclusion of strains in the density-scaled two-strain SIR model

**Model.** A population grows exponentially at net rate $\lambda-\mu$ (births $\lambda N$, deaths $\mu$ per capita, no disease mortality). Two strains with contact rates $\beta_1,\beta_2$ and removal rates $\gamma_1,\gamma_2$ compete for susceptibles without coinfection, and susceptibles are vaccinated at rate $\omega$:

$$
\begin{aligned}
\dot S&=\lambda N-\beta_1S\tfrac{I_1}{N}-\beta_2S\tfrac{I_2}{N}-(\omega+\mu)S,\qquad
\dot I_i=\beta_iS\tfrac{I_i}{N}-(\gamma_i+\mu)I_i\ (i=1,2),\\
\dot R&=\gamma_1I_1+\gamma_2I_2+\omega S-\mu R,\qquad N(t)=N_0e^{(\lambda-\mu)t}.
\end{aligned}
$$

In proportions $x=S/N$, $y=I_1/N$, $z=I_2/N$ the mortality cancels and

$$
\dot x=\lambda(1-x)-\omega x-\beta_1xy-\beta_2xz,\qquad \dot y=y\,\psi_1(x),\qquad \dot z=z\,\psi_2(x),\qquad \psi_i(x)=\beta_ix-\gamma_i-\lambda,
$$

on the compact invariant simplex $x+y+z\le1$, $x>0$, $y,z\ge0$.

**Theorem.**

1. *(Competitive exclusion.)* If $\gamma_2>\gamma_1$ and $\beta_2-\beta_1<\gamma_2-\gamma_1$, then $z(t)\to0$ for every solution with $y(0)>0$: strain 1 outcompetes strain 2, whether the dynamics are stationary or oscillatory.
2. *(Equilibria and global stability.)* Let $x_i=(\gamma_i+\lambda)/\beta_i$ and $F_1(x)=\frac{\lambda(1-x)-\omega x}{\beta_1x}$. The disease-free state $(\lambda/(\lambda+\omega),0,0)$ always exists, and is globally asymptotically stable if $x_1,x_2\ge\lambda/(\lambda+\omega)$. If $x_1<\min\{x_2,\lambda/(\lambda+\omega)\}$, the endemic equilibrium $(x_1,F_1(x_1),0)$ is globally asymptotically stable in the positive octant and in the positive $xy$-plane; symmetrically for strain 2.

Consequently, evolution selects the strain with the smallest susceptible threshold $x_i=(\gamma_i+\lambda)/\beta_i$, i.e. it maximizes the ability to raise the *proportion* of infected individuals, as long as stochastic oscillations keep $x$ near its deterministic equilibrium.

## Expansion

The ratio of the two infected classes satisfies $\frac{d}{dt}\frac yz=\frac yz\big(\psi_1(x)-\psi_2(x)\big)=\frac yz\big((\beta_1-\beta_2)x+\gamma_2-\gamma_1\big)$. The bracket is affine in $x$ and positive at $x=0$ and $x=1$ under the hypotheses, hence positive on $[0,1]$; so $y/z$ increases without bound along every solution and, since proportions are bounded, $z\to0$. Global stability of the strain-1 endemic state uses the Lyapunov function $W=x_2\Big(\int_{x_1}^{x}\frac{\psi_1(s)}{\beta_1s}ds+\int_{F_1(x_1)}^{y}\frac{s-F_1(x_1)}{s}ds\Big)+x_1z$, whose derivative is $x_2\psi_1(x)\big(F_1(x)-F_1(x_1)\big)+\beta_2x\,z\,(x_1-x_2)\le0$ because $F_1$ is decreasing and $x_1<x_2$; LaSalle's principle concludes. The density threshold involves the birth rate $\lambda$ rather than $\mu$, so $R_0$ (which counts infected numbers) is not the threshold for proportions. With realistic parameters ($\lambda,\mu$ tiny compared with $\beta,\gamma$) the endemic proportion of infected is very small, so the deterministic prediction is carried by few individuals; the stochastic counterpart then shows large oscillations and extinction, more violently in small isolated populations.

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Sources

- Torsten Lindström, "On the stochastic engine of transmittable diseases in exponentially growing populations", arXiv:2104.03254 (2021), Sections 2–4: model and density formulation, Theorem 1 (competitive exclusion), Theorem 2 and Remark 1 (global stability), <https://doi.org/10.48550/arXiv.2104.03254>.
