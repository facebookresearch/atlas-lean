# Pulsating traveling waves of the hybrid wild-type–mutant system exist exactly above the spreading speed

**Model.** Two pathogen strains (wild type $u$, mutant $v$) in an $L$-periodic environment, obtained from an SIS model with mutation:
$$\begin{aligned}u_t&=(\sigma(x)u_x)_x+\big(r_u(x)-\kappa_u(x)(u+v)\big)u+\mu_v(x)v-\mu_u(x)u,\\ v_t&=(\sigma(x)v_x)_x+\big(r_v(x)-\kappa_v(x)(u+v)\big)v+\mu_u(x)u-\mu_v(x)v,\end{aligned}\qquad t>0,\ x\in\mathbb{R},$$
with $L$-periodic continuous coefficients, $\sigma\in C^1$, $\sigma,\kappa_u,\kappa_v,\mu_u,\mu_v>0$ and growth rates $r_u,r_v$ of arbitrary sign. The system is cooperative through mutation and competitive through the shared crowding term, so it has no comparison principle.

**Principal eigenvalues.** For $\lambda\in\mathbb{R}$, let $k(\lambda)$ be the principal eigenvalue of the linearization at $0$ acting on $\lambda$-exponentially weighted periodic pairs $(\varphi,\psi)>0$ (the $\lambda$-periodic principal eigenvalue), and let $\lambda_1^{per}=k(0)$. If $\lambda_1^{per}>0$, front-like data spread to the right at speed
$$c_R^*=\min_{\lambda>0}\frac{k(\lambda)}{\lambda},\qquad\text{and to the left at}\qquad c_L^*=\min_{\lambda>0}\frac{k(-\lambda)}{\lambda}.$$

A **right pulsating traveling wave** of speed $c>0$ is an entire solution with $u(t+L/c,x)=u(t,x+L)$, $v(t+L/c,x)=v(t,x+L)$, vanishing as $x\to+\infty$ and staying bounded away from $0$ as $x\to-\infty$.

**Theorem.** Assume $\lambda_1^{per}>0$.
1. If $c_R^*>0$, a right pulsating traveling wave of speed $c$ exists **if and only if** $c\ge c_R^*$; symmetrically, if $c_L^*>0$, a left wave of speed $c$ exists iff $c\ge c_L^*$. So the spreading speed equals the minimal wave speed in each direction.
2. If $c_R^*=0$, there is a right stationary wave, and right traveling waves exist exactly for $c>0$.
3. If $\kappa_{\max}/\kappa_{\min}\le \mu_{\min}/r_{\max}$, then for each admissible speed the wave is unique up to a time shift and increasing in $t$.
4. The two speeds can differ: in a multi-scale example with mutation concentrated on thin intervals, $c_R^*<c_L^*$ for all small scale parameters.

## Expansion

Without a comparison principle, waves are built from the solution map over one period acting on a set squeezed between exponential sub- and super-barriers $e^{-\lambda(x-ct)}(\varphi^\lambda,\psi^\lambda)$ given by the principal eigenpairs, with a fixed-point argument followed by a limit for the critical speed. Nonexistence below $c_R^*$ follows from the spreading result: a wave slower than $c_R^*$ would be overtaken by the solution started from its own front-like data. The asymmetry $c_R^*\ne c_L^*$ is possible because $k(\lambda)$ need not be even once the mutation matrix and the coefficients lack a reflection symmetry.

## Sources

- Quentin Griette and Hiroshi Matano, "Front propagation in hybrid reaction-diffusion epidemic models with spatial heterogeneity. Part II: Pulsating traveling waves", arXiv:2607.11869 (2026), Theorems 2.7, 2.13, 2.15, 2.19 and 2.22, Section 2, <https://doi.org/10.48550/arXiv.2607.11869>.
