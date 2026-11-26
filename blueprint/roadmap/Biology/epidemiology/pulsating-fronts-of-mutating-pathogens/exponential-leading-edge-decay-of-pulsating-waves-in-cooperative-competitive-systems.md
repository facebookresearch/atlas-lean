# Exponential leading-edge decay of pulsating waves in cooperative–competitive systems

**Setting.** Let $(u,v)$ be a right pulsating traveling wave of speed $c\ge c_R^*>0$ for the periodic two-strain system
$$\begin{aligned}u_t&=(\sigma(x)u_x)_x+\big(r_u(x)-\kappa_u(x)(u+v)\big)u+\mu_v(x)v-\mu_u(x)u,\\ v_t&=(\sigma(x)v_x)_x+\big(r_v(x)-\kappa_v(x)(u+v)\big)v+\mu_u(x)u-\mu_v(x)v,\end{aligned}\qquad t>0,\ x\in\mathbb{R},$$
with $\lambda_1^{per}>0$, where $k(\lambda)$ is the $\lambda$-periodic principal eigenvalue of the linearization at $0$ with positive eigenvector $(\varphi^\lambda,\psi^\lambda)$.

**Theorem.**
1. *(Supercritical speed.)* If $c>c_R^*$ and $\lambda_c$ is the smallest positive root of $k(\lambda)=\lambda c$, there is $\alpha>0$ with
$$\lim_{x\to+\infty}\sup_{t\in[0,L/c]}\max\Big(\big|u\,e^{\lambda_c(x-ct)}-\alpha\varphi^{\lambda_c}(x)\big|,\ \big|v\,e^{\lambda_c(x-ct)}-\alpha\psi^{\lambda_c}(x)\big|\Big)=0.$$
2. *(Critical speed.)* If $c=c_R^*$ and $\lambda^*$ is the unique positive root of $k(\lambda)=\lambda c_R^*$, then for some $\alpha>0$ the same holds with the weight $e^{\lambda^*(x-c_R^*t)}/(x-c_R^*t)$, i.e. the leading edge decays like $(x-c^*_Rt)\,e^{-\lambda^*(x-c^*_Rt)}$.

These rates are those predicted by the linearization, and they hold for **every** traveling wave, not only the constructed ones, extending the scalar periodic KPP result of Hamel to a system without comparison principle.

## Depends on

- [Pulsating traveling waves of the hybrid wild-type–mutant system exist exactly above the spreading speed](pulsating-traveling-waves-of-the-hybrid-wild-type-mutant-system-exist-exactly-above-the-spreading-speed.md)

## Expansion

Far ahead of the front both densities are small, so the competition term is a perturbation and the wave solves, up to small error, a linear cooperative periodic system. Writing the wave in moving coordinates and expanding it along the principal Floquet–Bloch modes, the solution must pick the slowest admissible decay among the roots of $k(\lambda)=\lambda c$; at the critical speed the two roots merge, producing the extra linear factor exactly as in the scalar KPP case.

## Sources

- Quentin Griette and Hiroshi Matano, "Front propagation in hybrid reaction-diffusion epidemic models with spatial heterogeneity. Part II: Pulsating traveling waves", arXiv:2607.11869 (2026), Theorem 2.17 and Section 4, <https://doi.org/10.48550/arXiv.2607.11869>.
