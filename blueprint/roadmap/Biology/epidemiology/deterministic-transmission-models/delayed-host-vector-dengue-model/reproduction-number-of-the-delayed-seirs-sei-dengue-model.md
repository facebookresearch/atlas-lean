# Reproduction number of the delayed SEIRS–SEI dengue model

**Model (nondimensional).** Hosts $S_h,E_h,I_h,R_h$ and vectors $S_v,E_v,I_v$ satisfy

$$\dot S_h=1+\omega R_h-\lambda_hS_h-S_h,\quad \dot E_h=\alpha_1\lambda_hS_h-\sigma_hE_h,\quad \dot I_h=E_h-\xi_hI_h,\quad \dot R_h=I_h-\eta_hR_h,$$

$$\dot S_v=1-\lambda_vS_v-c_{1v}S_v,\quad \dot E_v=\alpha_2\lambda_vS_v-c_{2v}E_v,\quad \dot I_v=E_v-c_{1v}I_v,$$

with saturating forces of infection carrying the incubation delays,

$$\lambda_h=\frac{b_{1h}I_v(t-\tau_h)}{1+I_v(t-\tau_h)},\qquad \lambda_v=\frac{b_{1v}I_h(t-\tau_v)}{1+I_h(t-\tau_v)},$$

and recovery delayed by $\tau_r$ ($I_h$ replaced by $I_h(t-\tau_r)$ in the outflow terms); $\omega$ is the rate of loss of immunity and $\sigma_h,\xi_h,\eta_h,c_{1v},c_{2v}>1$ after scaling.

**Theorem.** The basic reproduction number is the spectral radius of the next-generation matrix,

$$R_0=\sqrt{\frac{A_1A_3}{\eta_h\sigma_h\xi_hA_5}}=\sqrt{\frac{b_{1h}b_{1v}\,\alpha_1\alpha_2}{\sigma_h\,\xi_h\,c_{1v}^2\,c_{2v}}},\qquad A_1=b_{1v}\alpha_1\eta_h,\ A_3=b_{1h}\alpha_2,\ A_5=c_{2v}c_{1v}^2 .$$

The equilibria do not depend on the delays. The disease-free equilibrium is $(1,0,0,0,1/c_{1v},0,0)$, and if $\sigma_h\xi_h\eta_h>\alpha_1\omega$, a unique positive endemic equilibrium exists iff $R_0>1$. For the model without delays ($\tau_h=\tau_v=\tau_r=0$) the disease-free equilibrium is locally asymptotically stable if $R_0<1$ and unstable if $R_0>1$. This threshold is not proved for the delayed model, and it fails there: when transmission vanishes ($b_{1h}b_{1v}\to0$), the linearization at the disease-free equilibrium has the factor $\lambda+\xi_he^{-\lambda\tau_r}$ coming from the delayed recovery term, which has roots with positive real part iff $\xi_h\tau_r>\pi/2$. By continuity of the roots, if $\xi_h\tau_r>\pi/2$ the disease-free equilibrium is unstable for all sufficiently small $b_{1h}b_{1v}$, where $R_0<1$. The delays $\tau_h,\tau_v,\tau_r$ do not enter $R_0$; they act on stability, which the paper studies by characteristic-equation analysis, numerical continuation and simulation, finding delay-induced Hopf oscillations, period doubling (a possible route to chaos).

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

At the disease-free state $S_h=1$ and $S_v=1/c_{1v}$. An infectious host lives $1/\xi_h$, infects vectors at rate $b_{1v}/c_{1v}$, a fraction $\alpha_2$ becomes exposed and a fraction $1/c_{2v}$ of those becomes infectious, giving $b_{1v}\alpha_2/(\xi_hc_{1v}c_{2v})$ infectious vectors per infectious host. An infectious vector lives $1/c_{1v}$ and produces $b_{1h}\alpha_1/(c_{1v}\sigma_h)$ infectious hosts. $R_0$ is the geometric mean of the two, i.e. the square root of their product, because a generation in the next-generation matrix is one host–vector or vector–host step. The incubation delays carry no mortality and the recovery delay does not change the equilibria, so no delay enters $R_0$; the recovery delay can still change the stability of the disease-free equilibrium, as above.

## Sources

- B. Gürbüz, A. Gökçe, S. I. Oke, M. O. Adeniyi, "Dynamical behavior and bifurcation analysis for a theoretical model of dengue fever transmission with incubation period and delayed recovery", *Mathematics and Computers in Simulation* 234 (2025), 497–513, nondimensional system (21)–(27), Eq. (R0S), Theorem 1, <https://doi.org/10.1016/j.matcom.2025.03.008> (preprint arXiv:2503.07875).
