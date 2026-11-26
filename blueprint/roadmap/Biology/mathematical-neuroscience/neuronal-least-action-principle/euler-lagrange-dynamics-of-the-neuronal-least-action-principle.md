# Euler–Lagrange dynamics of the neuronal least-action principle

**Setting.** Network neurons $i \in N$ have somatic voltages $u_i(t)$, input weights $W = (W_{\mathrm{in}}, W_{\mathrm{net}})$ and transfer function $\rho$; $\bar r_j = \rho(u_j)$ is the low-pass filtered (time constant $\tau$) rate of neuron $j$ (inputs included). The somato-dendritic mismatch error is $\bar e_i = u_i - \sum_jW_{ij}\bar r_j$, with mismatch energy $E^M_i = \tfrac12\bar e_i^2$. Output neurons $o \in O$ receive targets $u^*_o(t)$ with cost $C_o = \tfrac12(u^*_o - u_o)^2$. The **Lagrangian** with nudging strength $\beta \ge 0$ is

$$L = \frac12\sum_{i\in N}\Big(u_i - \sum_j W_{ij}\bar r_j\Big)^2 + \frac\beta2\sum_{o\in O}(u^*_o - u_o)^2.$$

The **prospective coordinates** are the discounted future voltages $\tilde u(t) = \frac1\tau\int_t^\infty u(t')e^{-(t'-t)/\tau}dt'$, so that $u = \tilde u - \tau\dot{\tilde u}$, and the **action** is $A = \int_{t_1}^{t_2}L[\tilde u(t),\dot{\tilde u}(t)]\,dt$.

**Theorem (least-action dynamics).** Trajectories with $\delta A = 0$ under variations of $\tilde u$ satisfy the Euler–Lagrange equations $\partial L/\partial\tilde u_i - \frac{d}{dt}\partial L/\partial\dot{\tilde u}_i = 0$, which reduce to

$$\tau\dot u = -u + Wr + e, \qquad \bar e = \bar r'_{\mathrm{net}}\odot W_{\mathrm{net}}^{\mathsf T}\bar e + \beta\,\bar e^*,$$

with prospective rates $r = \rho(u) + \tau\dot\rho(u)$, prospective errors $e = \bar e + \tau\dot{\bar e}$, target error $\bar e^*_o = u^*_o - u_o$ on outputs and $\bar e^*_i = 0$ elsewhere. Low-pass filtering the first equation gives the instantaneous moving equilibrium $u = W\bar r(u) + \bar e(u)$.

## Expansion

Since $u = \tilde u - \tau\dot{\tilde u}$, the Euler–Lagrange operator becomes $\big(1 + \tau\frac{d}{dt}\big)\frac{\partial}{\partial u_i}$, a look-ahead gradient; its kernel consists of functions decaying like $e^{-(t-t_0)/\tau}$, so after transients $\partial L/\partial u_i = 0$ along the trajectory, and this condition is the error equation. No acceleration term appears because the second derivative of $\tilde u$ is absorbed. The prospective rate is the inverse low-pass filter of $\rho(u)$, which is why a step change in one layer's voltage propagates to the next layer within an infinitesimal time and the input–output map $u_o = F_W(\bar r_{\mathrm{in}}, \bar e^*_o)$ is instantaneous regardless of depth. The error equation has the form of backpropagation through the transposed network weights.

## Sources

- W. Senn, D. Dold, A. F. Kungl, B. Ellenberger, J. Jordan, Y. Bengio, J. Sacramento, M. A. Petrovici, "A neuronal least-action principle for real-time learning in cortical circuits", eLife 12 (2024) RP89674, Results, Eqs (1)–(7b), and Methods (Euler–Lagrange equations as inverse low-pass filters; deriving the network dynamics), <https://doi.org/10.7554/eLife.89674>, PMCID PMC11661794.
