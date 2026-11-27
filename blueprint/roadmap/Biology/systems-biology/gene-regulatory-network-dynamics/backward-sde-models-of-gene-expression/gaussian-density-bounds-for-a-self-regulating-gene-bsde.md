# Gaussian density bounds for a self-regulating gene expression BSDE

**Model.** One active gene synthesizes one protein, and the protein concentration $Y_t$ is reconstructed backward from an observed terminal concentration $\xi$ at time $T$. On a Brownian filtration with Brownian motion $W$, consider the backward stochastic differential equation

$$Y_t = \xi + \int_t^T \big(f(Y_s) - \rho Y_s\big)\,ds - \int_t^T Z_s\,dW_s, \qquad f(y) = R\,\frac{a y^2}{1 + a y^2},$$

where $R$ is the polymerase activation rate, $\rho$ the mRNA degradation rate, $a > 0$, and $f$ is a Hill function with coefficient $2$.

**Proposition (sign preservation).** If $\xi \ge 0$ almost surely (resp. $\xi \le 0$), then $Y_t \ge 0$ (resp. $Y_t \le 0$) almost surely for every $t \in [0, T]$.

**Proposition (Gaussian tails).** Let $R \ge 0$ and $\rho$ be real constants and let $\xi$ be Gaussian and Malliavin differentiable, $\xi \in \mathbb D^{1,2}$, with $0 < \underline k \le D_r\xi \le \overline k$ for all $r \in [0, T]$. Set

$$\overline C = \tfrac98 R\sqrt{a/3} - \rho, \qquad \underline C = -\tfrac98 R\sqrt{a/3} - \rho, \qquad C_{Y_t} = \tfrac12\,\mathbb E\big|Y_t - \mathbb E Y_t\big| .$$

Then for every $t \in (0, T]$ the law of $Y_t$ has a density $\rho_{Y_t}$, and for all $x \in \mathbb R$, with $\sigma_-^2 = \underline k^2\,t\,e^{2\underline C(T-t)}$ and $\sigma_+^2 = \overline k^2\,t\,e^{2\overline C(T-t)}$,

$$\frac{C_{Y_t}}{\sigma_+^2}\exp\Big(-\frac{(x - \mathbb E Y_t)^2}{2\sigma_-^2}\Big) \le \rho_{Y_t}(x) \le \frac{C_{Y_t}}{\sigma_-^2}\exp\Big(-\frac{(x - \mathbb E Y_t)^2}{2\sigma_+^2}\Big).$$

## Expansion

Sign preservation comes from linearization: writing the driver as $\big(R\,aY_s/(1 + aY_s^2) - \rho\big)Y_s$ and applying Itô's formula to $Y_t$ times an exponential integrating factor gives $Y_t = \mathbb E_t\big[\xi\exp\big(\int_t^T (R\,aY_s/(1 + aY_s^2) - \rho)\,ds\big)\big]$. For the density, the Malliavin derivative solves the linear BSDE $D_uY_t = D_u\xi + \int_t^T \big(2R\,aY_s/(1 + aY_s^2)^2 - \rho\big)D_uY_s\,ds - \int_t^T D_uZ_s\,dW_s$. For $R \ge 0$ the map $y \mapsto 2R\,ay/(1 + ay^2)^2 - \rho$ has maximum $\overline C$ and minimum $\underline C$, attained at $|y| = 1/\sqrt{3a}$ (for $R < 0$ the two are swapped, which is why the sign of $R$ is fixed). Linearizing again gives $\underline k\,e^{\underline C(T-t)} \le D_uY_t \le \overline k\,e^{\overline C(T-t)}$. This sandwiches the Nourdin–Viens function $g_{Y_t}$ between $\sigma_-^2$ and $\sigma_+^2$, and the Nourdin–Viens formula $\rho_F(x) = \frac{\mathbb E|F - \mathbb EF|}{2g_F(x - \mathbb EF)}\exp\big(-\int_0^{x - \mathbb EF} u\,du/g_F(u)\big)$ turns that into the two Gaussian bounds. This puts on rigorous footing the Gaussian fit used to compare the BSDE with Gillespie simulations.

## Sources

- Thibaut Mastrolia, "Density analysis of non-Markovian BSDEs and applications to biology and finance", Stochastic Processes and their Applications 128 (2018), 897–938, <https://doi.org/10.1016/j.spa.2017.06.009>; numbering as in arXiv:1602.06101: Theorem 2.4 (Nourdin–Viens formula), Section 6, Propositions 6.1 and 6.2.
