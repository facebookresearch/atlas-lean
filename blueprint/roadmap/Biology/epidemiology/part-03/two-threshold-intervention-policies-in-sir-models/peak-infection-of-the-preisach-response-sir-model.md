# Peak infection of the Preisach-response SIR model

**Setting.** Consider the normalized SIR system $\dot I=R_0SI-I$, $\dot S=-R_0SI-\rho S+\rho$ ($0<\rho<1$). Its basic reproduction number is given by the continuous Preisach operator of heterogeneous two-threshold responses, with a bounded positive density $q$ on $\Pi=\{0\le\alpha_1<\alpha_2\le1\}$ and $R_0^{nat}>R_0^{int}>1$. Along the first outbreak from a nearly fully susceptible population the input $I$ only increases, so the operator reduces to a function of the current value $I$. Define the associated planar ODE by $R_0(t)=\hat R^0(I(t))$ with

$$\hat R^0(I)=R_0^{nat}-(R_0^{nat}-R_0^{int})\int_0^I\!\!\int_0^{\alpha_2}q(\alpha)\,d\alpha_1\,d\alpha_2 .$$

Let $\Gamma_0=(I^0_\Gamma(t),S^0_\Gamma(t))$ be the heteroclinic orbit of this ODE. It leaves the infection-free saddle $(0,1)$ along its unstable manifold and converges to the endemic equilibrium $E_0$. Suppose $E_0$ is a focus, and let $I^0_M=\max_t I^0_\Gamma(t)$, which is attained at the first crossing of the nullcline $\dot I=0$.

**Proposition.** Every trajectory $\mathcal C$ of the SIR system with Preisach response satisfies

$$\sup_{t>0}I_{\mathcal C}(t)\ \longrightarrow\ I^0_M\qquad\text{as } I(0)\to0,\ S(0)\to1,\ I(0)+S(0)\le1,$$

uniformly over admissible initial states of the Preisach operator. If $E_0$ is a node instead, then $\Gamma_0$ never crosses the nullcline and the peak tends to $I^*_0$, the infected density at $E_0$. Moreover, $E_0$ is the endpoint of the segment of endemic equilibria of the hysteretic system with the largest infected density.

## Expansion

Starting near $(0,1)$, the trajectory follows the unstable manifold of the saddle, and $I$ increases monotonically up to its first maximum. While the input increases, each relay is on exactly when $\alpha_2\le I$. The Preisach output therefore equals $\hat R^0(I)$, and the hysteretic system coincides with the ODE along $\Gamma_0$ up to the peak. Continuous dependence on initial data, uniform because every relay is off near $I=0$, gives convergence of the peak. The formula turns the peak healthcare burden into a planar ODE computation. Numerically, the peak grows both with a later intervention start ($I_{int}$) and with greater heterogeneity of the response.

## Depends on

- [Segment of endemic equilibria of the SIR model with Preisach transmission response](segment-of-endemic-equilibria-of-the-sir-model-with-preisach-transmission-response.md)

## Sources

- Dmitrii Rachinskii, Samiha Rouf, "Dynamics of SIR model with heterogeneous response to intervention policy", arXiv:2103.07989 (2021), Section 3 (peak of the infected population), Proposition 4, <https://doi.org/10.48550/arXiv.2103.07989>.
