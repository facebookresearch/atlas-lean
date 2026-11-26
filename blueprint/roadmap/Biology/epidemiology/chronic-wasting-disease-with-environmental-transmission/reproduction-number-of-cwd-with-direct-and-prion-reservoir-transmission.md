# Reproduction number of chronic wasting disease with direct and prion-reservoir transmission

**Model.** Susceptible $S$ and infected $I$ cervids ($N=S+I$) and an environmental prion load $U$ follow (deterministic part)
$$\begin{aligned}
\dot S &= \nu N\Big(1-\frac NK\Big) - \frac{\beta SI}{N} - \beta_e SU - \mu S\Big(1-\frac NK\Big) - \alpha_1 S,\\
\dot I &= \frac{\beta SI}{N} + \beta_e SU - \mu I\Big(1-\frac NK\Big) - \gamma I - \alpha_1 I,\\
\dot U &= \xi I - \epsilon U - \alpha_2 U,
\end{aligned}$$
with birth and density-dependent death parameters $\nu>\mu$, carrying capacity $K$, direct and environmental transmission rates $\beta, \beta_e$, disease mortality $\gamma$, hunting rate $\alpha_1<\nu-\mu$, prion shedding $\xi$, prion decay $\epsilon$ and decontamination rate $\alpha_2$. The disease-free equilibrium has $S_2^{*} = K\big(1-\frac{\alpha_1}{\nu-\mu}\big)$, $I=U=0$.

**Proposition.** With $a = \gamma + \frac{\nu\alpha_1}{\nu-\mu}$ and $d = \epsilon+\alpha_2$, the next-generation matrix at the disease-free equilibrium gives

$$R_0 = R_{\mathrm{dir}} + R_{\mathrm{env}} = \frac{\beta}{a} + \frac{\beta_e\,\xi\,S_2^{*}}{a\,d}.$$

The disease-free equilibrium is locally asymptotically stable for $R_0<1$ and unstable for $R_0>1$; at $R_0=1$ an endemic equilibrium branches off in a forward (supercritical) transcritical bifurcation, so no backward bifurcation occurs. For the stochastic version with multiplicative noise and a reflecting boundary at $S=0$, invasion of the disease-free state is instead governed by the sign of the top Lyapunov exponent of the linearised infection dynamics.

## Expansion

Ordering the infected compartments as $(I,U)$, new infections are $F=\begin{pmatrix}\beta & \beta_eS_2^{*}\\ 0&0\end{pmatrix}$ and transitions $V=\begin{pmatrix}a&0\\-\xi&d\end{pmatrix}$, since shedding moves infection into the reservoir without creating a new host infection; $FV^{-1}$ has rank one and its nonzero eigenvalue is $R_0$. An infected host transmits directly at rate $\beta$ for mean time $1/a$ and sheds $\xi/a$ prion units, each persisting for mean time $1/d$ and infecting susceptibles at rate $\beta_eS_2^{*}$. Hunting lowers both terms, decontamination only the environmental one.

## Sources

- W. Yin, W. J. Marrero, K. Jnawali, L. Asik, "Spread of chronic wasting disease under stochastic environmental conditions and its control using deep reinforcement learning", arXiv:2609.05566, Section 2, deterministic model: basic reproduction number and transcritical bifurcation; Theorem 2.5 for the stochastic model. <https://doi.org/10.48550/arXiv.2609.05566>
