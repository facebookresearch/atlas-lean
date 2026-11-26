# Endemic equilibria of the SIR model with a two-threshold intervention switch

**Model.** Rescale time in the SIR model with demography (recovery rate $\gamma$, departure rate $\mu$, total population normalized to $1$). On the invariant domain $\{I,S\ge0,\ I+S\le1\}$ this gives

$$\dot I=R_0SI-I,\qquad \dot S=-R_0SI-\rho S+\rho,\qquad \rho=\frac{\mu}{\gamma+\mu}<1 .$$

For constant $R_0>1$ the endemic equilibrium is $E=\bigl((1-1/R_0)\rho,\ 1/R_0\bigr)$. It is globally stable in the open positive quadrant, and it is a focus when $\rho R_0^2<4(R_0-1)$.

An intervention policy switches the basic reproduction number between $R_0^{nat}>R_0^{int}>1$ through a non-ideal relay (rectangular hysteresis loop) with thresholds $0<I_{nat}<I_{int}<1$. The intervention starts, and $R_0$ drops to $R_0^{int}$, when $I$ reaches $I_{int}$. It is revoked, and $R_0$ returns to $R_0^{nat}$, when $I$ falls to $I_{nat}$. Let

$$E_{nat}=\Bigl(\bigl(1-\tfrac1{R_0^{nat}}\bigr)\rho,\tfrac1{R_0^{nat}}\Bigr),\qquad E_{int}=\Bigl(\bigl(1-\tfrac1{R_0^{int}}\bigr)\rho,\tfrac1{R_0^{int}}\Bigr),$$

with infected components $I^*_{nat}>I^*_{int}$.

**Proposition.** Besides the infection-free saddle $(0,1)$, the switched system has:

- no endemic equilibrium if $I^*_{int}<I_{nat}<I_{int}<I^*_{nat}$;
- exactly one endemic equilibrium, $E_{nat}$, if $I^*_{int}<I_{nat}$ and $I^*_{nat}<I_{int}$;
- exactly one endemic equilibrium, $E_{int}$, if $I_{nat}<I^*_{int}$ and $I_{int}<I^*_{nat}$;
- two endemic equilibria, $E_{nat}$ and $E_{int}$ (bistability), if $I_{nat}<I^*_{int}<I^*_{nat}<I_{int}$.

Every endemic equilibrium that exists is stable. In the bistable case $E_{int}$ has more susceptible and fewer infected and recovered individuals than $E_{nat}$.

## Expansion

An equilibrium of the switched system must be an equilibrium of whichever flow is active, and it must be consistent with the relay state. $E_{nat}$ is admissible exactly when the relay can sit in the "no intervention" state at $I=I^*_{nat}$, that is, when $I^*_{nat}<I_{int}$. $E_{int}$ is admissible exactly when the relay can stay switched on at $I=I^*_{int}$, that is, when $I^*_{int}>I_{nat}$. Combining the two conditions gives the four cases. Stability is inherited from the global stability of each smooth flow, because near an admissible equilibrium no threshold is crossed. When neither equilibrium is admissible, trajectories that start near the infection-free state typically converge to a periodic orbit that runs clockwise around the hysteresis loop.

## Sources

- Dmitrii Rachinskii, Samiha Rouf, "Dynamics of SIR model with heterogeneous response to intervention policy", arXiv:2103.07989 (2021), Section 2 (normalized SIR model, switching rule) and Proposition 1, <https://doi.org/10.48550/arXiv.2103.07989>.
