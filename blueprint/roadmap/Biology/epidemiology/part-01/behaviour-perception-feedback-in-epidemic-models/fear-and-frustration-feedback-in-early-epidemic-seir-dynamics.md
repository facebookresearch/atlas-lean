# Fear and frustration feedback in early-epidemic SEIR dynamics

**Model.** Early in an outbreak ($S\approx N$), social distancing responds to perceived risk: fear of infection rises as a Hill function of new daily infections $\lambda E$ with threshold $M>0$ and steepness $q\ge1$, while frustration with distancing reduces compliance by at most a fraction $\omega^*\in[0,1]$. Assuming perception equilibrates fast, the reduced system is

$$
E'=\beta\Big(1-\frac{(\lambda E)^q}{M^q+(1+\omega^*)(\lambda E)^q}\Big)I-\lambda E,\qquad I'=\lambda E-\gamma I,
$$

with transmission rate $\beta$, incubation rate $\lambda$ and recovery rate $\gamma$; $\omega^*=0$ is the case without frustration. Besides the disease-free state $(0,0)$, there is the endemic state

$$
(\bar E,\bar I)=\Big(\frac M\lambda\,\Theta^{1/q},\ \frac M\gamma\,\Theta^{1/q}\Big),\qquad \Theta=\frac{\beta-\gamma}{\gamma-\omega^*(\beta-\gamma)},
$$

which is positive iff $0<\beta-\gamma<\gamma/\omega^*$.

**Theorem.**
1. If $\beta<\gamma$, only the disease-free state exists and it is asymptotically stable.
2. If $0<\beta-\gamma<\gamma/\omega^*$, the disease-free state is unstable and the endemic state is positive and asymptotically stable; nearby trajectories approach it without oscillation.
3. If $\beta-\gamma>\gamma/\omega^*$, only the disease-free state exists, it is unstable, and solutions grow without bound.

## Expansion

Without fear the linear growth rate is governed by $\beta-\gamma$. Fear saturates the effective transmission at $\beta\omega^*/(1+\omega^*)$ for large incidence, so the endemic plateau of new infections exists iff that saturated rate is below $\gamma$, i.e. $\beta-\gamma<\gamma/\omega^*$; otherwise frustration erodes distancing faster than fear can suppress transmission and the outbreak escapes. The planar Jacobian at the endemic state has negative trace and positive determinant with real eigenvalues for this direct-feedback system, which rules out oscillations; the source shows that adding delayed perception variables can instead produce damped oscillations or limit cycles, matching repeated waves.

## Proof depends on

- [Routh–Hurwitz: a real 2 × 2 matrix is Hurwitz iff tr M < 0 < det M](../../../../Analysis/ordinary-differential-equations/linear-systems-and-fundamental-matrices/is-hurwitz-iff-trace-neg-and-det-pos.md)
- [Lyapunov's indirect method (linearized stability), conditional decay form](../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/global-solution-decay-of-has-fderiv-at.md)
- [Lyapunov's indirect method, instability](../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/exists-unstable-of-has-fderiv-at.md)

## Sources

- Matthew D. Johnston, Bruce Pell, "A Dynamical Framework for Modeling Fear of Infection and Frustration with Social Distancing in COVID-19 Spread", arXiv:2008.06023: Section 2 (behaviour–perception SEIR model); Section 3.1 (reduced models); Appendix A: reduced direct system, endemic steady state and Theorem A.1, with Theorems A.2–A.3 for the delayed-perception variants. <https://doi.org/10.48550/arXiv.2008.06023>
