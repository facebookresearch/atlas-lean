# Linearization of the stochastic FitzHugh–Nagumo neuron near rest

Let $f(v,w)=v-v^3/3-w+I$ and $g(v,w)=\varepsilon(v+\alpha-\beta w)$, and consider the Stratonovich system

$$dv_t=f(v_t,w_t)\,dt,\qquad dw_t=g(v_t,w_t)\,dt+h(w_t)\circ dB_t,$$

with additive channel noise $h(w)=\sigma_0$ or multiplicative noise $h(w)=\sigma_0 w$. Write $X=(v,w)$, $F=(f,g)$, $H=(0,h)$. In the **excitable regime** the deterministic field has a unique equilibrium $X_e=(v_e,w_e)$ whose Jacobian has eigenvalues $-\mu\pm i\nu$ with $\mu>0$, so $X_e$ is a stable focus and the global attractor; noise can still trigger large excursions (spikes).

**Theorem.** (i) The system has a unique solution generating a random dynamical system, which has a global random pullback attractor. (ii) Write $X_t-X_e$'s drift as $DF(X_e)(X_t-X_e)+\bar F(X_t-X_e)$ with $\bar F=\bigl(-\tfrac13(v+2v_e)(v-v_e)^2,\,0\bigr)$, so that $\|\bar F(X-X_e)\|\le\gamma(r)\|X-X_e\|$ for $\|X-X_e\|\le r$, where $\gamma(r)=r^2/3+|v_e|r\to 0$. Let $\bar X$ solve the linearized system

$$d\bar X_t=DF(X_e)\bar X_t\,dt+H(\bar X_t+X_e)\circ dB_t,\qquad \bar X_0=X_0-X_e,$$

and let $\tau=\inf\{t>0:\|X_t-X_e\|\ge r\}$ with $\|X_0-X_e\|<r$. There is a constant $C$ independent of $r$ such that, for all $t\ge 0$,

$$\sup_{t\le\tau}\|X_t-X_e-\bar X_t\|\le C\gamma(r)\,r\quad\text{(additive noise)},\qquad \mathbb E\|X_{t\wedge\tau}-X_e-\bar X_{t\wedge\tau}\|^2\le C\gamma(r)^2r^2\quad\text{(multiplicative noise)}.$$

**Leaky integrate-and-fire embedding.** With the linear change of coordinates $Y=Q^{-1}\bar X$ that puts $DF(X_e)$ in real Jordan form, the radial process $R_t=\|Y_t\|$ obeys, when $\mu\ll\nu$ and after averaging over the fast rotation, a one-dimensional SDE of leaky integrate-and-fire type with leak rate $\mu$. Declaring a spike when $R_t$ first reaches a threshold $r_0>0$ and resetting gives interspike intervals $\tau_0=\inf\{t>0:R_t\ge r_0\}$, an upper bound for the spiking time of the full model.

## Expansion

For (ii), the difference $X_t-X_e-\bar X_t$ is driven only by the nonlinear remainder $\bar F$, which before the exit time $\tau$ is bounded by $\gamma(r)r$ because the stable linear part damps the accumulated error; the estimate is pathwise for additive noise and in mean square for multiplicative noise (proofs in the paper's appendix). In the rotated coordinates the linearized process is a damped stochastic oscillator; the Baxendale–Greenwood averaging theorem approximates it by an Ornstein–Uhlenbeck process up to the rotation $e^{-i\nu t}$, whose amplitude plays the role of the membrane potential of a leaky integrate-and-fire neuron. The sub-threshold small oscillations of the FitzHugh–Nagumo neuron are thereby the integrate phase, and the large excursions correspond to the fire-and-reset step.

## Depends on

- [The FitzHugh–Nagumo vector field](../../fitzhugh-nagumo-model/field.md)

## Sources

- M. E. Yamakou, T. D. Tran, L. H. Duc, J. Jost, "The stochastic Fitzhugh–Nagumo neuron model in the excitable regime embeds a leaky integrate-and-fire model", Journal of Mathematical Biology 79(2) (2019) 509–532, <https://doi.org/10.1007/s00285-019-01366-z>, PMCID PMC6647150. Eqs. (2.1), (3.1) and (3.8)–(3.13), Theorems 3.1–3.2 and Section 4.
