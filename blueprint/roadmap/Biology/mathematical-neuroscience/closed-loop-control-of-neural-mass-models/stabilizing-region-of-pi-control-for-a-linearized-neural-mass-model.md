# Stabilizing region of proportional-integral control for a linearized neural mass model

**Neural mass model.** The Jansen–Rit-type model has a pyramidal population and excitatory and inhibitory feedback interneuron populations with connectivity constants $C_1, \dots, C_4$. Each population converts firing rate to mean membrane potential by a linear synaptic kernel

$$h_e(t) = \frac{H_e}{\tau_e}\, t\, e^{-t/\tau_e}, \qquad h_i(t) = \frac{H_i}{\tau_i}\, t\, e^{-t/\tau_i} \qquad (t \ge 0),$$

with transfer functions $H_e\tau_e/(1 + \tau_e s)^2$ and $H_i\tau_i/(1 + \tau_i s)^2$, and converts potential to rate by the sigmoid $S(v) = 2e_0/(1 + e^{r(v_0 - v)})$. Standard values are $H_e = 3.25$ mV, $H_i = 22$ mV, $\tau_e = 10.8$ ms, $\tau_i = 20$ ms, $C_1 = 135$, $C_2 = 0.8\,C_1$, $C_3 = C_4 = 0.25\,C_1$, $v_0 = 6$ mV, $e_0 = 2.5\ \mathrm{s}^{-1}$, $r = 0.56\ \mathrm{mV}^{-1}$. Epileptic activity is modelled as the high-amplitude limit cycle born when the fixed point loses stability in a Hopf bifurcation as $H_e$ increases or $H_i$ decreases. Linearizing at the fixed point gives a rational transfer function $G(s)$ from stimulation input to the output $y$ (the pyramidal potential, read as the local field potential).

**PI control.** With error $e(t) = r(t) - y(t)$, the stimulation is $u(t) = K_p e(t) + K_i \int_0^t e$, i.e. $C(s) = K_p + K_i/s$, and the closed loop has characteristic equation

$$\Delta(s) = s + (K_p s + K_i)\, G(s) = 0 \quad (\text{after clearing denominators: a degree-7 polynomial}).$$

**Theorem (stability boundary locus).** Real-coefficient roots cross the imaginary axis either at $s = 0$ or as a pair $\pm j\omega$, $\omega > 0$, so the boundary of the stabilizing region in the $(K_p, K_i)$ plane consists of

1. the line $K_i = 0$ (root at $s = 0$, whenever $G(0) \ne 0$ is finite); for the neural mass model the constant term of $\Delta$ is proportional to $K_i H_e \tau_e$, so by the sign condition of the Routh criterion stability requires $K_i > 0$;
2. the curve, with $G(j\omega) = R(\omega) + j I(\omega)$,

$$K_p(\omega) = -\frac{R(\omega)}{R(\omega)^2 + I(\omega)^2}, \qquad K_i(\omega) = -\frac{\omega\, I(\omega)}{R(\omega)^2 + I(\omega)^2}, \qquad \omega > 0 .$$

Following the curve in the direction of increasing $\omega$, the stabilizing side is the one on which the Jacobian of $(\mathrm{Re}\,\Delta(j\omega), \mathrm{Im}\,\Delta(j\omega))$ with respect to $(K_p, K_i)$ has negative determinant; for the neural mass model this is the right side. The exact stabilizing region is the set above $K_i = 0$ and to the right of the curve. It shrinks as $H_e$ increases (hyper-excitation) or $H_i$ decreases (weak inhibition). Inside it, the integral action drives the error to zero for any constant reference $r(t) = a$.

## Expansion

Substituting $s = j\omega$ into $j\omega + (K_i + j\omega K_p)(R + jI) = 0$ and separating real and imaginary parts gives $K_i R - \omega K_p I = 0$ and $K_i I + \omega K_p R = -\omega$, a linear system in $(K_p, K_i)$ whose solution is the stated curve; this is the D-partition (stability-boundary-locus) method, which turns the search for stabilizing gains into plotting one parametric curve. Zero steady-state error follows from the final value theorem: the error transfer function $1/(1 + C(s)G(s))$ vanishes at $s = 0$ because $C(s)$ has a pole there, so $\lim_{t\to\infty} e(t) = \lim_{s \to 0} s \cdot \frac{a}{s} \cdot \frac{1}{1 + C(s)G(s)} = 0$ when the closed loop is stable. In noisy simulations with hyper-excitation ($H_e = 7$ mV, $K_p = 310$, $K_i = 2$) or weak inhibition ($H_i = 17$ mV, $K_p = 90$, $K_i = 2$), gains chosen inside the region suppressed the high-amplitude oscillation, leaving a small residual error because the noisy input never lets the loop reach a true steady state.

## Sources

- J. Wang, E. Niebur, J. Hu, X. Li, "Suppressing epileptic activity in a neural mass model using a closed-loop proportional-integral controller", Scientific Reports 6 (2016), 27344, Methods ("Model", Table 1, "Graphical stability analysis method", Eq. (1)) and Results (Eqs. (2)–(13), Lemmas 1–2, Theorem 1, Figs. 3–5, steady-state analysis Eqs. (16)–(21), simulations Figs. 6–7), <https://doi.org/10.1038/srep27344> (PMC4895166).
