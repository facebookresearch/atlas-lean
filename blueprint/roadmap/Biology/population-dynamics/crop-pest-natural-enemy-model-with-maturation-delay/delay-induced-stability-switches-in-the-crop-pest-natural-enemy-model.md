# Delay-induced stability switches in the crop–pest–natural enemy model

Let $x(t)$ be the crop, $y(t)$ the pest, and $z_1(t), z_2(t)$ immature and mature natural enemies, with maturation time $\tau \ge 0$:

$$

\begin{aligned}
x' &= x\,(a_1 - b_1x - c_1y), \qquad y' = y\,(\alpha_1x - d_1 - c_2 z_2),\\
z_1' &= \alpha_2\,y z_2 - d_2 z_1 - \alpha_2 e^{-d_2\tau}\,y(t-\tau)\,z_2(t-\tau),\\
z_2' &= \alpha_2 e^{-d_2\tau}\,y(t-\tau)\,z_2(t-\tau) - d_3 z_2,
\end{aligned}

$$

with positive parameters and positive continuous initial data on $[-\tau,0]$ satisfying $z_1(0) = \int_{-\tau}^0 \alpha_2\,y(s)z_2(s)e^{d_2 s}\,ds$. Solutions are positive and bounded. Since $z_1$ does not feed back, the dynamics are governed by $(x,y,z_2)$, with equilibria

- $E_0 = (0,0,0)$ and $E_1 = (a_1/b_1, 0, 0)$;
- $E_2 = \big(\tfrac{d_1}{\alpha_1}, \tfrac{a_1\alpha_1 - b_1 d_1}{c_1\alpha_1}, 0\big)$, which exists iff $a_1\alpha_1 > b_1 d_1$;
- the interior equilibrium $E_3 = (x^*, y^*, z_2^*)$ with

$$

y^* = \frac{d_3 e^{d_2\tau}}{\alpha_2}, \qquad x^* = \frac{a_1\alpha_2 - c_1 d_3 e^{d_2\tau}}{b_1\alpha_2}, \qquad z_2^* = \frac{\alpha_1 x^* - d_1}{c_2},

$$

which exists iff $\alpha_1 x^* > d_1$, i.e. for $\tau$ below a threshold $\bar\tau$, because $y^*$ increases and $x^*$ decreases with $\tau$.

**Theorem (stability switches).** Assume $E_3$ exists. Its characteristic equation has the form $P(\lambda,\tau) + Q(\lambda,\tau)e^{-\lambda\tau} = 0$ with delay-dependent coefficients, and with $F(\omega,\tau) = |P(i\omega,\tau)|^2 - |Q(i\omega,\tau)|^2$ define, for each positive root $\omega(\tau)$ of $F(\cdot,\tau) = 0$ on an interval $I_2 \subseteq [0,\bar\tau)$, the Beretta–Kuang functions $S_n(\tau) = \tau - (\theta(\tau) + 2n\pi)/\omega(\tau)$, $n \in \mathbb{N}_0$, where $\theta(\tau) \in [0,2\pi)$ is the phase at which $i\omega(\tau)$ solves the characteristic equation.

1. If $S_0$ has no positive zero in $I_2$, then $E_3$ is locally asymptotically stable for all admissible $\tau$.
2. If some $S_n$ has positive zeros $\tau^* < \tau^{**}$ in $I_2$, a pair of simple purely imaginary roots crosses the imaginary axis at each, in the direction given by $\mathrm{sign}\,\partial_\omega F \cdot \mathrm{sign}\,S_n'$. Then $E_3$ is locally asymptotically stable for $\tau \in [0,\tau^*) \cup (\tau^{**},\bar\tau)$ and unstable for $\tau \in (\tau^*,\tau^{**})$, with Hopf bifurcations at $\tau^*$ and $\tau^{**}$: a stability–instability–stability switch.

The direction of the Hopf bifurcations and the stability of the bifurcating periodic orbits follow from normal-form and center-manifold computations.

## Expansion

Because the delay appears in the coefficients through $e^{d_2\tau}$ as well as in $e^{-\lambda\tau}$, the classical analysis with constant coefficients does not apply, and the geometric criterion of Beretta and Kuang is used: purely imaginary roots $i\omega$ occur exactly where $F(\omega,\tau) = 0$ and $S_n(\tau) = 0$, and the sign of $d\mathrm{Re}\lambda/d\tau$ at a crossing equals $\mathrm{sign}\,\partial_\omega F \cdot \mathrm{sign}\,dS_n/d\tau$. At $\tau = 0$ the equilibrium is stable, so the number of roots in the right half-plane changes only at zeros of the $S_n$; two zeros with opposite crossing directions give the switch.

## Sources

- Kunwer Singh Jatav, Joydip Dhar, "Theoretical Study of Pest Control Using Stage Structured Natural Enemies with Maturation Delay: A Crop-Pest-Natural Enemy Model", arXiv (2013). Section 2 (model), Section 3 (positivity and boundedness), Section 4 (equilibria and Theorem 4.3), Section 5 (direction of the Hopf bifurcation). <https://doi.org/10.48550/arXiv.1302.5773>
