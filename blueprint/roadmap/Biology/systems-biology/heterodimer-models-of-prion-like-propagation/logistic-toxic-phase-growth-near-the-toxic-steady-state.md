# Logistic toxic-phase growth near the toxic steady state

Use the [heterodimer model](exponential-mixed-phase-growth-in-heterodimer-models.md) $\dot u = c_1 - c_2 u - \varepsilon u v f(v)$, $\dot v = \varepsilon v(u f(v) - 1)$ with analytic conversion function $f$, and assume the toxic steady state $(u_2^\star, v_2^\star)$ exists and is stable in the sense $f > g$ on $[0, v_2^\star)$, $f(v_2^\star) = g(v_2^\star)$, $f'(v_2^\star) \le 0$, where $g(v) = c_2/(c_1 - \varepsilon v)$.

**Lemma 1 (quasi steady state).** If the system starts at $u_0 = u_2^\star$, then for all $\tau \ge 0$ while $u = u_2^\star$,

$$\frac{du}{d\tau} = \varepsilon\Big(v_2^\star - \frac{v f(v)}{f(v_2^\star)}\Big),$$

so whenever $v_2^\star - v f(v)/f(v_2^\star) = O(1)$ the healthy species changes only on the slow scale, $du/d\tau = O(\varepsilon)$, and is quasi-stationary at early times.

**Theorem 3 (local logistic growth).** Under these assumptions, with $u_0 = u_2^\star$ and $v_0$ in a neighborhood of $v_2^\star$, let

$$\Psi(v) = \frac{c_1 f(v)}{c_2 + \varepsilon v f(v)} - 1, \qquad \gamma = \varepsilon\big(\Psi(v_0) - v_0\Psi'(v_0)\big), \qquad \kappa = v_0 - \frac{\Psi(v_0)}{\Psi'(v_0)},$$

with $\Psi'(v_0) \ne 0$. Then, as $\tau \to 0$,

$$v(\tau) = \frac{\kappa}{1 + \frac{\kappa - v_0}{v_0}e^{-\gamma\tau}} + O(\tau^3),$$

so the toxic species saturates locally like a logistic curve with growth rate $\gamma$ and carrying capacity $\kappa$.

## Expansion

Setting $\dot u = 0$ gives the slow manifold $u = c_1/(c_2 + \varepsilon v f(v))$, and substituting it into the $v$ equation yields the reduced scalar equation $\dot v = \varepsilon v\,\Psi(v)$; at the toxic steady state $\Psi(v_2^\star) = 0$. Linearizing $\Psi$ at $v_0$, $\Psi(v) \approx \Psi(v_0) + \Psi'(v_0)(v - v_0)$, turns the reduced equation into $\dot v = \gamma v(1 - v/\kappa)$ with $\gamma$ and $\kappa$ as stated (note $\kappa$ is the zero of the linearized $\Psi$, close to $v_2^\star$), whose solution is the logistic curve. Matching Taylor coefficients of the true solution and of the logistic curve through order $\tau^2$ gives the $O(\tau^3)$ error. Together with the exponential mixed-phase law this explains the sigmoidal time course of toxic protein load seen in neurodegenerative disease models.

## Depends on

- [Exponential mixed-phase growth in heterodimer models](exponential-mixed-phase-growth-in-heterodimer-models.md)
- [Explicit solution of the logistic equation](../../population-dynamics/logistic-growth-equation/logistic.md)

## Sources

- J. G. Borgqvist, "Analytical characterisation of the Mi- and To-phases in HeMiTo dynamics: exponential growth and logistic saturation of toxic prion-like proteins" (2026), Section 2 (toxic steady state and stability conditions), Section 3 (Lemma 1 and Theorem 3), <https://doi.org/10.48550/arXiv.2604.00871>.
