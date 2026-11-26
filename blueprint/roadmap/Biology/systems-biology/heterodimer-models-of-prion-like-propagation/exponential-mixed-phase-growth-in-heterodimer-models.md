# Exponential mixed-phase growth in heterodimer models

**Model.** Let $u(\tau)$ and $v(\tau)$ be the healthy and toxic forms of a prion-like protein. With production rate $c_1 > 0$, degradation rate $c_2 > 0$, small conversion parameter $\varepsilon \in (0,1)$ and an analytic conversion function $f$ (for example $f(v) = 1$ for single-particle templating, $f(v) = v$ for two-particle templating),

$$\frac{du}{d\tau} = c_1 - c_2 u - \varepsilon u v f(v), \qquad \frac{dv}{d\tau} = \varepsilon v\big(u f(v) - 1\big), \qquad u(0) = u_0,\ v(0) = v_0.$$

The healthy steady state is $(c_1/c_2, 0)$; a toxic steady state $(u_2^\star, v_2^\star) = \big(1/f(v_2^\star), (c_1 - c_2/f(v_2^\star))/\varepsilon\big)$ exists when this equation has a root with $f(v_2^\star) > 0$. Biologically relevant behavior (healthy state a saddle, toxic state a stable node) corresponds to $f(v) > g(v) := c_2/(c_1 - \varepsilon v)$ on $[0, v_2^\star)$, $f(v_2^\star) = g(v_2^\star)$ and $f'(v_2^\star) \le 0$.

**Phases.** Expand $u = u_{\mathrm{He}} + \varepsilon u_{\mathrm{Mi}} + O(\varepsilon^2)$ and $v = v_{\mathrm{He}} + \varepsilon v_{\mathrm{Mi}} + O(\varepsilon^2)$, with $u_0, v_0, f(v_0) = O(1)$. The healthy (He) phase has the outer solution

$$u_{\mathrm{He}}(\tau) = \frac{c_1}{c_2} - \Big(\frac{c_1}{c_2} - u_0\Big)e^{-c_2\tau}, \qquad v_{\mathrm{He}}(\tau) = v_0.$$

**Theorem 1 (mixed-phase inner solutions).** The mixed (Mi) phase corrections are

$$u_{\mathrm{Mi}}(\tau) = \Big(\frac{c_1}{c_2} + \frac{c_1 v_0 f(v_0)}{c_2^2}\Big)e^{-c_2\tau} + v_0 f(v_0)\Big(\frac{c_1}{c_2} - u_0\Big)\tau e^{-c_2\tau} - \frac{c_1 v_0 f(v_0)}{c_2^2},$$

$$v_{\mathrm{Mi}}(\tau) = v_0 - \frac{v_0 f(v_0)}{c_2}\Big(\frac{c_1}{c_2} - u_0\Big) + v_0\Big(f(v_0)\frac{c_1}{c_2} - 1\Big)\tau + \frac{v_0 f(v_0)}{c_2}\Big(\frac{c_1}{c_2} - u_0\Big)e^{-c_2\tau},$$

matching the He-phase limits $u_{\mathrm{Mi}}(0) = c_1/c_2$ and $v_{\mathrm{Mi}}(0) = v_0$.

**Theorem 2 (exponential growth of the toxic species).** Let $\lambda = f(v_0)u_0 - 1$. As $\tau \to 0$,

$$v_{\mathrm{Mi}}(\tau) = v_0 e^{\lambda\tau} + O(\tau^2),$$

so at early times of the mixed phase the toxic species grows (if $\lambda > 0$) or decays exponentially at rate $f(v_0)u_0 - 1$, the per-particle templating gain minus the unit loss rate.

## Expansion

Substituting the expansions and collecting $O(\varepsilon)$ terms gives linear ODEs for $u_{\mathrm{Mi}}$, $v_{\mathrm{Mi}}$ forced by the He-phase solution, $\dot u_{\mathrm{Mi}} = -c_2 u_{\mathrm{Mi}} - v_0 f(v_0)u_{\mathrm{He}}(\tau)$ and $\dot v_{\mathrm{Mi}} = v_0\big(f(v_0)u_{\mathrm{He}}(\tau) - 1\big)$, which integrate in closed form; analyticity of $f$ lets $f(v)$ be replaced by $f(v_0)$ at this order. Expanding $e^{-c_2\tau}$ to first order in $v_{\mathrm{Mi}}$ cancels the $c_1/c_2$ terms in the linear coefficient and leaves $v_0(1 + (f(v_0)u_0 - 1)\tau)$, which agrees with $v_0e^{\lambda\tau}$ to first order. The matched solution also explains the concave rise and maximum of the healthy species before it is depleted.

## Sources

- J. G. Borgqvist, "Analytical characterisation of the Mi- and To-phases in HeMiTo dynamics: exponential growth and logistic saturation of toxic prion-like proteins" (2026), Section 1 (heterodimer model class), Section 2 (steady states, stability conditions and He-phase outer solutions), Section 3 (Theorems 1 and 2), <https://doi.org/10.48550/arXiv.2604.00871>.
