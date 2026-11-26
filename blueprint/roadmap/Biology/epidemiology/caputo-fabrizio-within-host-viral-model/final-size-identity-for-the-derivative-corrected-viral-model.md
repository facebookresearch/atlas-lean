# Final-size identity for the derivative-corrected within-host viral model

**Model.** Target cells $H$, infected cells $I$, virions $V$ and removed cells $D$ obey a target-cell-limited model with Caputo-Fabrizio derivatives of order $\mathfrak{a} \in (0,1)$, infection rate $b$, infected-cell death rate $d$, virion production $p$ and clearance $m$:

$${}^{CF}D^{\mathfrak a}H = -bVH + bV_0H_0e^{-\frac{\mathfrak a}{1-\mathfrak a}t}, \qquad {}^{CF}D^{\mathfrak a}I = bVH - dI - (bV_0H_0 - dI_0)e^{-\frac{\mathfrak a}{1-\mathfrak a}t},$$
$${}^{CF}D^{\mathfrak a}V = pI - mV - (pI_0 - mV_0)e^{-\frac{\mathfrak a}{1-\mathfrak a}t}, \qquad {}^{CF}D^{\mathfrak a}D = dI - dI_0e^{-\frac{\mathfrak a}{1-\mathfrak a}t}.$$

The exponential corrections make the right-hand sides vanish at $t = 0$, as the Caputo-Fabrizio derivative requires. Applying the Caputo-Fabrizio integral turns each equation into an implicit ODE mixing instantaneous and derivative terms, e.g. $\dot H = -b\bigl[(1-\mathfrak a)\tfrac{d}{dt}(VH) + \mathfrak a\,VH\bigr]$; the parameter $\mathfrak a$ blends the classical model ($\mathfrak a = 1$) with derivative corrections.

**Results.** Wherever a computable determinant $\Delta(H,V) \ne 0$ the system is an explicit locally Lipschitz ODE; $\Delta > 0$ for all $V \ge 0$ if $(1-\mathfrak a)^2bpH_0 < (1 + (1-\mathfrak a)d)(1 + (1-\mathfrak a)m)$. Under $\Delta > 0$ non-negative data stay non-negative, $H + I + D$ is conserved, and $I(t) \to 0$, $V(t) \to 0$. The final target-cell level $H_\infty$ satisfies

$$\log\frac{H_0\bigl(1 + (1-\mathfrak a)bV_0\bigr)}{H_\infty} = \mathfrak a\,b\int_0^\infty \frac{V(t)}{1 + (1-\mathfrak a)bV(t)}\,dt .$$

For $\mathfrak a = 1$ this is the classical identity $\log(H_0/H_\infty) = b\int_0^\infty V\,dt$.

## Expansion

The implicit target-cell equation can be written $\dot H\,(1 + (1-\mathfrak a)bV) + (1-\mathfrak a)bH\dot V = -\mathfrak a bVH$, i.e. $\frac{d}{dt}\log\bigl(H(1 + (1-\mathfrak a)bV)\bigr) = -\mathfrak a bV/(1 + (1-\mathfrak a)bV)$. Integrating from $0$ to $\infty$ and using $V(t) \to 0$ gives the final-size identity. Conservation of $H + I + D$ follows by adding the equations, since the infection and death fluxes cancel in the integrated form. The derivative correction thus acts like a saturating incidence $V/(1 + (1-\mathfrak a)bV)$ in the cumulative infection pressure.

## Sources

- D. Seleši, D. Rajter-Ćirić, N. Juhász, G. Röst, "A novel derivative-corrected within-host viral model based on Caputo-Fabrizio fractional dynamics" (2026), system (eq:odj), Proposition 1, Theorem 1, Proposition 2, Theorems 2-5, <https://doi.org/10.48550/arXiv.2611.12929>.
